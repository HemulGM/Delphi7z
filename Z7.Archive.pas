unit Z7.Archive;

// 7z container reader. All decoding is native Pascal; no DLLs or processes.
// See https://github.com/ip7z/7zip/blob/main/DOC/7zFormat.txt.
interface

uses
  System.SysUtils, System.Classes, Z7.Archive.Lzma;

type
  TSevenZipEntry = record
    Name: string;
    Size, Offset: Int64;
    IsDirectory: Boolean;
    CRC: Cardinal;
    HasCRC: Boolean;
  end;

  TSevenZipArchive = class
  private
    type
      TCoder = record
        Method: UInt64;
        Props: TBytes;
        Size: Int64;
      end;

      TDigest = record
        Defined: Boolean;
        Value: Cardinal;
      end;

      TFolder = record
        Coders: TArray<TCoder>;
        BindIn, BindOut: TArray<Integer>;
        PackedIndex: Integer;
        Size, Offset: Int64;
        Digest: TDigest;
        SubSizes: TArray<Int64>;
        SubCRCs: TArray<TDigest>;
      end;

      TStreams = record
        PackPos: Int64;
        PackSizes: TArray<Int64>;
        PackCRCs: TArray<TDigest>;
        Folders: TArray<TFolder>;
      end;
  private
    FInput: TFileStream;
    FSpool: TFileStream;
    FTempName: string;
    FEntries: TArray<TSevenZipEntry>;
    FStreams: TStreams;
    FCancel: TFunc<Boolean>;
    FPrepared: Boolean;
    procedure CheckCancel;
    procedure ReadHeader;
    procedure ReadStreams(Reader: TObject; out Streams: TStreams);
    procedure ReadFiles(Reader: TObject);
    procedure DecodeStreams(const Streams: TStreams; Output: TStream);
    procedure Prepare;
    function GetEntries: TArray<TSevenZipEntry>;
  public
    constructor Create(const FileName: string; Cancel: TFunc<Boolean> = nil);
    destructor Destroy; override;
    // Extracts to the caller's stream, so archive names never become disk paths.
    procedure Extract(Index: Integer; Destination: TStream);
    property Entries: TArray<TSevenZipEntry> read GetEntries;
  end;

// Files are concatenated in ordinal filename order, matching ZIP ROM hashing.
function OpenSevenZipInput(const FileName: string; out ContentSize: Int64; Cancel: TFunc<Boolean> = nil): TStream;

implementation

uses
  System.IOUtils, System.Generics.Collections, System.Generics.Defaults,
  Z7.Archive.Filters;

const
  MaxHeaderSize = 64 * 1024 * 1024;
  MaxItems = 1000000;

type
  THeaderReader = class
  private
    FData: TBytes;
    FPosition: Integer;
  public
    constructor Create(const Data: TBytes);
    function ByteValue: Byte;
    function Number: Int64;
    function Count: Integer;
    function UInt32: Cardinal;
    function Bytes(N: Int64): TBytes;
    function Bits(N: Integer): TArray<Boolean>;
    procedure Expect(Value: Byte);
    procedure Finish;
  end;

  TSevenZipJoined = class(TStream)
  private
    FArchive: TSevenZipArchive;
    FOrder: TArray<Integer>;
    FPosition, FSize, FEntryPosition: Int64;
    FIndex: Integer;
  public
    constructor Create(const FileName: string; Cancel: TFunc<Boolean>);
    destructor Destroy; override;
    function Read(var Buffer; Count: Longint): Longint; override;
    function Write(const Buffer; Count: Longint): Longint; override;
    function Seek(const Offset: Int64; Origin: TSeekOrigin): Int64; override;
  protected
    function GetSize: Int64; override;
  end;

procedure Invalid(const Message: string);
begin
  raise ESevenZip.Create('7z: ' + Message);
end;

function CheckedAdd(A, B: Int64): Int64;
begin
  if (A < 0) or (B < 0) or (B > High(Int64) - A) then
    Invalid('size overflow');
  Result := A + B;
end;

procedure CopyBytes(Source, Dest: TStream; Count: Int64; Cancel: TFunc<Boolean>);
var
  Buffer: array[0..65535] of Byte;
  N: Integer;
begin
  while Count > 0 do
  begin
    if Assigned(Cancel) and Cancel() then
      raise EAbort.Create('Cancelled');
    N := SizeOf(Buffer);
    if Count < N then
      N := Integer(Count);
    Source.ReadBuffer(Buffer, N);
    Dest.WriteBuffer(Buffer, N);
    Dec(Count, N);
  end;
end;

function CRCStream(Stream: TStream; Count: Int64; Cancel: TFunc<Boolean>): Cardinal;
var
  Table: array[0..255] of Cardinal;
  Buffer: array[0..65535] of Byte;
  I, J, N: Integer;
  V: Cardinal;
begin
  for I := 0 to 255 do
  begin
    V := I;
    for J := 0 to 7 do
      if V and 1 <> 0 then
        V := (V shr 1) xor $EDB88320
      else
        V := V shr 1;
    Table[I] := V;
  end;
  Result := $FFFFFFFF;
  while Count > 0 do
  begin
    if Assigned(Cancel) and Cancel() then
      raise EAbort.Create('Cancelled');
    N := SizeOf(Buffer);
    if Count < N then
      N := Integer(Count);
    Stream.ReadBuffer(Buffer, N);
    for I := 0 to N - 1 do
      Result := Table[(Result xor Buffer[I]) and $FF] xor (Result shr 8);
    Dec(Count, N);
  end;
  Result := not Result;
end;

function CRCBytes(const Data: TBytes; Offset, Count: Integer): Cardinal;
var
  S: TBytesStream;
begin
  S := TBytesStream.Create(Data);
  try
    S.Position := Offset;
    Result := CRCStream(S, Count, nil);
  finally
    S.Free;
  end;
end;

constructor THeaderReader.Create(const Data: TBytes);
begin
  inherited Create;
  FData := Data;
end;

function THeaderReader.ByteValue: Byte;
begin
  if FPosition = Length(FData) then
    Invalid('truncated header');
  Result := FData[FPosition];
  Inc(FPosition);
end;

function THeaderReader.Number: Int64;
var
  First, Mask: Byte;
  I: Integer;
  V: UInt64;
begin
  First := ByteValue;
  Mask := $80;
  V := 0;
  for I := 0 to 7 do
  begin
    if First and Mask = 0 then
    begin
      V := V or (UInt64(First and (Mask - 1)) shl (8 * I));
      if V > UInt64(High(Int64)) then
        Invalid('size exceeds Int64');
      Exit(Int64(V));
    end;
    V := V or (UInt64(ByteValue) shl (8 * I));
    Mask := Mask shr 1;
  end;
  if V > UInt64(High(Int64)) then
    Invalid('size exceeds Int64');
  Result := Int64(V);
end;

function THeaderReader.Count: Integer;
var
  N: Int64;
begin
  N := Number;
  if N > MaxItems then
    Invalid('header item limit exceeded');
  Result := Integer(N);
end;

function THeaderReader.UInt32: Cardinal;
var
  I: Integer;
begin
  Result := 0;
  for I := 0 to 3 do
    Result := Result or (Cardinal(ByteValue) shl (I * 8));
end;

function THeaderReader.Bytes(N: Int64): TBytes;
begin
  if (N < 0) or (N > Length(FData) - FPosition) then
    Invalid('truncated header property');
  Result := Copy(FData, FPosition, Integer(N));
  Inc(FPosition, Integer(N));
end;

function THeaderReader.Bits(N: Integer): TArray<Boolean>;
var
  I: Integer;
  B: Byte;
begin
  SetLength(Result, N);
  B := 0;
  for I := 0 to N - 1 do
  begin
    if I and 7 = 0 then
      B := ByteValue;
    Result[I] := B and ($80 shr (I and 7)) <> 0;
  end;
end;

procedure THeaderReader.Expect(Value: Byte);
begin
  if ByteValue <> Value then
    Invalid('unexpected header property');
end;

procedure THeaderReader.Finish;
begin
  if FPosition <> Length(FData) then
    Invalid('trailing header data');
end;

procedure ReadDigests(R: THeaderReader; N: Integer; out Digests: TArray<TSevenZipArchive.TDigest>);
var
  Defined: TArray<Boolean>;
  I: Integer;
  All: Byte;
begin
  SetLength(Digests, N);
  All := R.ByteValue;
  if All > 1 then
    Invalid('invalid CRC definition');
  if All = 0 then
    Defined := R.Bits(N);
  for I := 0 to N - 1 do
  begin
    Digests[I].Defined := (All = 1);
    if All = 0 then
      Digests[I].Defined := Defined[I];
    if Digests[I].Defined then
      Digests[I].Value := R.UInt32;
  end;
end;

procedure TSevenZipArchive.CheckCancel;
begin
  if Assigned(FCancel) and FCancel() then
    raise EAbort.Create('Cancelled');
end;

procedure TSevenZipArchive.ReadStreams(Reader: TObject; out Streams: TStreams);
var
  R: THeaderReader;
  ID, Flags: Byte;
  I, J, K, N, C, Total, DigestCount, D, FinalIndex: Integer;
  Sum, Offset: Int64;
  Digests: TArray<TDigest>;
  UsedIn, UsedOut: TArray<Boolean>;
  SeenSize, SeenCRC: Boolean;
begin
  Streams := Default(TStreams);
  R := THeaderReader(Reader);
  ID := R.ByteValue;
  if ID = 6 then
  begin
    Streams.PackPos := R.Number;
    N := R.Count;
    SetLength(Streams.PackSizes, N);
    SetLength(Streams.PackCRCs, N);
    SeenSize := False;
    SeenCRC := False;
    ID := R.ByteValue;
    while ID <> 0 do
    begin
      case ID of
        9:
          begin
            if SeenSize then
              Invalid('duplicate pack sizes');
            SeenSize := True;
            for I := 0 to N - 1 do
              Streams.PackSizes[I] := R.Number;
          end;
        10:
          begin
            if SeenCRC then
              Invalid('duplicate pack CRCs');
            SeenCRC := True;
            ReadDigests(R, N, Streams.PackCRCs);
          end;
      else
        Invalid('unsupported pack property');
      end;
      ID := R.ByteValue;
    end;
    if (N <> 0) and not SeenSize then
      Invalid('missing pack sizes');
    ID := R.ByteValue;
  end;
  if ID = 7 then
  begin
    R.Expect(11);
    N := R.Count;
    SetLength(Streams.Folders, N);
    R.Expect(0); // External coder descriptions are deliberately rejected.
    for I := 0 to N - 1 do
    begin
      CheckCancel;
      C := R.Count;
      if (C = 0) or (C > 32) then
        Invalid('invalid coder count');
      SetLength(Streams.Folders[I].Coders, C);
      for J := 0 to C - 1 do
      begin
        Flags := R.ByteValue;
        if (Flags and $C0 <> 0) or (Flags and $F = 0) or (Flags and $F > 8) then
          Invalid('invalid coder flags');
        for K := 1 to Flags and $F do
          Streams.Folders[I].Coders[J].Method := (Streams.Folders[I].Coders[J].Method shl 8) or R.ByteValue;
        if Flags and $10 <> 0 then
          if (R.Number <> 1) or (R.Number <> 1) then
            Invalid('unsupported multi-stream codec (BCJ2)');
        if Flags and $20 <> 0 then
          Streams.Folders[I].Coders[J].Props := R.Bytes(R.Number);
      end;
      SetLength(Streams.Folders[I].BindIn, C - 1);
      SetLength(Streams.Folders[I].BindOut, C - 1);
      SetLength(UsedIn, 0);
      SetLength(UsedIn, C);
      SetLength(UsedOut, 0);
      SetLength(UsedOut, C);
      for J := 0 to C - 2 do
      begin
        K := R.Count;
        if (K >= C) or UsedIn[K] then
          Invalid('invalid coder input binding');
        UsedIn[K] := True;
        Streams.Folders[I].BindIn[J] := K;
        K := R.Count;
        if (K >= C) or UsedOut[K] then
          Invalid('invalid coder output binding');
        UsedOut[K] := True;
        Streams.Folders[I].BindOut[J] := K;
      end;
      FinalIndex := -1;
      for J := 0 to C - 1 do
      begin
        if not UsedIn[J] then
          Streams.Folders[I].PackedIndex := J;
        if not UsedOut[J] then
          FinalIndex := J;
      end;
      // Validate a single acyclic chain before any decoding is attempted.
      K := Streams.Folders[I].PackedIndex;
      Total := 1;
      while K <> FinalIndex do
      begin
        D := -1;
        for J := 0 to C - 2 do
          if Streams.Folders[I].BindOut[J] = K then
            D := Streams.Folders[I].BindIn[J];
        if (D < 0) or (Total >= C) then
          Invalid('cyclic coder graph');
        K := D;
        Inc(Total);
      end;
      if Total <> C then
        Invalid('disconnected coder graph');
    end;
    R.Expect(12);
    Offset := 0;
    for I := 0 to N - 1 do
    begin
      FinalIndex := -1;
      for J := 0 to High(Streams.Folders[I].Coders) do
      begin
        Streams.Folders[I].Coders[J].Size := R.Number;
        K := 0;
        while (K < Length(Streams.Folders[I].BindOut)) and (Streams.Folders[I].BindOut[K] <> J) do
          Inc(K);
        if K = Length(Streams.Folders[I].BindOut) then
          FinalIndex := J;
      end;
      Streams.Folders[I].Size := Streams.Folders[I].Coders[FinalIndex].Size;
      Streams.Folders[I].Offset := Offset;
      Offset := CheckedAdd(Offset, Streams.Folders[I].Size);
    end;
    ID := R.ByteValue;
    if ID = 10 then
    begin
      ReadDigests(R, N, Digests);
      for I := 0 to N - 1 do
        Streams.Folders[I].Digest := Digests[I];
      ID := R.ByteValue;
    end;
    if ID <> 0 then
      Invalid('unexpected unpack property');
    for I := 0 to N - 1 do
    begin
      SetLength(Streams.Folders[I].SubSizes, 1);
      SetLength(Streams.Folders[I].SubCRCs, 1);
      Streams.Folders[I].SubSizes[0] := Streams.Folders[I].Size;
      Streams.Folders[I].SubCRCs[0] := Streams.Folders[I].Digest;
    end;
    ID := R.ByteValue;
  end;
  if Length(Streams.Folders) <> Length(Streams.PackSizes) then
    Invalid('pack/folder count mismatch');
  if ID = 8 then
  begin
    ID := R.ByteValue;
    Total := 0;
    if ID = 13 then
    begin
      for I := 0 to High(Streams.Folders) do
      begin
        N := R.Count;
        if N > MaxItems - Total then
          Invalid('too many substreams');
        Inc(Total, N);
        SetLength(Streams.Folders[I].SubSizes, N);
        SetLength(Streams.Folders[I].SubCRCs, 0);
        SetLength(Streams.Folders[I].SubCRCs, N);
      end;
      ID := R.ByteValue;
    end;
    SeenSize := ID = 9;
    for I := 0 to High(Streams.Folders) do
    begin
      N := Length(Streams.Folders[I].SubSizes);
      Sum := 0;
      for J := 0 to N - 2 do
      begin
        if not SeenSize then
          Invalid('missing substream sizes');
        Streams.Folders[I].SubSizes[J] := R.Number;
        Sum := CheckedAdd(Sum, Streams.Folders[I].SubSizes[J]);
      end;
      if Sum > Streams.Folders[I].Size then
        Invalid('substreams exceed folder size');
      if N > 0 then
        Streams.Folders[I].SubSizes[N - 1] := Streams.Folders[I].Size - Sum
      else if Streams.Folders[I].Size <> 0 then
        Invalid('folder has no substreams');
    end;
    if SeenSize then
      ID := R.ByteValue;
    DigestCount := 0;
    for I := 0 to High(Streams.Folders) do
      if not ((Length(Streams.Folders[I].SubSizes) = 1) and Streams.Folders[I].Digest.Defined) then
        Inc(DigestCount, Length(Streams.Folders[I].SubSizes));
    SetLength(Digests, 0);
    SetLength(Digests, DigestCount);
    if ID = 10 then
    begin
      ReadDigests(R, DigestCount, Digests);
      ID := R.ByteValue;
    end;
    D := 0;
    for I := 0 to High(Streams.Folders) do
      for J := 0 to High(Streams.Folders[I].SubSizes) do
        if (Length(Streams.Folders[I].SubSizes) = 1) and Streams.Folders[I].Digest.Defined then
          Streams.Folders[I].SubCRCs[J] := Streams.Folders[I].Digest
        else
        begin
          Streams.Folders[I].SubCRCs[J] := Digests[D];
          Inc(D);
        end;
    if ID <> 0 then
      Invalid('unexpected substream property');
    ID := R.ByteValue;
  end;
  if ID <> 0 then
    Invalid('unexpected streams property');
end;

procedure TSevenZipArchive.ReadFiles(Reader: TObject);
var
  R, P: THeaderReader;
  N, I, J, EmptyCount, E, F, Sub: Integer;
  ID: Byte;
  Empty, EmptyFile, Anti, Seen: TArray<Boolean>;
  Ch: Word;
  Name: TStringBuilder;
  Offset: Int64;
begin
  R := THeaderReader(Reader);
  N := R.Count;
  SetLength(FEntries, N);
  SetLength(Empty, N);
  SetLength(Seen, 256);
  EmptyCount := 0;
  repeat
    CheckCancel;
    ID := R.ByteValue;
    if ID = 0 then
      Break;
    if Seen[ID] then
      Invalid('duplicate file property');
    Seen[ID] := True;
    P := THeaderReader.Create(R.Bytes(R.Number));
    try
      case ID of
        14:
          begin
            Empty := P.Bits(N);
            for I := 0 to N - 1 do
              if Empty[I] then
                Inc(EmptyCount);
          end;
        15:
          EmptyFile := P.Bits(EmptyCount);
        16:
          begin
            Anti := P.Bits(EmptyCount);
            for I := 0 to High(Anti) do
              if Anti[I] then
                Invalid('anti-items are unsupported');
          end;
        17:
          begin
            P.Expect(0);
            Name := TStringBuilder.Create;
            try
              for I := 0 to N - 1 do
              begin
                Name.Clear;
                repeat
                  Ch := P.ByteValue;
                  Ch := Ch or (Word(P.ByteValue) shl 8);
                  if Ch = 0 then
                    Break;
                  Name.Append(Char(Ch));
                until False;
                FEntries[I].Name := Name.ToString;
              end;
            finally
              Name.Free;
            end;
          end;
      end;
      if ID in [14, 15, 16, 17] then
        P.Finish;
    finally
      P.Free;
    end;
  until False;
  if (N > 0) and not Seen[17] then
    Invalid('missing file names');
  E := 0;
  F := 0;
  Sub := 0;
  Offset := 0;
  for I := 0 to N - 1 do
    if Empty[I] then
    begin
      FEntries[I].IsDirectory := True;
      if E < Length(EmptyFile) then
        FEntries[I].IsDirectory := not EmptyFile[E];
      Inc(E);
    end
    else
    begin
      while (F < Length(FStreams.Folders)) and (Sub = Length(FStreams.Folders[F].SubSizes)) do
      begin
        Inc(F);
        Sub := 0;
        Offset := 0;
      end;
      if F = Length(FStreams.Folders) then
        Invalid('file has no data stream');
      FEntries[I].Size := FStreams.Folders[F].SubSizes[Sub];
      FEntries[I].Offset := CheckedAdd(FStreams.Folders[F].Offset, Offset);
      FEntries[I].HasCRC := FStreams.Folders[F].SubCRCs[Sub].Defined;
      FEntries[I].CRC := FStreams.Folders[F].SubCRCs[Sub].Value;
      Offset := CheckedAdd(Offset, FEntries[I].Size);
      Inc(Sub);
    end;
  J := Sub;
  for I := F to High(FStreams.Folders) do
  begin
    if J <> Length(FStreams.Folders[I].SubSizes) then
      Invalid('unassigned data streams');
    J := 0;
  end;
end;

procedure TSevenZipArchive.ReadHeader;
var
  Signature, Data, Decoded: TBytes;
  R, Start: THeaderReader;
  Offset, N: UInt64;
  Expected: Cardinal;
  I, ID: Integer;
  Encoded: TStreams;
  Mem: TMemoryStream;
begin
  SetLength(Signature, 32);
  FInput.ReadBuffer(Signature, 32);
  if (Signature[0] <> $37) or (Signature[1] <> $7A) or (Signature[2] <> $BC) or
    (Signature[3] <> $AF) or (Signature[4] <> $27) or (Signature[5] <> $1C) then
    Invalid('invalid signature');
  if Signature[6] <> 0 then
    Invalid('unsupported archive version');
  Start := THeaderReader.Create(Copy(Signature, 8, 24));
  try
    Expected := Start.UInt32;
    if CRCBytes(Signature, 12, 20) <> Expected then
      Invalid('start header CRC mismatch');
    // These fields are fixed-width little endian, not 7z variable integers.
    Offset := 0;
    N := 0;
    for I := 0 to 7 do
      Offset := Offset or (UInt64(Start.ByteValue) shl (I * 8));
    for I := 0 to 7 do
      N := N or (UInt64(Start.ByteValue) shl (I * 8));
    Expected := Start.UInt32;
  finally
    Start.Free;
  end;
  if (N > MaxHeaderSize) or (Offset > UInt64(FInput.Size - 32)) or
    (N > UInt64(FInput.Size - 32) - Offset) then
    Invalid('next header out of bounds');
  if N = 0 then
    Exit;
  FInput.Position := 32 + Int64(Offset);
  SetLength(Data, Integer(N));
  FInput.ReadBuffer(Data, Length(Data));
  if CRCBytes(Data, 0, Length(Data)) <> Expected then
    Invalid('next header CRC mismatch');
  R := THeaderReader.Create(Data);
  try
    ID := R.ByteValue;
    if ID = 23 then
    begin
      ReadStreams(R, Encoded);
      R.Finish;
      N := 0;
      for I := 0 to High(Encoded.Folders) do
      begin
        N := N + UInt64(Encoded.Folders[I].Size);
        if N > MaxHeaderSize then
          Invalid('decoded header exceeds 64 MiB limit');
      end;
      Mem := TMemoryStream.Create;
      try
        DecodeStreams(Encoded, Mem);
        SetLength(Decoded, Integer(Mem.Size));
        Mem.Position := 0;
        if Length(Decoded) > 0 then
          Mem.ReadBuffer(Decoded, Length(Decoded));
      finally
        Mem.Free;
      end;
      FreeAndNil(R);
      R := THeaderReader.Create(Decoded);
      ID := R.ByteValue;
    end;
    if ID <> 1 then
      Invalid('expected archive header');
    ID := R.ByteValue;
    if ID = 2 then
    begin
      repeat
        ID := R.ByteValue;
        if ID = 0 then
          Break;
        R.Bytes(R.Number);
      until False;
      ID := R.ByteValue;
    end;
    if ID = 3 then
      Invalid('external metadata streams are unsupported');
    if ID = 4 then
    begin
      ReadStreams(R, FStreams);
      ID := R.ByteValue;
    end;
    if ID = 5 then
    begin
      ReadFiles(R);
      ID := R.ByteValue;
    end
    else if Length(FStreams.Folders) <> 0 then
      Invalid('missing file table');
    if ID <> 0 then
      Invalid('unexpected archive header property');
    R.Finish;
  finally
    R.Free;
  end;
end;

procedure TSevenZipArchive.DecodeStreams(const Streams: TStreams; Output: TStream);
var
  I, J, K, Step, Next: Integer;
  PackOffset, StartPos, InputSize: Int64;
  Source, Dest: TStream;
  Temp, NewTemp: TFileStream;
  TempName, NewName: string;
  Coder: TCoder;
begin
  PackOffset := CheckedAdd(32, Streams.PackPos);
  for I := 0 to High(Streams.Folders) do
  begin
    CheckCancel;
    InputSize := Streams.PackSizes[I];
    if (PackOffset > FInput.Size) or (InputSize > FInput.Size - PackOffset) then
      Invalid('packed stream out of bounds');
    FInput.Position := PackOffset;
    if Streams.PackCRCs[I].Defined then
    begin
      if CRCStream(FInput, InputSize, FCancel) <> Streams.PackCRCs[I].Value then
        Invalid('packed data CRC mismatch');
      FInput.Position := PackOffset;
    end;
    StartPos := Output.Position;
    Source := FInput;
    K := Streams.Folders[I].PackedIndex;
    Temp := nil;
    TempName := '';
    try
      for Step := 0 to High(Streams.Folders[I].Coders) do
      begin
        Coder := Streams.Folders[I].Coders[K];
        NewTemp := nil;
        NewName := '';
        if Step < High(Streams.Folders[I].Coders) then
        begin
          NewName := TPath.GetTempFileName;
          try
            NewTemp := TFileStream.Create(NewName, fmOpenReadWrite or fmShareExclusive);
          except
            TFile.Delete(NewName);
            raise;
          end;
          Dest := NewTemp;
        end
        else
          Dest := Output;
        try
          case Coder.Method of
            0:
              begin
                if (Length(Coder.Props) <> 0) or (InputSize <> Coder.Size) then
                  Invalid('invalid Copy codec');
                CopyBytes(Source, Dest, InputSize, FCancel);
              end;
            $030101, $21:
              DecodeLzma(Source, Dest, InputSize, Coder.Size,
                Coder.Props, Coder.Method = $21, FCancel);
            3, $03030103:
              begin
                if InputSize <> Coder.Size then
                  Invalid('filter changes stream size');
                Decode7zFilter(Source, Dest, InputSize, Coder.Method, Coder.Props, FCancel);
              end;
            $06F10701:
              Invalid('password-protected archives are unsupported');
          else
            Invalid('unsupported codec $' + IntToHex(Coder.Method, 2));
          end;
        except
          NewTemp.Free;
          if NewName <> '' then
            TFile.Delete(NewName);
          raise;
        end;
        Temp.Free;
        Temp := nil;
        if TempName <> '' then
          TFile.Delete(TempName);
        Temp := NewTemp;
        TempName := NewName;
        if Temp <> nil then
        begin
          Source := Temp;
          Source.Position := 0;
        end;
        InputSize := Coder.Size;
        Next := -1;
        for J := 0 to High(Streams.Folders[I].BindOut) do
          if Streams.Folders[I].BindOut[J] = K then
            Next := Streams.Folders[I].BindIn[J];
        K := Next;
      end;
    finally
      Temp.Free;
      if TempName <> '' then
        TFile.Delete(TempName);
    end;
    if Output.Position - StartPos <> Streams.Folders[I].Size then
      Invalid('incorrect folder size');
    if Streams.Folders[I].Digest.Defined then
    begin
      Output.Position := StartPos;
      if CRCStream(Output, Streams.Folders[I].Size, FCancel) <> Streams.Folders[I].Digest.Value then
        Invalid('folder CRC mismatch');
    end;
    PackOffset := CheckedAdd(PackOffset, Streams.PackSizes[I]);
  end;
end;

constructor TSevenZipArchive.Create(const FileName: string; Cancel: TFunc<Boolean>);
begin
  inherited Create;
  FCancel := Cancel;
  CheckCancel;
  FInput := TFileStream.Create(FileName, fmOpenRead or fmShareDenyWrite);
  if FInput.Size < 32 then
    Invalid('truncated signature header');
  ReadHeader;
end;

destructor TSevenZipArchive.Destroy;
begin
  FSpool.Free;
  FInput.Free;
  if FTempName <> '' then
    TFile.Delete(FTempName);
  inherited;
end;

procedure TSevenZipArchive.Prepare;
var
  I: Integer;
begin
  if FPrepared then
    Exit;
  CheckCancel;
  if FSpool <> nil then
    Invalid('archive decoding previously failed');
  FTempName := TPath.GetTempFileName;
  FSpool := TFileStream.Create(FTempName, fmOpenReadWrite or fmShareExclusive);
  DecodeStreams(FStreams, FSpool);
  for I := 0 to High(FEntries) do
    if FEntries[I].HasCRC then
    begin
      FSpool.Position := FEntries[I].Offset;
      if CRCStream(FSpool, FEntries[I].Size, FCancel) <> FEntries[I].CRC then
        Invalid('file CRC mismatch: ' + FEntries[I].Name);
    end;
  FPrepared := True;
end;

function TSevenZipArchive.GetEntries: TArray<TSevenZipEntry>;
begin
  Result := Copy(FEntries);
end;

procedure TSevenZipArchive.Extract(Index: Integer; Destination: TStream);
begin
  if (Index < 0) or (Index >= Length(FEntries)) then
    raise EArgumentOutOfRangeException.Create('7z entry index');
  if Destination = nil then
    raise EArgumentNilException.Create('Destination');
  Prepare;
  FSpool.Position := FEntries[Index].Offset;
  CopyBytes(FSpool, Destination, FEntries[Index].Size, FCancel);
end;

constructor TSevenZipJoined.Create(const FileName: string; Cancel: TFunc<Boolean>);
var
  Order: TList<Integer>;
  I: Integer;
begin
  inherited Create;
  FArchive := TSevenZipArchive.Create(FileName, Cancel);
  Order := TList<Integer>.Create;
  try
    for I := 0 to High(FArchive.FEntries) do
      if not FArchive.FEntries[I].IsDirectory then
      begin
        Order.Add(I);
        FSize := CheckedAdd(FSize, FArchive.FEntries[I].Size);
      end;
    Order.Sort(TComparer<Integer>.Construct(
      function(const A, B: Integer): Integer
      begin
        Result := CompareStr(FArchive.FEntries[A].Name, FArchive.FEntries[B].Name);
        if Result = 0 then
          Result := A - B;
      end));
    FOrder := Order.ToArray;
  finally
    Order.Free;
  end;
end;

destructor TSevenZipJoined.Destroy;
begin
  FArchive.Free;
  inherited;
end;

function TSevenZipJoined.GetSize: Int64;
begin
  Result := FSize;
end;

function TSevenZipJoined.Read(var Buffer; Count: Longint): Longint;
var
  E: TSevenZipEntry;
  N: Integer;
begin
  Result := 0;
  if Count <= 0 then
    Exit;
  FArchive.Prepare;
  while FIndex < Length(FOrder) do
  begin
    FArchive.CheckCancel;
    E := FArchive.FEntries[FOrder[FIndex]];
    if FEntryPosition = E.Size then
    begin
      Inc(FIndex);
      FEntryPosition := 0;
      Continue;
    end;
    N := Count;
    if E.Size - FEntryPosition < N then
      N := Integer(E.Size - FEntryPosition);
    FArchive.FSpool.Position := E.Offset + FEntryPosition;
    FArchive.FSpool.ReadBuffer(Buffer, N);
    Inc(FEntryPosition, N);
    Inc(FPosition, N);
    Exit(N);
  end;
end;

function TSevenZipJoined.Write(const Buffer; Count: Longint): Longint;
begin
  raise EStreamError.Create('Read-only 7z stream');
end;

function TSevenZipJoined.Seek(const Offset: Int64; Origin: TSeekOrigin): Int64;
begin
  if (Origin = soBeginning) and (Offset = 0) then
  begin
    FIndex := 0;
    FEntryPosition := 0;
    FPosition := 0;
  end
  else if (Origin = soEnd) and (Offset = 0) then
  begin
    FIndex := Length(FOrder);
    FEntryPosition := 0;
    FPosition := FSize;
  end
  else if not ((Origin = soCurrent) and (Offset = 0)) then
    raise EStreamError.Create('Sequential 7z stream');
  Result := FPosition;
end;

function OpenSevenZipInput(const FileName: string; out ContentSize: Int64; Cancel: TFunc<Boolean>): TStream;
begin
  Result := TSevenZipJoined.Create(FileName, Cancel);
  ContentSize := Result.Size;
end;

end.

