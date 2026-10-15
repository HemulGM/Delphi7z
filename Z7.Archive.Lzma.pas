unit Z7.Archive.Lzma;

// Native Delphi range/LZMA decoder. Format reference: the public-domain LZMA
// SDK by Igor Pavlov (https://7-zip.org/sdk.html). No external runtime is used.
interface

uses
  System.SysUtils, System.Classes;

type
  ESevenZip = class(EStreamError);

procedure DecodeLzma(Input, Output: TStream; PackedSize, UnpackedSize: Int64; const Properties: TBytes; Lzma2: Boolean; Cancel: TFunc<Boolean>);

implementation

{$Q+}{$R+}

type
  TLzmaDecoder = class
  private
    FInput, FOutput: TStream;
    FCancel: TFunc<Boolean>;
    FRemaining: Int64;
    FInBuffer: array[0..65535] of Byte;
    FInPos, FInSize: Integer;
    FOutBuffer: array[0..65535] of Byte;
    FOutSize: Integer;
    FDictionary: TBytes;
    FDictPos: Integer;
    FHistory, FProcessed, FWritten: Int64;
    FRange, FCode: Cardinal;
    FChunkLeft: Int64;
    FProbs: TArray<Word>;
    FLc, FLp, FPb, FState: Integer;
    FRep: array[0..3] of Cardinal;
    function GetByte: Byte;
    function RangeByte: Byte;
    procedure Normalize;
    function Bit(Index: Integer): Cardinal;
    function Tree(Index, Bits: Integer): Cardinal;
    function ReverseTree(Index, Bits: Integer): Cardinal;
    function DirectBits(Bits: Integer): Cardinal;
    function DecodeLength(Index, PosState: Integer): Integer;
    procedure SetProperties(Value: Byte; IsLzma2: Boolean);
    procedure ResetState;
    procedure ResetDictionary;
    procedure Flush;
    procedure PutByte(Value: Byte);
    function Previous(Distance: Cardinal): Byte;
    procedure Chunk(ChunkPacked, ChunkUnpacked: Int64);
    procedure FinishLzma1;
  public
    procedure Decode(Input, Output: TStream; PackedSize, UnpackedSize: Int64; const Props: TBytes; IsLzma2: Boolean; Cancel: TFunc<Boolean>);
  end;

const
  IsMatch = 0;
  IsRep = IsMatch + 12 * 16;
  IsRepG0 = IsRep + 12;
  IsRepG1 = IsRepG0 + 12;
  IsRepG2 = IsRepG1 + 12;
  IsRep0Long = IsRepG2 + 12;
  PosSlot = IsRep0Long + 12 * 16;
  SpecPos = PosSlot + 4 * 64;
  AlignPos = SpecPos + 114;
  LenCoder = AlignPos + 16;
  LenSize = 2 + 16 * 8 * 2 + 256;
  RepLenCoder = LenCoder + LenSize;
  Literal = RepLenCoder + LenSize;

procedure Fail(const Message: string);
begin
  raise ESevenZip.Create('7z: ' + Message);
end;

function TLzmaDecoder.GetByte: Byte;
var
  N: Integer;
begin
  if FInPos = FInSize then
  begin
    if Assigned(FCancel) and FCancel() then
      raise EAbort.Create('Cancelled');
    if FRemaining = 0 then
      Fail('truncated compressed data');
    N := SizeOf(FInBuffer);
    if FRemaining < N then
      N := Integer(FRemaining);
    FInSize := FInput.Read(FInBuffer, N);
    if FInSize = 0 then
      Fail('truncated compressed data');
    Dec(FRemaining, FInSize);
    FInPos := 0;
  end;
  Result := FInBuffer[FInPos];
  Inc(FInPos);
end;

function TLzmaDecoder.RangeByte: Byte;
begin
  if FChunkLeft = 0 then
    Fail('truncated LZMA chunk');
  Dec(FChunkLeft);
  Result := GetByte;
end;

procedure TLzmaDecoder.Normalize;
begin
  if FRange < $1000000 then
  begin
    FRange := FRange shl 8;
    FCode := (FCode shl 8) or RangeByte;
  end;
end;

function TLzmaDecoder.Bit(Index: Integer): Cardinal;
var
  Bound: Cardinal;
  P: Word;
begin
  Normalize;
  P := FProbs[Index];
  Bound := (FRange shr 11) * P;
  if FCode < Bound then
  begin
    FRange := Bound;
    FProbs[Index] := P + ((2048 - P) shr 5);
    Result := 0;
  end
  else
  begin
    Dec(FRange, Bound);
    Dec(FCode, Bound);
    FProbs[Index] := P - (P shr 5);
    Result := 1;
  end;
end;

function TLzmaDecoder.Tree(Index, Bits: Integer): Cardinal;
var
  I: Integer;
begin
  Result := 1;
  for I := 1 to Bits do
    Result := (Result shl 1) or Bit(Index + Integer(Result));
  Dec(Result, Cardinal(1) shl Bits);
end;

function TLzmaDecoder.ReverseTree(Index, Bits: Integer): Cardinal;
var
  I, Node: Integer;
  B: Cardinal;
begin
  Result := 0;
  Node := 1;
  for I := 0 to Bits - 1 do
  begin
    B := Bit(Index + Node);
    Node := (Node shl 1) or Integer(B);
    Result := Result or (B shl I);
  end;
end;

function TLzmaDecoder.DirectBits(Bits: Integer): Cardinal;
var
  I: Integer;
begin
  Result := 0;
  for I := 1 to Bits do
  begin
    Normalize;
    FRange := FRange shr 1;
    Result := Result shl 1;
    if FCode >= FRange then
    begin
      Dec(FCode, FRange);
      Result := Result or 1;
    end;
  end;
end;

function TLzmaDecoder.DecodeLength(Index, PosState: Integer): Integer;
begin
  if Bit(Index) = 0 then
    Exit(Integer(Tree(Index + 2 + PosState * 8, 3)) + 2);
  if Bit(Index + 1) = 0 then
    Exit(Integer(Tree(Index + 2 + 128 + PosState * 8, 3)) + 10);
  Result := Integer(Tree(Index + 2 + 256, 8)) + 18;
end;

procedure TLzmaDecoder.SetProperties(Value: Byte; IsLzma2: Boolean);
begin
  if Value >= 225 then
    Fail('invalid LZMA properties');
  FLc := Value mod 9;
  FLp := (Value div 9) mod 5;
  FPb := Value div 45;
  if IsLzma2 and (FLc + FLp > 4) then
    Fail('invalid LZMA2 literal properties');
  SetLength(FProbs, Literal + (768 shl (FLc + FLp)));
end;

procedure TLzmaDecoder.ResetState;
var
  I: Integer;
begin
  for I := 0 to High(FProbs) do
    FProbs[I] := 1024;
  FState := 0;
  FillChar(FRep, SizeOf(FRep), 0);
end;

procedure TLzmaDecoder.ResetDictionary;
begin
  FHistory := 0;
  FProcessed := 0;
  FDictPos := 0;
end;

procedure TLzmaDecoder.Flush;
begin
  if Assigned(FCancel) and FCancel() then
    raise EAbort.Create('Cancelled');
  if FOutSize <> 0 then
    FOutput.WriteBuffer(FOutBuffer, FOutSize);
  FOutSize := 0;
end;

procedure TLzmaDecoder.PutByte(Value: Byte);
begin
  FDictionary[FDictPos] := Value;
  Inc(FDictPos);
  if FDictPos = Length(FDictionary) then
    FDictPos := 0;
  if FHistory < Length(FDictionary) then
    Inc(FHistory);
  Inc(FProcessed);
  Inc(FWritten);
  FOutBuffer[FOutSize] := Value;
  Inc(FOutSize);
  if FOutSize = SizeOf(FOutBuffer) then
    Flush;
end;

function TLzmaDecoder.Previous(Distance: Cardinal): Byte;
var
  P: Int64;
begin
  if UInt64(Distance) >= UInt64(FHistory) then
    Fail('invalid LZMA match distance');
  P := Int64(FDictPos) - Int64(Distance) - 1;
  if P < 0 then
    Inc(P, Length(FDictionary));
  Result := FDictionary[Integer(P)];
end;

procedure TLzmaDecoder.Chunk(ChunkPacked, ChunkUnpacked: Int64);
var
  I, PosState, Context, Symbol, MatchBit, MatchByte, L, Slot, NumBits: Integer;
  Distance, T: Cardinal;
  Target: Int64;
  Prev: Byte;
begin
  FChunkLeft := ChunkPacked;
  if RangeByte <> 0 then
    Fail('invalid range coder prefix');
  FCode := 0;
  FRange := $FFFFFFFF;
  for I := 1 to 4 do
    FCode := (FCode shl 8) or RangeByte;
  if FCode = FRange then
    Fail('invalid range coder');
  Target := FWritten + ChunkUnpacked;
  while FWritten < Target do
  begin
    PosState := Integer(FProcessed and ((1 shl FPb) - 1));
    if Bit(IsMatch + FState * 16 + PosState) = 0 then
    begin
      Prev := 0;
      if FHistory <> 0 then
        Prev := Previous(0);
      Context := Literal + 768 * ((Integer(FProcessed and ((1 shl FLp) - 1)) shl FLc) + (Prev shr (8 - FLc)));
      Symbol := 1;
      if FState >= 7 then
      begin
        MatchByte := Previous(FRep[0]);
        repeat
          MatchBit := (MatchByte shr 7) and 1;
          MatchByte := (MatchByte shl 1) and $FF;
          I := Integer(Bit(Context + ((1 + MatchBit) shl 8) + Symbol));
          Symbol := (Symbol shl 1) or I;
          if I <> MatchBit then
            Break;
        until Symbol >= 256;
      end;
      while Symbol < 256 do
        Symbol := (Symbol shl 1) or Integer(Bit(Context + Symbol));
      PutByte(Byte(Symbol and $FF));
      if FState < 4 then
        FState := 0
      else if FState < 10 then
        Dec(FState, 3)
      else
        Dec(FState, 6);
      Continue;
    end;
    if Bit(IsRep + FState) <> 0 then
    begin
      if Bit(IsRepG0 + FState) = 0 then
      begin
        if Bit(IsRep0Long + FState * 16 + PosState) = 0 then
        begin
          if FState < 7 then
            FState := 9
          else
            FState := 11;
          PutByte(Previous(FRep[0]));
          Continue;
        end;
      end
      else
      begin
        if Bit(IsRepG1 + FState) = 0 then
          Distance := FRep[1]
        else
        begin
          if Bit(IsRepG2 + FState) = 0 then
            Distance := FRep[2]
          else
          begin
            Distance := FRep[3];
            FRep[3] := FRep[2];
          end;
          FRep[2] := FRep[1];
        end;
        FRep[1] := FRep[0];
        FRep[0] := Distance;
      end;
      L := DecodeLength(RepLenCoder, PosState);
      if FState < 7 then
        FState := 8
      else
        FState := 11;
    end
    else
    begin
      L := DecodeLength(LenCoder, PosState);
      if FState < 7 then
        FState := 7
      else
        FState := 10;
      I := L - 2;
      if I > 3 then
        I := 3;
      Slot := Integer(Tree(PosSlot + I * 64, 6));
      if Slot < 4 then
        Distance := Slot
      else
      begin
        NumBits := (Slot shr 1) - 1;
        Distance := Cardinal(2 or (Slot and 1)) shl NumBits;
        if Slot < 14 then
          Inc(Distance, ReverseTree(SpecPos + Integer(Distance) - Slot - 1, NumBits))
        else
        begin
          T := DirectBits(NumBits - 4);
          Distance := Distance + (T shl 4) + ReverseTree(AlignPos, 4);
        end;
      end;
      if Distance = $FFFFFFFF then
        Fail('premature LZMA end marker');
      FRep[3] := FRep[2];
      FRep[2] := FRep[1];
      FRep[1] := FRep[0];
      FRep[0] := Distance;
    end;
    if L > Target - FWritten then
      Fail('LZMA match exceeds output size');
    for I := 1 to L do
      PutByte(Previous(FRep[0]));
  end;
  Normalize;
  // Known-size LZMA1 streams may carry an optional end marker. LZMA2
  // chunks have no marker and must consume exactly their bounded payload.
end;

procedure TLzmaDecoder.FinishLzma1;
var
  PosState: Integer;
  Distance: Cardinal;
begin
  if FCode <> 0 then
  begin
    // A known-size stream can omit its end marker. If there is one, decode
    // and validate it instead of silently discarding the remaining bytes.
    PosState := Integer(FProcessed and ((1 shl FPb) - 1));
    if Bit(IsMatch + FState * 16 + PosState) <> 1 then
      Fail('missing LZMA end marker');
    if Bit(IsRep + FState) <> 0 then
      Fail('invalid LZMA end marker');
    if DecodeLength(LenCoder, PosState) <> 2 then
      Fail('invalid LZMA end length');
    if Tree(PosSlot, 6) <> 63 then
      Fail('invalid LZMA end distance');
    Distance := DirectBits(26) shl 4;
    Distance := Distance or ReverseTree(AlignPos, 4);
    if Distance <> $3FFFFFFF then
      Fail('invalid LZMA end distance');
    Normalize;
  end;
  if (FCode <> 0) or (FChunkLeft <> 0) then
    Fail('invalid LZMA stream ending');
end;

procedure TLzmaDecoder.Decode(Input, Output: TStream; PackedSize, UnpackedSize: Int64; const Props: TBytes; IsLzma2: Boolean; Cancel: TFunc<Boolean>);
var
  DictionarySize: UInt64;
  C, NeedInit: Byte;
  U, P, I: Integer;
begin
  FInput := Input;
  FOutput := Output;
  FCancel := Cancel;
  FRemaining := PackedSize;
  if (PackedSize < 0) or (UnpackedSize < 0) then
    Fail('negative stream size');
  if IsLzma2 then
  begin
    if (Length(Props) <> 1) or (Props[0] > 40) then
      Fail('invalid LZMA2 dictionary properties');
    if Props[0] = 40 then
      DictionarySize := $FFFFFFFF
    else
      DictionarySize := UInt64(2 or (Props[0] and 1)) shl (Props[0] div 2 + 11);
  end
  else
  begin
    if Length(Props) <> 5 then
      Fail('invalid LZMA properties size');
    DictionarySize := Cardinal(Props[1]) or (Cardinal(Props[2]) shl 8) or
      (Cardinal(Props[3]) shl 16) or (Cardinal(Props[4]) shl 24);
    if DictionarySize < 4096 then
      DictionarySize := 4096;
  end;
  // A dictionary larger than the entire output cannot be referenced.
  if DictionarySize > UInt64(UnpackedSize) then
    DictionarySize := UnpackedSize;
  if DictionarySize = 0 then
    DictionarySize := 1;
  if DictionarySize > 256 * 1024 * 1024 then
    Fail('dictionary exceeds 256 MiB resource limit');
  SetLength(FDictionary, Integer(DictionarySize));
  ResetDictionary;
  if not IsLzma2 then
  begin
    SetProperties(Props[0], False);
    ResetState;
    Chunk(PackedSize, UnpackedSize);
    FinishLzma1;
  end
  else
  begin
    NeedInit := $E0;
    repeat
      C := GetByte;
      if C = 0 then
        Break;
      if (C > 2) and (C < $80) then
        Fail('invalid LZMA2 control');
      if (C < $80) and (C <> 1) and (NeedInit = $E0) then
        Fail('missing LZMA2 dictionary reset');
      U := Integer(GetByte) shl 8;
      U := U + GetByte + 1;
      if C < $80 then
      begin
        if C = 1 then
        begin
          ResetDictionary;
          NeedInit := $C0;
        end
        else if NeedInit < $A0 then
          NeedInit := $A0;
        if U > UnpackedSize - FWritten then
          Fail('LZMA2 copy exceeds output size');
        for I := 1 to U do
          PutByte(GetByte);
      end
      else
      begin
        if C < NeedInit then
          Fail('missing LZMA2 state reset');
        U := U + (Integer(C and $1F) shl 16);
        P := Integer(GetByte) shl 8;
        P := P + GetByte + 1;
        if C >= $C0 then
          SetProperties(GetByte, True);
        if C >= $E0 then
          ResetDictionary;
        if C >= $A0 then
          ResetState;
        NeedInit := 0;
        if U > UnpackedSize - FWritten then
          Fail('LZMA2 chunk exceeds output size');
        Chunk(P, U);
        if (FChunkLeft <> 0) or (FCode <> 0) then
          Fail('invalid LZMA2 chunk ending');
      end;
    until False;
    if FWritten <> UnpackedSize then
      Fail('incorrect LZMA2 output size');
    if (FRemaining <> 0) or (FInPos <> FInSize) then
      Fail('trailing LZMA2 data');
  end;
  Flush;
end;

procedure DecodeLzma(Input, Output: TStream; PackedSize, UnpackedSize: Int64; const Properties: TBytes; Lzma2: Boolean; Cancel: TFunc<Boolean>);
var
  D: TLzmaDecoder;
begin
  D := TLzmaDecoder.Create;
  try
    D.Decode(Input, Output, PackedSize, UnpackedSize, Properties, Lzma2, Cancel);
  finally
    D.Free;
  end;
end;

end.

