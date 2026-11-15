unit Z7.Archive.Filters;

// Delta and x86 BCJ decoding, based on the public-domain LZMA SDK formats.
interface

uses System.SysUtils, System.Classes;

procedure Decode7zFilter(Source, Destination: TStream; Size: Int64;
  Method: UInt64; const Properties: TBytes; Cancel: TFunc<Boolean>);

implementation

uses Z7.Archive.Lzma;

{$Q+}{$R+}

function IsSignByte(B: Byte): Boolean;
begin
  Result := (B = 0) or (B = $FF);
end;

function Read32(const Data: TBytes; P: Integer): Cardinal;
begin
  Result := Cardinal(Data[P]) or (Cardinal(Data[P+1]) shl 8) or
    (Cardinal(Data[P+2]) shl 16) or (Cardinal(Data[P+3]) shl 24);
end;

function BCJ(var Data: TBytes; Size: Integer; IP: Cardinal; var State: Cardinal): Integer;
const
  Allowed: array[0..7] of Boolean = (True, True, True, False, True, False, False, False);
  BitNumber: array[0..7] of Integer = (0, 1, 2, 2, 3, 3, 3, 3);
var
  Pos, PrevPos, Distance, Index: Integer;
  Mask, Src, Dest: Cardinal;
begin
  Pos := 0; PrevPos := -1; Mask := State and 7;
  while Pos <= Size - 5 do
  begin
    if Data[Pos] and $FE <> $E8 then begin Inc(Pos); Continue; end;
    Distance := Pos - PrevPos;
    if Distance > 3 then Mask := 0
    else
    begin
      Mask := (Mask shl (Distance - 1)) and 7;
      if (Mask <> 0) and ((not Allowed[Mask]) or IsSignByte(Data[Pos + 4 - BitNumber[Mask]])) then
      begin
        PrevPos := Pos;
        Mask := ((Mask shl 1) or 1) and 7;
        Inc(Pos);
        Continue;
      end;
    end;
    PrevPos := Pos;
    if IsSignByte(Data[Pos + 4]) then
    begin
      Src := Read32(Data, Pos + 1);
      repeat
        Dest := Cardinal((Int64(Src) - IP - Pos - 5) and $FFFFFFFF);
        if Mask = 0 then Break;
        Index := BitNumber[Mask] * 8;
        if not IsSignByte(Byte((Dest shr (24 - Index)) and $FF)) then Break;
        Src := Dest xor Cardinal((UInt64(1) shl (32 - Index)) - 1);
      until False;
      Data[Pos + 1] := Byte(Dest and $FF);
      Data[Pos + 2] := Byte((Dest shr 8) and $FF);
      Data[Pos + 3] := Byte((Dest shr 16) and $FF);
      if Dest and $1000000 <> 0 then Data[Pos + 4] := $FF else Data[Pos + 4] := 0;
      Inc(Pos, 5);
    end
    else
    begin
      Mask := ((Mask shl 1) or 1) and 7;
      Inc(Pos);
    end;
  end;
  Distance := Pos - PrevPos;
  if Distance > 3 then State := 0 else State := Mask shl (Distance - 1);
  Result := Pos;
end;

procedure Decode7zFilter(Source, Destination: TStream; Size: Int64;
  Method: UInt64; const Properties: TBytes; Cancel: TFunc<Boolean>);
var
  Data: TBytes;
  History: array[0..255] of Byte;
  N, Carry, Done, I, Distance, HistPos: Integer;
  State, IP: Cardinal;
begin
  Distance := 0; IP := 0;
  case Method of
    3: begin
      if Length(Properties) <> 1 then raise ESevenZip.Create('7z: invalid Delta properties');
      Distance := Integer(Properties[0]) + 1;
    end;
    $03030103: begin
      if not (Length(Properties) in [0, 4]) then raise ESevenZip.Create('7z: invalid BCJ properties');
      if Length(Properties) = 4 then IP := Read32(Properties, 0);
    end;
  else raise ESevenZip.Create('7z: unsupported filter'); end;
  SetLength(Data, 65536 + 4);
  FillChar(History, SizeOf(History), 0);
  HistPos := 0; Carry := 0; State := 0;
  while Size > 0 do
  begin
    if Assigned(Cancel) and Cancel() then raise EAbort.Create('Cancelled');
    N := 65536;
    if Size < N then N := Integer(Size);
    Source.ReadBuffer(Data[Carry], N);
    Dec(Size, N);
    Inc(N, Carry);
    if Method = 3 then
    begin
      for I := 0 to N - 1 do
      begin
        Data[I] := Byte((Integer(Data[I]) + History[HistPos]) and $FF);
        History[HistPos] := Data[I];
        Inc(HistPos);
        if HistPos = Distance then HistPos := 0;
      end;
      Done := N;
    end
    else
      Done := BCJ(Data, N, IP, State);
    Destination.WriteBuffer(Data[0], Done);
    IP := Cardinal((UInt64(IP) + Cardinal(Done)) and $FFFFFFFF);
    Carry := N - Done;
    if Carry > 0 then Move(Data[Done], Data[0], Carry);
  end;
  if Carry > 0 then Destination.WriteBuffer(Data[0], Carry);
end;

end.
