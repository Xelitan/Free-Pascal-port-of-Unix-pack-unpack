//Free Pascal port of Unix pack / unpack (Huffman coder)
//Version 1.0 – 20-04-2026
//License : MIT
//Author  : www.xelitan.com

//Usage:
//    pack -c <input_file> <output_file>   (like `pack`)
//    pack -d <input_file> <output_file>   (like `unpack`)
//
//  File format: classic Unix .z pack format
//    Bytes 0-1  : magic  0x1F 0x1E  (US RS)
//    Bytes 2-5  : original size, big-endian 32-bit
//    Byte  6    : maxlev  (number of tree levels)
//    Bytes 7 .. : levcount[1..maxlev-1], then levcount[maxlev]-2
//    Then       : leaf characters in level order (0-255 only, not the EOF symbol)
//    Then       : packed bit stream, MSB-first within each byte

program pack;

{$mode objfpc}{$H+}
{$RANGECHECKS OFF}
{$OVERFLOWCHECKS OFF}

uses
  Classes, SysUtils;

const
  CEND    = 256;      { index of the EOF / END symbol }
  MAGIC1  = $1F;      { US }
  MAGIC2  = $1E;      { RS }
  BUFSIZE = 4096;

{ ── Types ───────────────────────────────────────────────────── }
type
  THeapRec = record
    count : Int64;
    node  : Integer;
  end;

{ ── Globals shared between pack and build routines ──────────── }
var
  freq      : array[0..CEND] of Int64;       { char frequencies (doubled) }
  parr      : array[0..2*CEND+2] of Integer; { Huffman tree parents }
  clen      : array[0..CEND] of Integer;     { code bit-lengths }
  cbits     : array[0..CEND] of LongInt;     { canonical code patterns }
  heap      : array[1..CEND+2] of THeapRec;
  hsize     : Integer;                        { current heap size }
  lastNode  : Integer;
  maxLev    : Integer;
  levCnt    : array[0..25] of Integer;
  diffBytes : Integer;
  inSize    : Int64;                          { original file size in bytes }

{ ═══════════════════════════════════════════════════════════════
  PACK (compress) side
  ═══════════════════════════════════════════════════════════════ }

{ ── Min-heap sift-down ──────────────────────────────────────── }
procedure Heapify(i: Integer);
var
  k, lastP : Integer;
  sub      : THeapRec;
begin
  sub   := heap[i];
  lastP := hsize div 2;
  while i <= lastP do begin
    k := 2 * i;
    if (k < hsize) and (heap[k].count > heap[k+1].count) then
      Inc(k);
    if sub.count < heap[k].count then Break;
    heap[i] := heap[k];
    i := k;
  end;
  heap[i] := sub;
end;

{ ── Count character frequencies (counts are doubled) ────────── }
procedure CountFreq(inStream: TStream);
var
  buf    : array[0..BUFSIZE-1] of Byte;
  i, n   : Integer;
begin
  FillChar(freq, SizeOf(freq), 0);
  n := inStream.Read(buf, BUFSIZE);
  while n > 0 do begin
    for i := 0 to n-1 do
      Inc(freq[buf[i]], 2);
    n := inStream.Read(buf, BUFSIZE);
  end;
end;

{ ── Build Huffman tree and compute canonical code patterns ──── }
procedure BuildTree;
var
  i, c, p, depth : Integer;
  incVal, mask   : LongInt;
begin
  { Populate heap with all symbols that have non-zero frequency }
  diffBytes := -1;
  freq[CEND] := 1;   { EOF symbol always present }
  inSize := 0;
  hsize  := 0;
  for i := CEND downto 0 do begin
    parr[i] := 0;
    if freq[i] > 0 then begin
      Inc(diffBytes);
      Inc(inSize, freq[i]);
      Inc(hsize);
      heap[hsize].count := freq[i];
      heap[hsize].node  := i;
    end;
  end;
  inSize := inSize shr 1;  { actual byte count (frequencies were doubled) }

  { Build min-heap }
  for i := hsize div 2 downto 1 do
    Heapify(i);

  { Combine the two smallest nodes repeatedly }
  lastNode := CEND;
  while hsize > 1 do begin
    Inc(lastNode);
    parr[heap[1].node] := lastNode;
    incVal             := heap[1].count;
    heap[1]            := heap[hsize];
    Dec(hsize);
    Heapify(1);
    parr[heap[1].node] := lastNode;
    heap[1].node       := lastNode;
    Inc(heap[1].count, incVal);
    Heapify(1);
  end;
  parr[lastNode] := 0;

  { Measure code lengths by walking parent pointers }
  maxLev := 0;
  for i := 0 to 24 do levCnt[i] := 0;
  for i := 0 to CEND do begin
    depth := 0;
    p := parr[i];
    while p <> 0 do begin
      Inc(depth);
      p := parr[p];
    end;
    Inc(levCnt[depth]);
    clen[i] := depth;
    if depth > maxLev then maxLev := depth;
  end;

  if maxLev > 24 then
    raise Exception.Create('Huffman tree has too many levels (file too large)');

  { Assign canonical bit patterns (left-aligned in 24-bit space) }
  incVal := LongInt(1) shl 24;
  incVal := incVal shr maxLev;
  mask   := 0;
  for i := maxLev downto 1 do begin
    for c := 0 to CEND do
      if clen[c] = i then begin
        cbits[c] := mask;
        Inc(mask, incVal);
      end;
    mask   := mask and (not incVal);
    incVal := incVal shl 1;
  end;
end;

{ ── Write pack-format file header ───────────────────────────── }
procedure WritePackHeader(outStream: TStream);
var
  i, c : Integer;
begin
  outStream.WriteByte(MAGIC1);
  outStream.WriteByte(MAGIC2);
  { Original size big-endian }
  outStream.WriteByte((inSize shr 24) and $FF);
  outStream.WriteByte((inSize shr 16) and $FF);
  outStream.WriteByte((inSize shr  8) and $FF);
  outStream.WriteByte( inSize         and $FF);
  { maxlev }
  outStream.WriteByte(maxLev);
  { Level counts; last entry stored as levCnt[maxLev]-2 }
  for i := 1 to maxLev-1 do
    outStream.WriteByte(levCnt[i]);
  outStream.WriteByte(levCnt[maxLev] - 2);
  { Leaf characters in level order (symbols 0..255; CEND is NOT written) }
  for i := 1 to maxLev do
    for c := 0 to CEND-1 do
      if clen[c] = i then
        outStream.WriteByte(c);
end;

{ ── Encode input stream and write packed output ─────────────── }
procedure PackStream(inStream, outStream: TStream);
var
  buf      : array[0..BUFSIZE-1] of Byte;
  n, j     : Integer;
  outByte  : Byte;
  bitsLeft : Integer;
  mask     : Int64;
  b        : array[0..3] of Byte;
  idx      : Integer;

  { Emit the code for symbol sym into the bit stream }
  procedure OutCode(sym: Integer);
  begin
    { Shift canonical code left by bitsLeft so its MSB aligns with bit 31 }
    mask := Int64(cbits[sym]) shl bitsLeft;
    b[0] := (mask shr 24) and $FF;
    b[1] := (mask shr 16) and $FF;
    b[2] := (mask shr  8) and $FF;
    b[3] :=  mask          and $FF;

    { Merge or start current output byte }
    if bitsLeft = 8 then
      outByte := b[0]
    else
      outByte := outByte or b[0];

    Dec(bitsLeft, clen[sym]);
    idx := 1;

    { Flush full output bytes produced by this code }
    while bitsLeft < 0 do begin
      outStream.WriteByte(outByte);
      outByte := b[idx];
      Inc(idx);
      Inc(bitsLeft, 8);
    end;

    { If we landed exactly on a byte boundary, flush it too }
    if bitsLeft = 0 then begin
      outStream.WriteByte(outByte);
      outByte  := 0;
      bitsLeft := 8;
    end;
  end;

begin
  CountFreq(inStream);
  BuildTree;

  if inSize = 0 then
    raise Exception.Create('Empty file – nothing to pack');

  WritePackHeader(outStream);

  { Re-read input and encode each byte }
  inStream.Position := 0;
  bitsLeft := 8;
  outByte  := 0;

  n := inStream.Read(buf, BUFSIZE);
  while n > 0 do begin
    for j := 0 to n-1 do
      OutCode(buf[j]);
    n := inStream.Read(buf, BUFSIZE);
  end;

  OutCode(CEND);   { emit the EOF marker code }

  { Flush any remaining partial byte }
  if bitsLeft < 8 then
    outStream.WriteByte(outByte);
end;

{ ═══════════════════════════════════════════════════════════════
  UNPACK (decompress) side
  ═══════════════════════════════════════════════════════════════ }

{ ── Try to read one byte; return -1 at end-of-stream ────────── }
function TryReadByte(s: TStream): Integer;
var
  b : Byte;
begin
  if s.Read(b, SizeOf(b)) = SizeOf(b) then
    Result := Integer(b)
  else
    Result := -1;
end;

{ ── Decode packed stream and write original data ────────────── }
procedure UnpackStream(inStream, outStream: TStream);
var
  h0, h1    : Integer;
  origSize  : Int64;
  mxLev     : Integer;
  { Raw leaf counts per level as read from the header }
  rawCnt    : array[1..24] of Integer;
  { Internal-node counts (after conversion) }
  intNd     : array[1..24] of Integer;
  { Flat character table (all leaf chars, level by level) }
  chars     : array[0..511] of Byte;
  { Index in chars[] where each level's leaves begin }
  treeStart : array[1..24] of Integer;
  { Index just past the last real char = EOF sentinel position }
  eofMark   : Integer;
  charTotal : Integer;
  i, j, c  : Integer;
  nchildren : Integer;
  lev       : Integer;
  nodeIdx   : Integer;
  leafIdx   : Integer;
  curByte   : Integer;
  bit       : Byte;
  outBuf    : array[0..BUFSIZE-1] of Byte;
  outPos    : Integer;
  done      : Boolean;
begin
  { ── Read magic ── }
  h0 := TryReadByte(inStream);
  h1 := TryReadByte(inStream);
  if (h0 < 0) or (h1 < 0) then
    raise Exception.Create('Unexpected EOF reading header');
  if (h0 = MAGIC1) and (h1 = MAGIC1) then
    raise Exception.Create('Old-style pack format is not supported');
  if (h0 <> MAGIC1) or (h1 <> MAGIC2) then
    raise Exception.CreateFmt(
      'Not a packed file (magic %02X %02X, expected %02X %02X)',
      [h0, h1, MAGIC1, MAGIC2]);

  { ── Original size (big-endian 4 bytes) ── }
  origSize := 0;
  for i := 0 to 3 do begin
    c := TryReadByte(inStream);
    if c < 0 then raise Exception.Create('Unexpected EOF in header (size)');
    origSize := origSize * 256 + c;
  end;

  { ── maxlev ── }
  mxLev := TryReadByte(inStream);
  if (mxLev <= 0) or (mxLev > 24) then
    raise Exception.Create('Bad pack header (maxlev out of range)');

  { ── Level counts ──
    Header stores:  rawCnt[1..maxlev-1]  then  levCnt[maxlev]-2
    We read them as-is, then correct the last entry. }
  for i := 1 to mxLev do begin
    c := TryReadByte(inStream);
    if c < 0 then raise Exception.Create('Unexpected EOF in header (levcount)');
    rawCnt[i] := c;
  end;
  { The last entry was written as levCnt[maxlev]-2; restore it }
  Inc(rawCnt[mxLev], 2);

  { ── Read the leaf character table ──
    The C unpack.c loop reads rawCnt[i] chars per level
    (using the ORIGINAL rawCnt before the +=2 fixup).
    Then it reads one extra char.  After that it does += 2.
    Net result for level maxlev: (rawCnt[mxLev]-2) + 1 = rawCnt[mxLev]-1 chars stored,
    and the EOF sentinel is one position past the last stored char. }
  charTotal := 0;
  for i := 1 to mxLev do begin
    treeStart[i] := charTotal;
    { Number of chars to read in the loop: rawCnt[i] for i<maxlev, rawCnt[i]-2 for i=maxlev }
    if i < mxLev then
      j := rawCnt[i]
    else
      j := rawCnt[mxLev] - 2;
    while j > 0 do begin
      c := TryReadByte(inStream);
      if c < 0 then raise Exception.Create('Unexpected EOF in character table');
      chars[charTotal] := Byte(c);
      Inc(charTotal);
      Dec(j);
    end;
  end;
  { One extra char (the C *eof++ = *inp++ after the level loop) }
  c := TryReadByte(inStream);
  if c < 0 then raise Exception.Create('Unexpected EOF in character table (final char)');
  chars[charTotal] := Byte(c);
  Inc(charTotal);
  eofMark := charTotal;   { EOF sentinel = index just past the last real char }

  { ── Convert leaf counts to internal-node counts ──
    Mirrors the conversion in unpack.c getdict():
      nchildren = 0
      for i = maxlev downto 1:
          c = rawCnt[i]
          rawCnt[i] = nchildren / 2
          nchildren = nchildren/2 + c  }
  nchildren := 0;
  for i := mxLev downto 1 do begin
    c         := rawCnt[i];
    intNd[i]  := nchildren div 2;
    nchildren := nchildren div 2 + c;
  end;

  { ── Decode the bit stream ── }
  lev     := 1;
  nodeIdx := 0;
  outPos  := 0;
  done    := False;

  curByte := TryReadByte(inStream);
  while (curByte >= 0) and not done do begin
    bit := $80;
    while (bit <> 0) and not done do begin
      nodeIdx := nodeIdx * 2;
      if (curByte and Integer(bit)) <> 0 then Inc(nodeIdx);
      bit := bit shr 1;

      leafIdx := nodeIdx - intNd[lev];
      if leafIdx >= 0 then begin
        { At a leaf: check for EOF sentinel }
        j := treeStart[lev] + leafIdx;
        if j >= eofMark then begin
          done := True;           { reached the END symbol }
        end else begin
          outBuf[outPos] := chars[j];
          Inc(outPos);
          if outPos = BUFSIZE then begin
            outStream.WriteBuffer(outBuf, outPos);
            outPos := 0;
          end;
          lev     := 1;
          nodeIdx := 0;
        end;
      end else
        Inc(lev);
    end;

    if not done then
      curByte := TryReadByte(inStream);
  end;

  if not done then
    raise Exception.Create('Unexpected end of packed data');

  { Flush remaining output }
  if outPos > 0 then
    outStream.WriteBuffer(outBuf, outPos);
end;

{ ═══════════════════════════════════════════════════════════════
  Main program
  ═══════════════════════════════════════════════════════════════ }

procedure Usage;
begin
  WriteLn('Usage:');
  WriteLn('  pack -c <input> <output>   (pack a file)');
  WriteLn('  pack -d <input> <output>   (unpack a file)');
end;

var
  mode, inPath, outPath : string;
  inStream, outStream   : TStream;
  doCompress            : Boolean;
begin
  inStream  := nil;
  outStream := nil;
  try
    if ParamCount <> 3 then begin
      Usage;
      Halt(1);
    end;

    mode    := ParamStr(1);
    inPath  := ParamStr(2);
    outPath := ParamStr(3);

    if (mode = '-c') or (mode = '--compress') then
      doCompress := True
    else if (mode = '-d') or (mode = '--decompress') then
      doCompress := False
    else begin
      Usage;
      Halt(1);
    end;

    inStream  := TFileStream.Create(inPath,  fmOpenRead  or fmShareDenyWrite);
    outStream := TFileStream.Create(outPath, fmCreate);

    if doCompress then
      PackStream(inStream, outStream)
    else
      UnpackStream(inStream, outStream);

    FreeAndNil(inStream);
    FreeAndNil(outStream);
  except
    on E: Exception do begin
      FreeAndNil(inStream);
      FreeAndNil(outStream);
      WriteLn(ErrOutput, 'Error: ', E.Message);
      Halt(1);
    end;
  end;
end.
