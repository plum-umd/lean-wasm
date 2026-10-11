import Wasm.Binary.Reader

/-! Decoder for the implemented Wasm 3.0 scalar and module fragment.
Decoding is an ordinary computation; its correctness is not assumed by the kernel. -/
namespace Wasm.Binary

private def heapType : DecodeM RefKind := do
  let n ← signed 33
  if n ≥ 0 then return .typeIdx n.toNat
  match n with
  | -16 => return .func
  | -17 => return .extern
  | -13 => return .nofunc
  | -14 => return .noextern
  | -23 => return .exn
  | -12 => return .noexn
  | -18 => return .any
  | -19 => return .eq
  | -20 => return .i31
  | -21 => return .struct_
  | -22 => return .array
  | -15 => return .none
  | _ => malformed "unknown heap type encoding"

private def valueType : DecodeM ValType := do
  match ← byte with
  | 0x7f => return .i32
  | 0x7e => return .i64
  | 0x7d => return .f32
  | 0x7c => return .f64
  | 0x70 => return .ref .func
  | 0x6f => return .ref .extern
  | 0x73 => return .ref .nofunc
  | 0x72 => return .ref .noextern
  | 0x63 => return .ref (← heapType)
  | 0x64 => return .refNonNull (← heapType)
  | 0x7b => pure .v128
  | 0x69 => return .ref .exn
  | 0x74 => return .ref .noexn
  | 0x6e => return .ref .any
  | 0x6d => return .ref .eq
  | 0x6c => return .ref .i31
  | 0x6b => return .ref .struct_
  | 0x6a => return .ref .array
  | 0x71 => return .ref .none
  | _ => malformed "unknown value type encoding"

private def referenceType : DecodeM (RefKind × Bool) := do
  match ← valueType with
  | .ref heap => return (heap, true)
  | .refNonNull heap => return (heap, false)
  | _ => malformed "table or element type must be a reference"

private def storageType : DecodeM Types.StorageType := do
  match ← peek with
  | 0x78 => let _ ← byte; return .i8
  | 0x77 => let _ ← byte; return .i16
  | _ => return .val (Types.embedVal (← valueType))

private def fieldType : DecodeM Types.FieldType := do
  let type ← storageType
  let mutability ← byte
  if mutability > 1 then malformed "unknown field mutability"
  return .mk type (mutability == 1)

private def compositeType : DecodeM CompositeType := do
  match ← byte with
  | 0x60 => return .func ⟨← vector valueType, ← vector valueType⟩
  | 0x5f => return .struct_ (← vector fieldType)
  | 0x5e => return .array (← fieldType)
  | _ => malformed "unknown composite type encoding"

private def subtype : DecodeM (Types.SubType × CompositeType) := do
  let tag ← peek
  let (final, supers) ← if tag == 0x4f || tag == 0x50 then do
    let _ ← byte
    let parents ← vector unsigned
    pure (tag == 0x4f, parents.map Types.HeapType.typeIdx)
  else pure (true, [])
  let composite ← compositeType
  let sub := match composite with
    | .func signature => Types.SubType.func final supers
        (signature.params.map Types.embedVal) (signature.results.map Types.embedVal)
    | .struct_ fields => Types.SubType.struct_ final supers fields
    | .array field => Types.SubType.array final supers field
  return (sub, composite)

private def recursiveType : DecodeM (List (Types.SubType × CompositeType)) := do
  if (← peek) == 0x4e then
    let _ ← byte
    vector subtype
  else return [← subtype]

private def limits : DecodeM (ValType × Nat × Option Nat) := do
  let flags ← byte
  if flags ≥ 8 then malformed "reserved limits flags"
  if flags % 4 ≥ 2 then unsupported "shared limits"
  let address : ValType := if flags ≥ 4 then .i64 else .i32
  let minimum ← unsigned 64
  let maximum ← if flags % 2 == 1 then pure (some (← unsigned 64)) else pure none
  return (address, minimum, maximum)

private def memoryType : DecodeM MemoryType := do
  let (address, minimum, maximum) ← limits
  return ⟨address, minimum, maximum⟩

private def tableType : DecodeM TableType := do
  let (heap, nullable) ← referenceType
  let (address, minimum, maximum) ← limits
  return ⟨address, minimum, maximum, heap, nullable⟩

private def globalType : DecodeM GlobalType := do
  let type ← valueType
  let mutability ← match ← byte with
    | 0 => pure Mutability.const
    | 1 => pure Mutability.var
    | _ => malformed "unknown mutability encoding"
  return ⟨mutability, type⟩

private def blockType : DecodeM BlockType := do
  let first ← peek
  if first == 0x40 then byte *> pure (.val none)
  else if first ≥ 0x63 && first < 0x80 then return .val (some (← valueType))
  else
    let index ← signed 33
    if index < 0 then malformed "negative block type index"
    return .typeIdx index.toNat

private def memarg : DecodeM (Nat × MemArg) := do
  let flags ← unsigned
  if flags ≥ 128 then malformed "reserved memory operand flags"
  let memory ← if flags ≥ 64 then unsigned else pure 0
  let offset ← unsigned 64
  return (memory, ⟨flags % 64, offset⟩)

private def simpleOpcode : Nat → Option Instr
  | 0x00 => some (.unreachable)
  | 0x01 => some (.nop)
  | 0x0f => some (.return_)
  | 0x1a => some (.drop)
  | 0x1b => some (.select none)
  | 0x45 => some (.eqz .i32)
  | 0x46 => some (.intRel .i32 .eq)
  | 0x47 => some (.intRel .i32 .ne)
  | 0x48 => some (.intRel .i32 .ltS)
  | 0x49 => some (.intRel .i32 .ltU)
  | 0x4a => some (.intRel .i32 .gtS)
  | 0x4b => some (.intRel .i32 .gtU)
  | 0x4c => some (.intRel .i32 .leS)
  | 0x4d => some (.intRel .i32 .leU)
  | 0x4e => some (.intRel .i32 .geS)
  | 0x4f => some (.intRel .i32 .geU)
  | 0x50 => some (.eqz .i64)
  | 0x51 => some (.intRel .i64 .eq)
  | 0x52 => some (.intRel .i64 .ne)
  | 0x53 => some (.intRel .i64 .ltS)
  | 0x54 => some (.intRel .i64 .ltU)
  | 0x55 => some (.intRel .i64 .gtS)
  | 0x56 => some (.intRel .i64 .gtU)
  | 0x57 => some (.intRel .i64 .leS)
  | 0x58 => some (.intRel .i64 .leU)
  | 0x59 => some (.intRel .i64 .geS)
  | 0x5a => some (.intRel .i64 .geU)
  | 0x5b => some (.floatRel .w32 .eq)
  | 0x5c => some (.floatRel .w32 .ne)
  | 0x5d => some (.floatRel .w32 .lt)
  | 0x5e => some (.floatRel .w32 .gt)
  | 0x5f => some (.floatRel .w32 .le)
  | 0x60 => some (.floatRel .w32 .ge)
  | 0x61 => some (.floatRel .w64 .eq)
  | 0x62 => some (.floatRel .w64 .ne)
  | 0x63 => some (.floatRel .w64 .lt)
  | 0x64 => some (.floatRel .w64 .gt)
  | 0x65 => some (.floatRel .w64 .le)
  | 0x66 => some (.floatRel .w64 .ge)
  | 0x67 => some (.intUnary .i32 .clz)
  | 0x68 => some (.intUnary .i32 .ctz)
  | 0x69 => some (.intUnary .i32 .popcnt)
  | 0x6a => some (.binop .i32 .add)
  | 0x6b => some (.binop .i32 .sub)
  | 0x6c => some (.binop .i32 .mul)
  | 0x6d => some (.intBinary .i32 .divS)
  | 0x6e => some (.intBinary .i32 .divU)
  | 0x6f => some (.intBinary .i32 .remS)
  | 0x70 => some (.intBinary .i32 .remU)
  | 0x71 => some (.intBinary .i32 .and_)
  | 0x72 => some (.intBinary .i32 .or_)
  | 0x73 => some (.intBinary .i32 .xor)
  | 0x74 => some (.intBinary .i32 .shl)
  | 0x75 => some (.intBinary .i32 .shrS)
  | 0x76 => some (.intBinary .i32 .shrU)
  | 0x77 => some (.intBinary .i32 .rotl)
  | 0x78 => some (.intBinary .i32 .rotr)
  | 0x79 => some (.intUnary .i64 .clz)
  | 0x7a => some (.intUnary .i64 .ctz)
  | 0x7b => some (.intUnary .i64 .popcnt)
  | 0x7c => some (.binop .i64 .add)
  | 0x7d => some (.binop .i64 .sub)
  | 0x7e => some (.binop .i64 .mul)
  | 0x7f => some (.intBinary .i64 .divS)
  | 0x80 => some (.intBinary .i64 .divU)
  | 0x81 => some (.intBinary .i64 .remS)
  | 0x82 => some (.intBinary .i64 .remU)
  | 0x83 => some (.intBinary .i64 .and_)
  | 0x84 => some (.intBinary .i64 .or_)
  | 0x85 => some (.intBinary .i64 .xor)
  | 0x86 => some (.intBinary .i64 .shl)
  | 0x87 => some (.intBinary .i64 .shrS)
  | 0x88 => some (.intBinary .i64 .shrU)
  | 0x89 => some (.intBinary .i64 .rotl)
  | 0x8a => some (.intBinary .i64 .rotr)
  | 0x8b => some (.floatUnary .w32 .abs)
  | 0x8c => some (.floatUnary .w32 .neg)
  | 0x8d => some (.floatUnary .w32 .ceil)
  | 0x8e => some (.floatUnary .w32 .floor)
  | 0x8f => some (.floatUnary .w32 .trunc)
  | 0x90 => some (.floatUnary .w32 .nearest)
  | 0x91 => some (.floatUnary .w32 .sqrt)
  | 0x92 => some (.floatBinary .w32 .add)
  | 0x93 => some (.floatBinary .w32 .sub)
  | 0x94 => some (.floatBinary .w32 .mul)
  | 0x95 => some (.floatBinary .w32 .div)
  | 0x96 => some (.floatBinary .w32 .min)
  | 0x97 => some (.floatBinary .w32 .max)
  | 0x98 => some (.floatBinary .w32 .copysign)
  | 0x99 => some (.floatUnary .w64 .abs)
  | 0x9a => some (.floatUnary .w64 .neg)
  | 0x9b => some (.floatUnary .w64 .ceil)
  | 0x9c => some (.floatUnary .w64 .floor)
  | 0x9d => some (.floatUnary .w64 .trunc)
  | 0x9e => some (.floatUnary .w64 .nearest)
  | 0x9f => some (.floatUnary .w64 .sqrt)
  | 0xa0 => some (.floatBinary .w64 .add)
  | 0xa1 => some (.floatBinary .w64 .sub)
  | 0xa2 => some (.floatBinary .w64 .mul)
  | 0xa3 => some (.floatBinary .w64 .div)
  | 0xa4 => some (.floatBinary .w64 .min)
  | 0xa5 => some (.floatBinary .w64 .max)
  | 0xa6 => some (.floatBinary .w64 .copysign)
  | 0xa7 => some (.intConvert .wrapI64)
  | 0xa8 => some (.floatConvert (.trunc .w32 .w32 true false))
  | 0xa9 => some (.floatConvert (.trunc .w32 .w32 false false))
  | 0xaa => some (.floatConvert (.trunc .w32 .w64 true false))
  | 0xab => some (.floatConvert (.trunc .w32 .w64 false false))
  | 0xac => some (.intConvert .extendI32S)
  | 0xad => some (.intConvert .extendI32U)
  | 0xae => some (.floatConvert (.trunc .w64 .w32 true false))
  | 0xaf => some (.floatConvert (.trunc .w64 .w32 false false))
  | 0xb0 => some (.floatConvert (.trunc .w64 .w64 true false))
  | 0xb1 => some (.floatConvert (.trunc .w64 .w64 false false))
  | 0xb2 => some (.floatConvert (.convert .w32 .w32 true))
  | 0xb3 => some (.floatConvert (.convert .w32 .w32 false))
  | 0xb4 => some (.floatConvert (.convert .w32 .w64 true))
  | 0xb5 => some (.floatConvert (.convert .w32 .w64 false))
  | 0xb6 => some (.floatConvert .demote)
  | 0xb7 => some (.floatConvert (.convert .w64 .w32 true))
  | 0xb8 => some (.floatConvert (.convert .w64 .w32 false))
  | 0xb9 => some (.floatConvert (.convert .w64 .w64 true))
  | 0xba => some (.floatConvert (.convert .w64 .w64 false))
  | 0xbb => some (.floatConvert .promote)
  | 0xbc => some (.floatConvert .reinterpretI32)
  | 0xbd => some (.floatConvert .reinterpretI64)
  | 0xbe => some (.floatConvert .reinterpretF32)
  | 0xbf => some (.floatConvert .reinterpretF64)
  | 0xc0 => some (.intConvert .extendI32_8S)
  | 0xc1 => some (.intConvert .extendI32_16S)
  | 0xc2 => some (.intConvert .extendI64_8S)
  | 0xc3 => some (.intConvert .extendI64_16S)
  | 0xc4 => some (.intConvert .extendI64_32S)
  | 0xd1 => some (.refIsNull)
  | _ => none

private def extendedOpcode : DecodeM Instr := do
  match ← unsigned with
  | n =>
    if n < 8 then
      let integer : NumWidth := if n < 4 then .w32 else .w64
      let float : NumWidth := if n % 4 < 2 then .w32 else .w64
      return .floatConvert (.trunc integer float (n % 2 == 0) true)
    else match n with
      | 8 =>
        modify fun reader => {reader with usesData := true}
        let data ← unsigned
        return .memoryInit (← unsigned) data
      | 9 =>
        modify fun reader => {reader with usesData := true}
        return .dataDrop (← unsigned)
      | 10 => return .memoryCopy (← unsigned) (← unsigned)
      | 11 => return .memoryFill (← unsigned)
      | 12 => let elem ← unsigned; return .tableInit (← unsigned) elem
      | 13 => return .elemDrop (← unsigned)
      | 14 => return .tableCopy (← unsigned) (← unsigned)
      | 15 => return .tableGrow (← unsigned)
      | 16 => return .tableSize (← unsigned)
      | 17 => return .tableFill (← unsigned)
      | _ => malformed "unknown extended opcode"

private def scalarOpcode (opcode : Nat) : DecodeM Instr := do
  if let some instr := simpleOpcode opcode then return instr
  if 0x28 ≤ opcode && opcode ≤ 0x35 then
    let ops : List LoadOp := [.i32, .i64, .f32, .f64, .i32_8S, .i32_8U, .i32_16S,
      .i32_16U, .i64_8S, .i64_8U, .i64_16S, .i64_16U, .i64_32S, .i64_32U]
    let some op := ops[opcode - 0x28]? | malformed "load opcode"
    let (memory, arg) ← memarg
    return .load op memory arg
  if 0x36 ≤ opcode && opcode ≤ 0x3e then
    let ops : List StoreOp := [.i32, .i64, .f32, .f64, .i32_8, .i32_16,
      .i64_8, .i64_16, .i64_32]
    let some op := ops[opcode - 0x36]? | malformed "store opcode"
    let (memory, arg) ← memarg
    return .store op memory arg
  match opcode with
  | 0x0c => return .br (← unsigned)
  | 0x0d => return .brIf (← unsigned)
  | 0x0e => return .brTable (← vector unsigned) (← unsigned)
  | 0x10 => return .call (← unsigned)
  | 0x11 => let type ← unsigned; return .callIndirect (← unsigned) type
  | 0x1c => return .select (some (← vector valueType))
  | 0x20 => return .localGet (← unsigned)
  | 0x21 => return .localSet (← unsigned)
  | 0x22 => return .localTee (← unsigned)
  | 0x23 => return .globalGet (← unsigned)
  | 0x24 => return .globalSet (← unsigned)
  | 0x25 => return .tableGet (← unsigned)
  | 0x26 => return .tableSet (← unsigned)
  | 0x3f => return .memorySize (← unsigned)
  | 0x40 => return .memoryGrow (← unsigned)
  | 0x41 => return .const (.i32 (BitVec.ofInt 32 (← signed 32)))
  | 0x42 => return .const (.i64 (BitVec.ofInt 64 (← signed 64)))
  | 0x43 => return .const (.f32 (BitVec.ofNat 32 (← littleEndian 4)))
  | 0x44 => return .const (.f64 (BitVec.ofNat 64 (← littleEndian 8)))
  | 0xd0 => return .refNull (← heapType)
  | 0xd2 => return .refFunc (← unsigned)
  | 0xfc => extendedOpcode
  | 0xfb =>
    let op ← unsigned
    match op with
    | 0 => return .structNew (← unsigned) false
    | 1 => return .structNew (← unsigned) true
    | 2 => return .structGet (← unsigned) (← unsigned) none
    | 3 => return .structGet (← unsigned) (← unsigned) (some true)
    | 4 => return .structGet (← unsigned) (← unsigned) (some false)
    | 5 => return .structSet (← unsigned) (← unsigned)
    | 6 => return .arrayOp (.new_ (← unsigned) false)
    | 7 => return .arrayOp (.new_ (← unsigned) true)
    | 8 => return .arrayOp (.newFixed (← unsigned) (← unsigned))
    | 9 => return .arrayOp (.newData (← unsigned) (← unsigned))
    | 10 => return .arrayOp (.newElem (← unsigned) (← unsigned))
    | 11 => return .arrayOp (.get (← unsigned) none)
    | 12 => return .arrayOp (.get (← unsigned) (some true))
    | 13 => return .arrayOp (.get (← unsigned) (some false))
    | 14 => return .arrayOp (.set (← unsigned))
    | 15 => return .arrayOp .len
    | 16 => return .arrayOp (.fill (← unsigned))
    | 17 => return .arrayOp (.copy (← unsigned) (← unsigned))
    | 18 => return .arrayOp (.initData (← unsigned) (← unsigned))
    | 19 => return .arrayOp (.initElem (← unsigned) (← unsigned))
    | 20 => return .refTest false (← heapType)
    | 21 => return .refTest true (← heapType)
    | 22 => return .refCast false (← heapType)
    | 23 => return .refCast true (← heapType)
    | 24 | 25 => do
      let flags ← byte
      unless flags < 4 do malformed "invalid cast branch flags"
      let label ← unsigned
      let source ← heapType
      let target ← heapType
      return .brOnCast (op == 25) label
        ⟨flags &&& 1 != 0, source⟩ ⟨flags &&& 2 != 0, target⟩
    | 26 => pure (.gcReference .anyConvertExtern)
    | 27 => pure (.gcReference .externConvertAny)
    | 28 => pure (.gcReference .i31New)
    | 29 => pure (.gcReference .i31GetS)
    | 30 => pure (.gcReference .i31GetU)
    | _ => unsupported "GC opcode"
  | 0xfd =>
    let some opcode := VectorOpcode.ofBinary (← unsigned) | malformed "unknown SIMD opcode"
    if opcode == .v128_const then
      return .const (.v128 (BitVec.ofNat 128 (← littleEndian 16)))
    let (memory, arg) ← if opcode.isMemory then memarg else pure (0, {})
    let count := if opcode == .i8x16_shuffle then 16
      else if opcode.name.endsWith "lane" ||
        (opcode.name.splitOn "extract_lane").length > 1 then 1 else 0
    let lanes ← (List.replicate count ()).mapM fun _ => return (← byte)
    return .vector ⟨opcode, lanes, memory, arg⟩
  | 0xfe => unsupported "atomic opcode"
  | 0x08 => return .throw_ (← unsigned)
  | 0x0a => return .throwRef
  | 0x12 => return .returnCall (← unsigned)
  | 0x13 => let type ← unsigned; return .returnCallIndirect (← unsigned) type
  | 0x15 => return .returnCallRef (← unsigned)
  | 0x14 => return .callRef (← unsigned)
  | 0xd4 => return .refAsNonNull
  | 0xd5 => return .brOnNull (← unsigned)
  | 0xd6 => return .brOnNonNull (← unsigned)
  | 0xd3 => pure (.gcReference .eq)
  | _ => malformed s!"unknown opcode {opcode}"

private def catchClause : DecodeM Catch := do
  match ← byte with
  | 0 => return .tag (← unsigned) (← unsigned) false
  | 1 => return .tag (← unsigned) (← unsigned) true
  | 2 => return .all (← unsigned) false
  | 3 => return .all (← unsigned) true
  | _ => malformed "unknown catch clause"

private def code : Nat → Bool → DecodeM (List Instr × Bool)
  | 0, _ => malformed "instruction nesting exceeds binary size"
  | fuel + 1, allowElse => do
    let opcode ← byte
    if opcode == 0x0b then return ([], false)
    if opcode == 0x05 then
      if allowElse then return ([], true) else malformed "misplaced else"
    let instr ← if opcode == 0x02 || opcode == 0x03 || opcode == 0x04 then do
      let type ← blockType
      let (body, hasElse) ← code fuel (opcode == 0x04)
      if opcode == 0x04 then
        let other ← if hasElse then (code fuel false).map Prod.fst else pure []
        pure (Instr.if_ type body other)
      else pure (if opcode == 0x02 then Instr.block type body else Instr.loop type body)
    else if opcode == 0x1f then do
      let type ← blockType
      let catches ← vector catchClause
      let (body, _) ← code fuel false
      pure (.tryTable type catches body)
    else scalarOpcode opcode
    let (tail, hasElse) ← code fuel allowElse
    return (instr :: tail, hasElse)

private def expression : DecodeM (List Instr) := do
  let reader ← get
  return (← code (reader.limit - reader.offset + 1) false).1

private def importEntry : DecodeM Import := do
  let owner ← name
  let importedName ← name
  let desc ← match ← byte with
    | 0 => pure (ImportDesc.func (← unsigned))
    | 1 => pure (ImportDesc.table (← tableType))
    | 2 => pure (ImportDesc.memory (← memoryType))
    | 3 => pure (ImportDesc.global (← globalType))
    | 4 => do expect 0; pure (ImportDesc.tag (← unsigned))
    | _ => malformed "unknown import kind"
  return ⟨owner, importedName, desc⟩

private def exportEntry : DecodeM Export := do
  let exportedName ← name
  let kind ← byte
  let index ← unsigned
  let desc ← match kind with
    | 0 => pure (ExternIdx.func index)
    | 1 => pure (ExternIdx.table index)
    | 2 => pure (ExternIdx.memory index)
    | 3 => pure (ExternIdx.global index)
    | 4 => pure (.tag index)
    | _ => malformed "unknown export kind"
  return ⟨exportedName, desc⟩

private def tableEntry : DecodeM Table := do
  if (← peek) == 0x40 then
    expect 0x40
    expect 0
    let type ← tableType
    return ⟨type, ← expression⟩
  else return {type := ← tableType}

private def globalEntry : DecodeM Global := do return ⟨← globalType, ← expression⟩

private def elementEntry : DecodeM Elem := do
  let flags ← unsigned
  if flags > 7 then malformed "unknown element segment flags"
  let mode ← match flags % 4 with
    | 0 => pure (ElemMode.active 0 (← expression))
    | 1 => pure ElemMode.passive
    | 2 => pure (ElemMode.active (← unsigned) (← expression))
    | _ => pure ElemMode.declarative
  let (heap, nullable) ←
    if flags == 0 || flags == 4 then pure (Types.HeapType.func, decide (flags ≥ 4))
    else if flags < 4 then expect 0 *> pure (Types.HeapType.func, decide (flags ≥ 4))
    else referenceType
  let initializers ← if flags < 4 then
    vector (do return [Instr.refFunc (← unsigned)]) else vector expression
  return ⟨heap, initializers, mode, nullable⟩

private def dataEntry : DecodeM Data := do
  let flags ← unsigned
  let mode ← match flags with
    | 0 => pure (DataMode.active 0 (← expression))
    | 1 => pure DataMode.passive
    | 2 => pure (DataMode.active (← unsigned) (← expression))
    | _ => malformed "unknown data segment flags"
  let raw ← blob
  return ⟨raw.data.map (fun b => BitVec.ofNat 8 b.toNat), mode⟩

private def functionBody : DecodeM (List ValType × List Instr) := sized do
  let groups ← vector (do return ((← unsigned), (← valueType)))
  let count := groups.foldl (fun n group => n + group.1) 0
  if count ≥ 2^32 then malformed "too many locals"
  if count > 1000000 then unsupported "local declaration allocation budget"
  let locals := groups.flatMap fun (n, type) => List.replicate n type
  return (locals, ← expression)

private def sectionRank : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 13 => 6
  | 6 => 7 | 7 => 8 | 8 => 9 | 9 => 10 | 12 => 11 | 10 => 12 | 11 => 13
  | _ => 0

private def moduleBody : DecodeM Module := do
  for expected in [0, 0x61, 0x73, 0x6d, 1, 0, 0, 0] do expect expected
  let mut result : Module := {}
  let mut functionTypes : List Nat := []
  let mut bodies : List (List ValType × List Instr) := []
  let mut declaredData : Option Nat := none
  let mut rank := 0
  while (← get).offset < (← get).limit do
    let id ← byte
    let nextRank := sectionRank id
    if id != 0 then
      if nextRank == 0 then malformed "unknown section id"
      if nextRank ≤ rank then malformed "duplicate or out-of-order section"
      rank := nextRank
    match id with
    | 0 => sized do
      let _ ← name
      modify fun reader => {reader with offset := reader.limit}
    | 1 =>
      let groups ← sized (vector recursiveType)
      let signatures := groups.flatten.map Prod.snd
      let declarations := groups.map (List.map Prod.fst)
      result := {result with types := signatures, typeGroups := declarations}
    | 2 => result := {result with imports := ← sized (vector importEntry)}
    | 3 => functionTypes := ← sized (vector unsigned)
    | 4 => result := {result with tables := ← sized (vector tableEntry)}
    | 5 => result := {result with mems := ← sized (vector memoryType)}
    | 6 => result := {result with globals := ← sized (vector globalEntry)}
    | 7 => result := {result with exports := ← sized (vector exportEntry)}
    | 8 => result := {result with start := some (← sized unsigned)}
    | 9 => result := {result with elems := ← sized (vector elementEntry)}
    | 10 => bodies := ← sized (vector functionBody)
    | 11 => result := {result with datas := ← sized (vector dataEntry)}
    | 12 => declaredData := some (← sized unsigned)
    | 13 => result := {result with tags := ← sized (vector (do expect 0; unsigned))}
    | _ => malformed "unknown section id"
  if functionTypes.length != bodies.length then malformed "function and code counts differ"
  if let some count := declaredData then
    if count != result.datas.length then malformed "data count differs from data section"
  if (← get).usesData && declaredData.isNone then malformed "data count section required"
  return {result with funcs := (functionTypes.zip bodies).map fun (type, locals, body) =>
    ⟨type, locals, body⟩}

/-- Decode directly to the source module used by text validation and instantiation. -/
def decode (bytes : ByteArray) : Except DecodeError Module :=
  (moduleBody.run ⟨bytes, 0, bytes.size, false⟩).map Prod.fst

end Wasm.Binary
