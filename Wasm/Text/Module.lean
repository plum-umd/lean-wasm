import Wasm.Text.SExpr
import Wasm.Text.Float
import Wasm.Module

namespace Wasm.Text

inductive Error where
  | unsupported (message : String)
  | invalid (message : String)
  deriving Repr, BEq

abbrev Result := Except Error

def name (bytes : ByteArray) : Result String :=
  match String.fromUTF8? bytes with
  | some s => .ok s
  | none => .error (.invalid "name is not UTF-8")

private def digit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

/-- Parse integer magnitudes without host machine overflow. -/
def magnitude (s : String) : Result Nat := do
  let chars := s.toList
  let (base, chars) := match chars with
    | '0' :: 'x' :: rest => (16, rest)
    | _ => (10, chars)
  if chars.isEmpty || chars.head? == some '_' || chars.getLast? == some '_' then
    throw (.invalid "invalid integer literal")
  let mut n := 0
  let mut underscore := false
  for c in chars do
    if c == '_' then
      if underscore then throw (.invalid "consecutive integer separators")
      underscore := true
    else
      let some d := digit c | throw (.invalid "invalid integer digit")
      if d ≥ base then throw (.invalid "digit outside integer base")
      n := n * base + d
      underscore := false
  return n

def integer (width : Nat) (s : String) : Result Int := do
  let (negative, chars) := match s.toList with
    | '-' :: cs => (true, cs)
    | '+' :: cs => (false, cs)
    | cs => (false, cs)
  let n ← magnitude (String.ofList chars)
  if n ≥ 2^width || (negative && n > 2^(width-1)) then
    throw (.invalid "integer literal out of range")
  return if negative then -(Int.ofNat n) else Int.ofNat n

private def heapType : String → Result RefKind
  | "func" => .ok .func
  | "extern" => .ok .extern
  | _ => .error (.unsupported "heap type")

def constant : SExpr → Result Value
  | .list [.atom "i32.const", .atom s] => do return .i32 (BitVec.ofInt 32 (← integer 32 s))
  | .list [.atom "i64.const", .atom s] => do return .i64 (BitVec.ofInt 64 (← integer 64 s))
  | .list [.atom "f32.const", .atom s] => (floatLiteral .w32 s).mapError Error.invalid
  | .list [.atom "f64.const", .atom s] => (floatLiteral .w64 s).mapError Error.invalid
  | .list [.atom "ref.null", .atom kind] => do return .ref (.null (← heapType kind))
  | .list [.atom "ref.extern", .atom id] => do return .ref (.extern (← magnitude id))
  | _ => .error (.unsupported "script constant")

private def valType : SExpr → Result ValType
  | .atom "i32" => .ok .i32
  | .atom "i64" => .ok .i64
  | .atom "f32" => .ok .f32
  | .atom "f64" => .ok .f64
  | .atom "funcref" => .ok (.ref .func)
  | .atom "externref" => .ok (.ref .extern)
  | .list [.atom "ref", .atom "null", .atom kind] => do return .ref (← heapType kind)
  | _ => .error (.unsupported "value type")

private def index (names : List (String × Nat)) (s : String) : Result Nat :=
  if s.startsWith "$" then
    match names.lookup s with
    | some n => .ok n
    | none => .error (.invalid s!"unknown identifier {s}")
  else magnitude s

private def floatInstruction (op : String) : Option Instr := do
  let [type, suffix] := op.splitOn "." | none
  let integer ← match type with
    | "i32" => some NumWidth.w32 | "i64" => some .w64 | _ => none
  if suffix == "reinterpret_f32" && integer == .w32 then
    return .floatConvert .reinterpretI32
  if suffix == "reinterpret_f64" && integer == .w64 then
    return .floatConvert .reinterpretI64
  let parts := suffix.splitOn "_"
  let (saturating, source, sign) ← match parts with
    | ["trunc", source, sign] => some (false, source, sign)
    | ["trunc", "sat", source, sign] => some (true, source, sign)
    | _ => none
  let float ← match source with | "f32" => some NumWidth.w32 | "f64" => some .w64 | _ => none
  if sign != "s" && sign != "u" then none
  else return .floatConvert (.trunc integer float (sign == "s") saturating)

private def floatOperation (width : NumWidth) (suffix : String) : Result Instr := do
  match suffix with
  | "abs" => return .floatUnary width .abs | "neg" => return .floatUnary width .neg
  | "ceil" => return .floatUnary width .ceil | "floor" => return .floatUnary width .floor
  | "trunc" => return .floatUnary width .trunc | "nearest" => return .floatUnary width .nearest
  | "sqrt" => return .floatUnary width .sqrt
  | "add" => return .floatBinary width .add | "sub" => return .floatBinary width .sub
  | "mul" => return .floatBinary width .mul | "div" => return .floatBinary width .div
  | "min" => return .floatBinary width .min | "max" => return .floatBinary width .max
  | "copysign" => return .floatBinary width .copysign
  | "eq" => return .floatRel width .eq | "ne" => return .floatRel width .ne
  | "lt" => return .floatRel width .lt | "gt" => return .floatRel width .gt
  | "le" => return .floatRel width .le | "ge" => return .floatRel width .ge
  | "demote_f64" => if width == .w32 then return .floatConvert .demote
  | "promote_f32" => if width == .w64 then return .floatConvert .promote
  | "reinterpret_i32" => if width == .w32 then return .floatConvert .reinterpretF32
  | "reinterpret_i64" => if width == .w64 then return .floatConvert .reinterpretF64
  | _ => pure ()
  match suffix.splitOn "_" with
  | ["convert", source, sign] =>
    let integer ← match source with
      | "i32" => pure NumWidth.w32 | "i64" => pure .w64
      | _ => throw (.unsupported "float conversion")
    if sign == "s" || sign == "u" then
      return .floatConvert (.convert width integer (sign == "s"))
  | _ => pure ()
  throw (.unsupported s!"float instruction {suffix}")

private def operation (op : String) : Result Instr := do
  if let some instr := floatInstruction op then return instr
  match op with
  | "nop" => return .nop
  | "unreachable" => return .unreachable
  | "drop" => return .drop
  | "return" => return .return_
  | "select" => return .select none
  | "ref.is_null" => return .refIsNull
  | "i32.wrap_i64" => return .intConvert .wrapI64
  | "i64.extend_i32_s" => return .intConvert .extendI32S
  | "i64.extend_i32_u" => return .intConvert .extendI32U
  | "i32.extend8_s" => return .intConvert .extendI32_8S
  | "i32.extend16_s" => return .intConvert .extendI32_16S
  | "i64.extend8_s" => return .intConvert .extendI64_8S
  | "i64.extend16_s" => return .intConvert .extendI64_16S
  | "i64.extend32_s" => return .intConvert .extendI64_32S
  | _ => pure ()
  let parts := op.splitOn "."
  let [typeName, suffix] := parts | throw (.unsupported s!"instruction {op}")
  if typeName == "f32" then return ← floatOperation .w32 suffix
  if typeName == "f64" then return ← floatOperation .w64 suffix
  let t ← valType (.atom typeName)
  match suffix with
  | "add" => return .binop t .add
  | "sub" => return .binop t .sub
  | "mul" => return .binop t .mul
  | "eqz" => return .eqz t
  | "clz" => return .intUnary t .clz
  | "ctz" => return .intUnary t .ctz
  | "popcnt" => return .intUnary t .popcnt
  | "div_s" => return .intBinary t .divS
  | "div_u" => return .intBinary t .divU
  | "rem_s" => return .intBinary t .remS
  | "rem_u" => return .intBinary t .remU
  | "and" => return .intBinary t .and_
  | "or" => return .intBinary t .or_
  | "xor" => return .intBinary t .xor
  | "shl" => return .intBinary t .shl
  | "shr_s" => return .intBinary t .shrS
  | "shr_u" => return .intBinary t .shrU
  | "rotl" => return .intBinary t .rotl
  | "rotr" => return .intBinary t .rotr
  | "eq" => return .intRel t .eq
  | "ne" => return .intRel t .ne
  | "lt_s" => return .intRel t .ltS
  | "lt_u" => return .intRel t .ltU
  | "le_s" => return .intRel t .leS
  | "le_u" => return .intRel t .leU
  | "gt_s" => return .intRel t .gtS
  | "gt_u" => return .intRel t .gtU
  | "ge_s" => return .intRel t .geS
  | "ge_u" => return .intRel t .geU
  | _ => throw (.unsupported s!"instruction {op}")

private def immediate (locals funcs : List (String × Nat)) (op arg : String) :
    Result Instr := do
  match op with
  | "i32.const" => return .const (.i32 (BitVec.ofInt 32 (← integer 32 arg)))
  | "i64.const" => return .const (.i64 (BitVec.ofInt 64 (← integer 64 arg)))
  | "f32.const" => return .const (← (floatLiteral .w32 arg).mapError Error.invalid)
  | "f64.const" => return .const (← (floatLiteral .w64 arg).mapError Error.invalid)
  | "local.get" => return .localGet (← index locals arg)
  | "local.set" => return .localSet (← index locals arg)
  | "local.tee" => return .localTee (← index locals arg)
  | "call" => return .call (← index funcs arg)
  | "ref.func" => return .refFunc (← index funcs arg)
  | "ref.null" => return .refNull (← heapType arg)
  | _ => throw (.unsupported s!"instruction {op}")

private def hasImmediate (op : String) : Bool :=
  ["i32.const", "i64.const", "f32.const", "f64.const", "local.get", "local.set",
    "local.tee", "call",
    "ref.func", "ref.null"].contains op

abbrev ParseM := StateT (List FuncType) Result

private def depth (labels : List (Option String)) (s : String) : Result Nat :=
  if s.startsWith "$" then
    match (labels.zipIdx.find? (fun p => p.1 == some s)) with
    | some (_, n) => .ok n
    | none => .error (.invalid s!"unknown label {s}")
  else magnitude s

private def isIndex (s : String) : Bool :=
  s.startsWith "$" || (s.toList.head?.map Char.isDigit).getD false

private def closingLabel (label : Option String) (xs : List SExpr) : Result (List SExpr) := do
  match xs with
  | .atom id :: rest =>
    if id.startsWith "$" then
      if label == some id then return rest else throw (.invalid "closing label mismatch")
    else return xs
  | _ => return xs

private def bindings (xs : List SExpr) (offset : Nat) :
    Result (List ValType × List (String × Nat)) := do
  match xs with
  | .atom id :: rest =>
    if id.startsWith "$" then
      let [t] := rest | throw (.invalid "named binding must have one type")
      return ([← valType t], [(id, offset)])
    else return (← xs.mapM valType, [])
  | _ => return (← xs.mapM valType, [])

private def intern (ft : FuncType) : ParseM Nat := do
  let types ← get
  match types.zipIdx.find? (fun p => p.1 == ft) with
  | some (_, n) => return n
  | none =>
    set (types ++ [ft])
    return types.length

private def typeUse (typeNames : List (String × Nat)) (xs : List SExpr) :
    ParseM (FuncType × Nat × List (String × Nat) × List SExpr) := do
  let (ref, xs) ← match xs with
    | .list [.atom "type", .atom id] :: rest =>
      pure (some (← liftM (index typeNames id)), rest)
    | .list (.atom "type" :: _) :: _ => throw (.invalid "type use requires one index")
    | _ => pure (none, xs)
  let mut rest := xs
  let mut params := []
  let mut results := []
  let mut names := []
  let mut inlineSeen := false
  let mut resultSeen := false
  let mut scanning := true
  while scanning do
    match rest with
    | .list (.atom "param" :: ts) :: tail =>
      if resultSeen then throw (.invalid "parameter after result")
      let (ps, ns) ← liftM (bindings ts params.length)
      params := params ++ ps
      names := names ++ ns
      inlineSeen := true
      rest := tail
    | .list (.atom "result" :: ts) :: tail =>
      resultSeen := true
      inlineSeen := true
      results := results ++ (← liftM (ts.mapM valType))
      rest := tail
    | _ => scanning := false
  let ft : FuncType := ⟨params, results⟩
  let (ft, n) ← match ref with
    | some n => do
      match (← get)[n]? with
      | some declared =>
        if inlineSeen && ft != declared then throw (.invalid "inline type does not match type use")
        pure (declared, n)
      | none =>
        -- Inferred signatures must not accidentally bind an unknown source type index.
        -- Preserve an out-of-range index so executable validation reports the error.
        pure (ft, 2^32 + n)
    | none => pure (ft, ← intern ft)
  if (names.map Prod.fst).eraseDups.length != names.length then
    throw (.invalid "duplicate parameter identifier")
  return (ft, n, names, rest)

private def header (typeNames : List (String × Nat)) (xs : List SExpr) :
    ParseM (Option String × BlockType × List SExpr) := do
  let (label, xs) := match xs with
    | .atom id :: rest => if id.startsWith "$" then (some id, rest) else (none, xs)
    | _ => (none, xs)
  let explicit := match xs with
    | .list (.atom "type" :: _) :: _ => true
    | _ => false
  let previous ← get
  let (ft, n, names, rest) ← typeUse typeNames xs
  if !names.isEmpty then throw (.invalid "block parameters cannot have identifiers")
  let bt := if !explicit && ft.params.isEmpty && ft.results.length ≤ 1 then
    BlockType.val ft.results.head?
  else BlockType.typeIdx n
  if !explicit && ft.params.isEmpty && ft.results.length ≤ 1 then set previous
  return (label, bt, rest)

private def branchTable (labels : List (Option String)) (args : List SExpr) :
    Result (Instr × List SExpr) := do
  let indices := args.takeWhile fun | .atom s => isIndex s | _ => false
  let xs ← indices.mapM fun
    | .atom s => depth labels s
    | _ => throw (.invalid "branch table index")
  let some fallback := xs.getLast? | throw (.invalid "branch table requires a default")
  return (.brTable xs.dropLast fallback, args.drop indices.length)

private def loadOp : String → Option LoadOp
  | "i32.load" => some .i32 | "i64.load" => some .i64
  | "f32.load" => some .f32 | "f64.load" => some .f64
  | "i32.load8_s" => some .i32_8S | "i32.load8_u" => some .i32_8U
  | "i32.load16_s" => some .i32_16S | "i32.load16_u" => some .i32_16U
  | "i64.load8_s" => some .i64_8S | "i64.load8_u" => some .i64_8U
  | "i64.load16_s" => some .i64_16S | "i64.load16_u" => some .i64_16U
  | "i64.load32_s" => some .i64_32S | "i64.load32_u" => some .i64_32U
  | _ => none

private def storeOp : String → Option StoreOp
  | "i32.store" => some .i32 | "i64.store" => some .i64
  | "f32.store" => some .f32 | "f64.store" => some .f64
  | "i32.store8" => some .i32_8 | "i32.store16" => some .i32_16
  | "i64.store8" => some .i64_8 | "i64.store16" => some .i64_16
  | "i64.store32" => some .i64_32
  | _ => none

private def memoryIndex (names : List (String × Nat)) (args : List SExpr) :
    Result (Nat × List SExpr) := do
  match args with
  | .atom id :: rest =>
    if isIndex id then return (← index names id, rest)
  | _ => pure ()
  return (0, args)

private def memarg (bytes : Nat) (args : List SExpr) : Result (MemArg × List SExpr) := do
  let mut rest := args
  let mut offset := 0
  let mut align := bytes.log2
  if let .atom attr :: tail := rest then
    if attr.startsWith "offset=" then
      offset ← magnitude (attr.drop 7).toString
      if offset ≥ 2 ^ 64 then throw (.invalid "offset exceeds u64")
      rest := tail
  if let .atom attr :: tail := rest then
    if attr.startsWith "align=" then
      let n ← magnitude (attr.drop 6).toString
      if n ≥ 2 ^ 64 then throw (.invalid "alignment exceeds u64")
      if n == 0 || 2 ^ n.log2 != n then throw (.invalid "alignment must be a power of two")
      align := n.log2
      rest := tail
  return (⟨align, offset⟩, rest)

private def scalar (locals funcs : List (String × Nat)) (labels : List (Option String))
    (typeNames tableNames elemNames globalNames memNames dataNames : List (String × Nat))
    (op : String) (args : List SExpr) : ParseM (Instr × List SExpr) := do
  if let some load := loadOp op then
    let (memory, args) ← liftM (memoryIndex memNames args)
    let (arg, rest) ← liftM (memarg load.bytes args)
    return (.load load memory arg, rest)
  if let some store := storeOp op then
    let (memory, args) ← liftM (memoryIndex memNames args)
    let (arg, rest) ← liftM (memarg store.bytes args)
    return (.store store memory arg, rest)
  if ["memory.size", "memory.grow", "memory.fill"].contains op then
    let (memory, rest) ← liftM (memoryIndex memNames args)
    return (if op == "memory.size" then .memorySize memory
      else if op == "memory.grow" then .memoryGrow memory else .memoryFill memory, rest)
  if op == "memory.copy" then
    match args with
    | .atom dst :: .atom src :: rest =>
      if isIndex dst && isIndex src then
        return (.memoryCopy (← liftM (index memNames dst)) (← liftM (index memNames src)), rest)
      else if isIndex dst then throw (.invalid "memory.copy requires two memory indices")
    | .atom dst :: _ =>
      if isIndex dst then throw (.invalid "memory.copy requires two memory indices")
    | _ => pure ()
    return (.memoryCopy 0 0, args)
  if op == "memory.init" then
    let .atom first :: rest := args | throw (.invalid "memory.init requires a data index")
    match rest with
    | .atom second :: tail =>
      if isIndex second then
        return (.memoryInit (← liftM (index memNames first))
          (← liftM (index dataNames second)), tail)
    | _ => pure ()
    return (.memoryInit 0 (← liftM (index dataNames first)), rest)
  if op == "data.drop" then
    let .atom id :: rest := args | throw (.invalid "data.drop requires a data index")
    return (.dataDrop (← liftM (index dataNames id)), rest)
  if op == "global.get" || op == "global.set" then
    let .atom id :: rest := args | throw (.invalid s!"missing immediate for {op}")
    let idx ← liftM (index globalNames id)
    return (if op == "global.get" then .globalGet idx else .globalSet idx, rest)
  if op == "call_indirect" then
    let (table, args) ← match args with
      | .atom id :: rest =>
        if isIndex id then pure (← liftM (index tableNames id), rest) else pure (0, args)
      | _ => pure (0, args)
    let (_, type, names, rest) ← typeUse typeNames args
    if !names.isEmpty then throw (.invalid "indirect call parameters cannot have identifiers")
    return (.callIndirect table type, rest)
  if ["table.get", "table.set", "table.size", "table.grow", "table.fill"].contains op then
    let (table, rest) ← match args with
      | .atom id :: rest =>
        if isIndex id then pure (← liftM (index tableNames id), rest) else pure (0, args)
      | _ => pure (0, args)
    let instr := if op == "table.get" then Instr.tableGet table
      else if op == "table.set" then Instr.tableSet table
      else if op == "table.grow" then Instr.tableGrow table
      else if op == "table.fill" then Instr.tableFill table else Instr.tableSize table
    return (instr, rest)
  if op == "table.copy" then
    match args with
    | .atom dst :: .atom src :: rest =>
      if isIndex dst && isIndex src then
        return (.tableCopy (← liftM (index tableNames dst))
          (← liftM (index tableNames src)), rest)
      else if isIndex dst then throw (.invalid "table.copy requires two table indices")
    | .atom dst :: _ =>
      if isIndex dst then throw (.invalid "table.copy requires two table indices")
    | _ => pure ()
    return (.tableCopy 0 0, args)
  if op == "table.init" then
    let .atom first :: rest := args | throw (.invalid "table.init requires an element index")
    if !isIndex first then throw (.invalid "table.init requires an element index")
    match rest with
    | .atom second :: tail =>
      if isIndex second then
        return (.tableInit (← liftM (index tableNames first))
          (← liftM (index elemNames second)), tail)
    | _ => pure ()
    return (.tableInit 0 (← liftM (index elemNames first)), rest)
  if op == "elem.drop" then
    let .atom id :: rest := args | throw (.invalid "elem.drop requires an element index")
    return (.elemDrop (← liftM (index elemNames id)), rest)
  if op == "br_table" then return ← liftM (branchTable labels args)
  if op == "br" || op == "br_if" then
    let .atom arg :: rest := args | throw (.invalid "branch requires a label")
    let n ← liftM (depth labels arg)
    return (if op == "br" then .br n else .brIf n, rest)
  if hasImmediate op then
    let .atom arg :: rest := args | throw (.invalid s!"missing immediate for {op}")
    return (← liftM (immediate locals funcs op arg), rest)
  if op == "select" then
    match args with
    | .list (.atom "result" :: _) :: _ =>
      let mut rest := args
      let mut types := []
      while true do
        match rest with
        | .list (.atom "result" :: ts) :: tail =>
          types := types ++ (← liftM (ts.mapM valType))
          rest := tail
        | _ => break
      return (.select (some types), rest)
    | _ => pure ()
  return (← liftM (operation op), args)

mutual
  private partial def sequence (locals funcs : List (String × Nat))
      (labels : List (Option String))
      (typeNames tableNames elemNames globalNames memNames dataNames : List (String × Nat))
      (stop : Bool) (xs : List SExpr) :
      ParseM (List Instr × List SExpr × Option String) := do
    match xs with
    | [] => return ([], [], none)
    | .atom op :: rest =>
      if op == "end" || op == "else" then
        if stop then return ([], rest, some op)
        else throw (.invalid s!"unexpected {op}")
      if op == "block" || op == "loop" || op == "if" then
        let (label, bt, rest) ← header typeNames rest
        let (yes, rest, term) ←
          sequence locals funcs (label :: labels)
              typeNames tableNames elemNames globalNames memNames dataNames true rest
        let rest ← liftM (closingLabel label rest)
        let (no, rest) ← if op == "if" && term == some "else" then do
          let (no, rest, term) ←
            sequence locals funcs (label :: labels)
              typeNames tableNames elemNames globalNames memNames dataNames true rest
          if term != some "end" then throw (.invalid "if requires end")
          pure (no, ← liftM (closingLabel label rest))
        else do
          if term != some "end" then throw (.invalid s!"{op} requires end")
          pure ([], rest)
        let instr := if op == "block" then Instr.block bt yes
          else if op == "loop" then Instr.loop bt yes else Instr.if_ bt yes no
        let (tail, rest, term) ←
          sequence locals funcs labels
            typeNames tableNames elemNames globalNames memNames dataNames stop rest
        return (instr :: tail, rest, term)
      let (instr, rest) ←
        scalar locals funcs labels
          typeNames tableNames elemNames globalNames memNames dataNames op rest
      let (tail, rest, term) ←
        sequence locals funcs labels
          typeNames tableNames elemNames globalNames memNames dataNames stop rest
      return (instr :: tail, rest, term)
    | .list (.atom op :: args) :: rest =>
      let code ←
        folded locals funcs labels
          typeNames tableNames elemNames globalNames memNames dataNames op args
      let (tail, rest, term) ←
        sequence locals funcs labels
          typeNames tableNames elemNames globalNames memNames dataNames stop rest
      return (code ++ tail, rest, term)
    | _ => throw (.invalid "instruction syntax")
  private partial def folded (locals funcs : List (String × Nat))
      (labels : List (Option String))
      (typeNames tableNames elemNames globalNames memNames dataNames : List (String × Nat))
      (op : String) (args : List SExpr) :
      ParseM (List Instr) := do
    if ["type", "param", "result", "local", "export"].contains op then
      throw (.invalid s!"misplaced {op} declaration")
    let all := fun ls xs => do
      let (code, _, _) ←
        sequence locals funcs ls
          typeNames tableNames elemNames globalNames memNames dataNames false xs
      pure code
    if op == "block" || op == "loop" || op == "if" then
      let (label, bt, args) ← header typeNames args
      if op == "block" || op == "loop" then
        let code ← all (label :: labels) args
        return [if op == "block" then .block bt code else .loop bt code]
      let conditions := args.takeWhile fun
        | .list (.atom "then" :: _) => false
        | _ => true
      let .list (.atom "then" :: yes) :: arms := args.drop conditions.length |
        throw (.invalid "folded if requires then")
      let no ← match arms with
        | [] => pure []
        | [.list (.atom "else" :: no)] => pure no
        | _ => throw (.invalid "folded if arm syntax")
      let condition ← all labels conditions
      let yes ← all (label :: labels) yes
      let no ← all (label :: labels) no
      return condition ++ [.if_ bt yes no]
    let (instr, args) ←
      scalar locals funcs labels
        typeNames tableNames elemNames globalNames memNames dataNames op args
    return (← all labels args) ++ [instr]
end

private def function (fields : List SExpr)
    (funcs typeNames tableNames elemNames globalNames memNames dataNames : List (String × Nat))
    (idx : Nat) : ParseM (Func × List Export) := do
  let fields := match fields with
    | .atom id :: rest => if id.startsWith "$" then rest else fields
    | _ => fields
  let mut rest := fields
  let mut exports := []
  while true do
    match rest with
    | .list [.atom "export", .string bytes] :: tail =>
      exports := exports ++ [{name := ← liftM (name bytes), desc := .func idx}]
      rest := tail
    | _ => break
  let (ft, typeIndex, paramNames, rest') ← typeUse typeNames rest
  rest := rest'
  let mut locals := []
  let mut names := paramNames
  while true do
    match rest with
    | .list (.atom "local" :: xs) :: tail =>
      let (ts, ns) ← liftM (bindings xs (ft.params.length + locals.length))
      locals := locals ++ ts
      names := names ++ ns
      rest := tail
    | _ => break
  if (names.map Prod.fst).eraseDups.length != names.length then
    throw (.invalid "duplicate local identifier")
  let (code, _, _) ←
    sequence names funcs [none]
      typeNames tableNames elemNames globalNames memNames dataNames false rest
  return (⟨typeIndex, locals, code⟩, exports)

private def declaration (xs : List SExpr) : Result (Option String × FuncType) := do
  let (id, xs) := match xs with
    | .atom id :: rest => if id.startsWith "$" then (some id, rest) else (none, xs)
    | _ => (none, xs)
  let [.list (.atom "func" :: fields)] := xs |
    throw (.unsupported "nonfunction type declaration")
  let mut params := []
  let mut results := []
  let mut names := []
  let mut resultSeen := false
  for field in fields do
    match field with
    | .list (.atom "param" :: xs) =>
      if resultSeen then throw (.invalid "parameter after result")
      let (ts, ns) ← bindings xs params.length
      params := params ++ ts
      names := names ++ ns
    | .list (.atom "result" :: xs) =>
      resultSeen := true
      results := results ++ (← xs.mapM valType)
    | _ => throw (.invalid "function type syntax")
  if (names.map Prod.fst).eraseDups.length != names.length then
    throw (.invalid "duplicate parameter identifier")
  return (id, ⟨params, results⟩)

private def refKind : SExpr → Result RefKind
  | .atom "funcref" => .ok .func
  | .atom "externref" => .ok .extern
  | .list [.atom "ref", .atom "null", .atom "func"] => .ok .func
  | .list [.atom "ref", .atom "null", .atom "extern"] => .ok .extern
  | _ => .error (.unsupported "table reference type")

private def elemExpressions (funcs globals : List (String × Nat)) (xs : List SExpr) :
    Result (List (List Instr)) :=
  xs.mapM fun
    | .atom id => do return [.refFunc (← index funcs id)]
    | .list [.atom "ref.func", .atom id] => do return [.refFunc (← index funcs id)]
    | .list [.atom "ref.null", .atom kind] => do return [.refNull (← heapType kind)]
    | .list [.atom "global.get", .atom id] => do return [.globalGet (← index globals id)]
    | .list [.atom "item", .list [.atom "ref.func", .atom id]] =>
      do return [.refFunc (← index funcs id)]
    | .list [.atom "item", .list [.atom "ref.null", .atom kind]] =>
      do return [.refNull (← heapType kind)]
    | .list [.atom "item", .list [.atom "global.get", .atom id]] =>
      do return [.globalGet (← index globals id)]
    | _ => throw (.unsupported "element initializer")

private def element (fields : List SExpr)
    (funcs typeNames tableNames elemNames globalNames memNames dataNames : List (String × Nat)) :
    ParseM Elem := do
  let mut rest := match fields with
    | .atom id :: rest => if id.startsWith "$" then rest else fields
    | _ => fields
  let mut mode := ElemMode.passive
  let mut table := 0
  let mut explicitTable := false
  match rest with
  | .atom "declare" :: tail => mode := .declarative; rest := tail
  | .list [.atom "table", .atom id] :: tail =>
    explicitTable := true
    table ← liftM (index tableNames id)
    rest := tail
  | _ => pure ()
  let offset ← match rest with
    | .list (.atom "offset" :: expressions) :: tail => pure (some (expressions, tail))
    | expression@(.list _) :: tail => pure (some ([expression], tail))
    | _ => pure none
  if let some (expressions, tail) := offset then
    if mode == .declarative then throw (.invalid "declarative element has offset")
    let (code, _, _) ← sequence [] funcs [] typeNames tableNames elemNames globalNames
      memNames dataNames false expressions
    mode := .active table code
    rest := tail
  if explicitTable then
    match mode with
    | .active _ _ => pure ()
    | _ => throw (.invalid "active element requires offset")
  let mut kind := Types.HeapType.func
  match rest with
  | .atom "externref" :: tail => kind := .extern; rest := tail
  | .list [.atom "ref", .atom "null", .atom heap] :: tail =>
    kind ← liftM (heapType heap)
    rest := tail
  | .list (.atom "ref" :: _) :: _ => throw (.unsupported "element reference type")
  | .atom "func" :: tail | .atom "funcref" :: tail => rest := tail
  | _ => pure ()
  return { kind, init := ← liftM (elemExpressions funcs globalNames rest), mode }

private def table (fields : List SExpr) (funcs globals : List (String × Nat)) (idx : Nat) :
    Result (Table × List Export × List Elem) := do
  let mut rest := match fields with
    | .atom id :: rest => if id.startsWith "$" then rest else fields
    | _ => fields
  let mut exports := []
  while true do
    match rest with
    | .list [.atom "export", .string bytes] :: tail =>
      exports := exports ++ [{name := ← name bytes, desc := .table idx}]
      rest := tail
    | _ => break
  let (addrType, rest') := match rest with
    | .atom "i64" :: tail => (ValType.i64, tail)
    | .atom "i32" :: tail => (ValType.i32, tail)
    | _ => (ValType.i32, rest)
  rest := rest'
  match rest with
  | [kind, .list (.atom "elem" :: xs)] =>
    let kind ← refKind kind
    if kind != Types.HeapType.func then throw (Error.unsupported "nonfunction inline elements")
    let init ← elemExpressions funcs globals xs
    let type : TableType := {addrType, min := init.length, max := some init.length, kind}
    let offset : List Instr := [.const (Value.ofNat addrType 0)]
    return (⟨type, [.refNull kind]⟩, exports, [{init, mode := .active idx offset}])
  | .atom min :: tail =>
    let min ← magnitude min
    let (max, tail) ← match tail with
      | .atom max :: kind :: remaining =>
        if isIndex max && !max.startsWith "$" then pure (some (← magnitude max), kind :: remaining)
        else pure (none, tail)
      | _ => pure (none, tail)
    let kind :: init := tail | throw (Error.unsupported "table declaration syntax")
    let kind ← refKind kind
    let type : TableType := {addrType, min, max, kind}
    let code : List Instr ← if init.isEmpty then pure [Instr.refNull kind] else do
      let [code] ← elemExpressions funcs globals init |
        throw (Error.invalid "table requires one initializer expression")
      pure code
    return (⟨type, code⟩, exports, [])
  | _ => throw (Error.unsupported "table declaration syntax")

private def dataBytes (xs : List SExpr) : Result (Array Byte) := do
  let mut bytes := #[]
  for x in xs do
    let .string part := x | throw (.unsupported "data string syntax")
    bytes := bytes ++ part.data.map (fun b => BitVec.ofNat 8 b.toNat)
  return bytes

private def memory (fields : List SExpr) (idx : Nat) :
    Result (MemoryType × List Export × List Data) := do
  let mut rest := match fields with
    | .atom id :: rest => if id.startsWith "$" then rest else fields
    | _ => fields
  let mut exports := []
  while true do
    match rest with
    | .list [.atom "export", .string bytes] :: tail =>
      exports := exports ++ [{name := ← name bytes, desc := .memory idx}]
      rest := tail
    | _ => break
  let (addrType, tail) := match rest with
    | .atom "i64" :: tail => (ValType.i64, tail)
    | .atom "i32" :: tail => (ValType.i32, tail)
    | _ => (ValType.i32, rest)
  match tail with
  | [.list (.atom "data" :: xs)] =>
    let bytes ← dataBytes xs
    let pages := (bytes.size + 65535) / 65536
    return (⟨addrType, pages, some pages⟩, exports,
      [{bytes, mode := .active idx [.const (Value.ofNat addrType 0)]}])
  | [.atom min] => return (⟨addrType, ← magnitude min, none⟩, exports, [])
  | [.atom min, .atom max] =>
    if max == "shared" then throw (Error.unsupported "shared memory")
    return (⟨addrType, ← magnitude min, some (← magnitude max)⟩, exports, [])
  | _ => throw (Error.unsupported "memory declaration syntax")

private def dataSegment (fields : List SExpr)
    (funcs typeNames tableNames elemNames globalNames memNames dataNames : List (String × Nat)) :
    ParseM Data := do
  let mut rest := match fields with
    | .atom id :: rest => if id.startsWith "$" then rest else fields
    | _ => fields
  let mut memory := 0
  let mut explicitMemory := false
  if let .list [.atom "memory", .atom id] :: tail := rest then
    memory ← liftM (index memNames id)
    explicitMemory := true
    rest := tail
  let mut mode := DataMode.passive
  let offset := match rest with
    | .list (.atom "offset" :: expressions) :: tail => some (expressions, tail)
    | (expr@(.list (.atom _ :: _))) :: tail => some ([expr], tail)
    | _ => none
  if let some (expressions, tail) := offset then
    let (code, _, _) ← sequence [] funcs []
      typeNames tableNames elemNames globalNames memNames dataNames false expressions
    mode := .active memory code
    rest := tail
  else if explicitMemory then throw (Error.invalid "active data requires offset")
  return {bytes := ← liftM (dataBytes rest), mode}

private def globalType : SExpr → Result GlobalType
  | .list [.atom "mut", type] => do return ⟨.var, ← valType type⟩
  | .list (.atom "mut" :: _) => throw (.invalid "mutable global type syntax")
  | type => do return ⟨.const, ← valType type⟩

private def importedGlobal (fields : List SExpr) : Result GlobalType := do
  let fields := match fields with
    | .atom id :: rest => if id.startsWith "$" then rest else fields
    | _ => fields
  let [type] := fields | throw (.invalid "imported global requires a type and no initializer")
  globalType type

private def global (fields : List SExpr)
    (funcs typeNames tableNames elemNames globalNames memNames dataNames : List (String × Nat))
    (idx : Nat) : ParseM (Global × List Export) := do
  let fields := match fields with
    | .atom id :: rest => if id.startsWith "$" then rest else fields
    | _ => fields
  let mut rest := fields
  let mut exports := []
  while true do
    match rest with
    | .list [.atom "export", .string bytes] :: tail =>
      exports := exports ++ [{name := ← liftM (name bytes), desc := .global idx}]
      rest := tail
    | _ => break
  let type :: init := rest | throw (.invalid "global requires a type")
  let type ← liftM (globalType type)
  let (code, _, _) ←
    sequence [] funcs [] typeNames tableNames elemNames globalNames memNames dataNames false init
  return (⟨type, code⟩, exports)

private def expandInlineImport (field : SExpr) (funcIndex tableIndex globalIndex memIndex : Nat) :
    Result (List SExpr) := do
  let .list (.atom kind :: xs) := field | return [field]
  if kind != "func" && kind != "table" && kind != "global" && kind != "memory" then return [field]
  let (id, xs) := match xs with
    | .atom id :: rest => if id.startsWith "$" then ([SExpr.atom id], rest) else ([], xs)
    | _ => ([], xs)
  let mut rest := xs
  let mut exports := []
  while true do
    match rest with
    | .list [.atom "export", .string bytes] :: tail =>
      exports := exports ++ [bytes]
      rest := tail
    | _ => break
  match rest with
  | .list [.atom "import", .string owner, .string name] :: tail =>
    let idx := if kind == "func" then funcIndex
      else if kind == "table" then tableIndex
      else if kind == "memory" then memIndex else globalIndex
    let imported := SExpr.list [.atom "import", .string owner, .string name,
      .list (.atom kind :: (id ++ tail))]
    let aliases := exports.map fun bytes =>
      SExpr.list [.atom "export", .string bytes, .list [.atom kind, .atom (toString idx)]]
    return imported :: aliases
  | .list (.atom "import" :: _) :: _ => throw (.invalid "inline import syntax")
  | _ => return [field]

private def entityFields (kind : String) : SExpr → Option (List SExpr × Bool)
  | .list (.atom tag :: xs) => if tag == kind then some (xs, false) else
      match tag, xs with
      | "import", [.string _, .string _, .list (.atom tag :: fields)] =>
        if tag == kind then some (fields, true) else none
      | _, _ => none
  | _ => none

private def expandImports (fields : List SExpr) : Result (List SExpr) := do
  let mut expanded := []
  let mut funcs := 0
  let mut tables := 0
  let mut globals := 0
  let mut memories := 0
  let mut defined := false
  for field in fields do
    let next ← expandInlineImport field funcs tables globals memories
    for field in next do
      match field with
      | .list (.atom "import" :: _) =>
        if defined then throw (.invalid "imports must precede definitions")
      | .list (.atom "tag" :: _) => throw (.unsupported "tags")
      | .list (.atom tag :: _) =>
        if ["func", "table", "global", "memory", "tag"].contains tag then defined := true
      | _ => pure ()
      if (entityFields "func" field).isSome then funcs := funcs + 1
      if (entityFields "table" field).isSome then tables := tables + 1
      if (entityFields "global" field).isSome then globals := globals + 1
      if (entityFields "memory" field).isSome then memories := memories + 1
      expanded := expanded ++ [field]
  return expanded

private def importedFunction (fields : List SExpr) (typeNames : List (String × Nat)) :
    ParseM Nat := do
  let fields := match fields with
    | .atom id :: rest => if id.startsWith "$" then rest else fields
    | _ => fields
  let (_, typeIdx, _, rest) ← typeUse typeNames fields
  if !rest.isEmpty then throw (.invalid "imported function cannot have locals or a body")
  return typeIdx

/-- First module elaborator: integer functions and function exports. No validation is implied. -/
def module (expr : SExpr) : Result Module := do
  let .list (.atom "module" :: fields) := expr | throw (.invalid "expected module")
  let fields := match fields with
    | .atom id :: rest => if id.startsWith "$" then rest else fields
    | _ => fields
  let fields ← expandImports fields
  let mut names := []
  let mut count := 0
  for field in fields do
    if let some (xs, _) := entityFields "func" field then
      if let .atom id :: _ := xs then
        if id.startsWith "$" then names := names ++ [(id, count)]
      count := count + 1
  if (names.map Prod.fst).eraseDups.length != names.length then
    throw (.invalid "duplicate function identifier")
  let mut globalNames := []
  let mut globalCount := 0
  for field in fields do
    if let some (xs, _) := entityFields "global" field then
      if let .atom id :: _ := xs then
        if id.startsWith "$" then globalNames := globalNames ++ [(id, globalCount)]
      globalCount := globalCount + 1
  if (globalNames.map Prod.fst).eraseDups.length != globalNames.length then
    throw (.invalid "duplicate global identifier")
  let mut tableNames := []
  let mut tableCount := 0
  let mut elemNames := []
  let mut elemCount := 0
  for field in fields do
    if let some (xs, imported) := entityFields "table" field then
      if let .atom id :: _ := xs then
        if id.startsWith "$" then tableNames := tableNames ++ [(id, tableCount)]
      let (_, _, implicitElems) ← table xs names globalNames tableCount
      if imported && !implicitElems.isEmpty then
        throw (.invalid "imported table cannot have inline elements")
      elemCount := elemCount + implicitElems.length
      tableCount := tableCount + 1
    if let .list (.atom "elem" :: xs) := field then
      if let .atom id :: _ := xs then
        if id.startsWith "$" then elemNames := elemNames ++ [(id, elemCount)]
      elemCount := elemCount + 1
  if (tableNames.map Prod.fst).eraseDups.length != tableNames.length then
    throw (.invalid "duplicate table identifier")
  if (elemNames.map Prod.fst).eraseDups.length != elemNames.length then
    throw (.invalid "duplicate element identifier")
  let mut memNames := []
  let mut memCount := 0
  let mut dataNames := []
  let mut dataCount := 0
  for field in fields do
    if let some (xs, imported) := entityFields "memory" field then
      if let .atom id :: _ := xs then
        if id.startsWith "$" then memNames := memNames ++ [(id, memCount)]
      let (_, _, implicitData) ← memory xs memCount
      if imported && !implicitData.isEmpty then
        throw (.invalid "imported memory cannot have inline data")
      dataCount := dataCount + implicitData.length
      memCount := memCount + 1
    if let .list (.atom "data" :: xs) := field then
      if let .atom id :: _ := xs then
        if id.startsWith "$" then dataNames := dataNames ++ [(id, dataCount)]
      dataCount := dataCount + 1
  if (memNames.map Prod.fst).eraseDups.length != memNames.length then
    throw (.invalid "duplicate memory identifier")
  if (dataNames.map Prod.fst).eraseDups.length != dataNames.length then
    throw (.invalid "duplicate data identifier")
  -- Collect explicit types first so inferred signatures cannot shift their indices.
  let mut typeNames := []
  let mut types := []
  for field in fields do
    if let .list (.atom "type" :: xs) := field then
      let (id, ft) ← declaration xs
      if let some id := id then typeNames := typeNames ++ [(id, types.length)]
      types := types ++ [ft]
  if (typeNames.map Prod.fst).eraseDups.length != typeNames.length then
    throw (.invalid "duplicate type identifier")
  let mut result : Module := {types := types}
  for field in fields do
    match field with
    | .list [.atom "import", .string owner, .string bytes, .list (.atom kind :: fields)] =>
      let moduleName ← name owner
      let importName ← name bytes
      let (desc, updatedTypes) ← match kind with
        | "func" => do
          let (idx, importedTypes) ← (importedFunction fields typeNames).run result.types
          pure (ImportDesc.func idx, importedTypes)
        | "memory" => do
          let (type, es, datas) ← memory fields result.importedMemories.length
          if !es.isEmpty || !datas.isEmpty then
            throw (.invalid "imported memory cannot have exports or inline data")
          pure (ImportDesc.memory type, result.types)
        | "global" => do
          pure (ImportDesc.global (← importedGlobal fields), result.types)
        | "table" => do
          let (t, es, elems) ← table fields names globalNames result.importedTables.length
          if !es.isEmpty || !elems.isEmpty then
            throw (.invalid "imported table cannot have exports or inline elements")
          pure (ImportDesc.table t.type, result.types)
        | _ => throw (.unsupported s!"import kind {kind}")
      result := {result with
        types := updatedTypes
        imports := result.imports ++ [⟨moduleName, importName, desc⟩]}
    | .list (.atom "import" :: _) => throw (.invalid "import declaration syntax")
    | .list (.atom "func" :: fields) =>
      let ((f, es), updatedTypes) ←
        (function fields names typeNames tableNames elemNames globalNames memNames dataNames
          (result.importedFuncIndices.length + result.funcs.length)).run result.types
      result := { result with
        types := updatedTypes
        funcs := result.funcs ++ [f]
        exports := result.exports ++ es }
    | .list (.atom "global" :: fields) =>
      let ((g, es), updatedTypes) ←
        (global fields names typeNames tableNames elemNames globalNames memNames dataNames
          (result.importedGlobals.length + result.globals.length)).run result.types
      result := {result with
        types := updatedTypes
        globals := result.globals ++ [g]
        exports := result.exports ++ es}
    | .list (.atom "type" :: _) => pure ()
    | .list (.atom "table" :: fields) =>
      let (t, es, elems) ←
        table fields names globalNames (result.importedTables.length + result.tables.length)
      result := {result with
        tables := result.tables ++ [t]
        exports := result.exports ++ es
        elems := result.elems ++ elems}
    | .list (.atom "memory" :: fields) =>
      let (type, es, datas) ←
        memory fields (result.importedMemories.length + result.mems.length)
      result := {result with
        mems := result.mems ++ [type]
        exports := result.exports ++ es
        datas := result.datas ++ datas}
    | .list (.atom "data" :: fields) =>
      let (data, updatedTypes) ← (dataSegment fields names
        typeNames tableNames elemNames globalNames memNames dataNames).run result.types
      result := {result with datas := result.datas ++ [data], types := updatedTypes}
    | .list [.atom "export", .string bytes, .list [.atom "memory", .atom id]] =>
      result := {result with exports := result.exports ++
        [{name := ← name bytes, desc := .memory (← index memNames id)}]}
    | .list [.atom "start", .atom id] =>
      if result.start.isSome then throw (.invalid "duplicate start")
      result := {result with start := some (← index names id)}
    | .list (.atom "elem" :: fields) =>
      let (elem, updatedTypes) ← (element fields names typeNames tableNames elemNames globalNames
        memNames dataNames).run result.types
      result := {result with elems := result.elems ++ [elem], types := updatedTypes}
    | .list [.atom "export", .string bytes, .list [.atom "table", .atom id]] =>
      result := {result with exports := result.exports ++
        [{name := ← name bytes, desc := .table (← index tableNames id)}]}
    | .list [.atom "export", .string bytes, .list [.atom "global", .atom id]] =>
      result := {result with exports := result.exports ++
        [{name := ← name bytes, desc := .global (← index globalNames id)}]}
    | .list [.atom "export", .string bytes, .list [.atom "func", .atom id]] =>
      result := {result with exports := result.exports ++
        [{name := ← name bytes, desc := .func (← index names id)}]}
    | _ => throw (.unsupported "module field")
  return result

end Wasm.Text
