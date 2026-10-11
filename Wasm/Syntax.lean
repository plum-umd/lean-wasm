import Wasm.TypeEquality
import Wasm.VectorOpcode

/-!
Integer, parametric, and structured-control fragment of WebAssembly 3.0 abstract syntax.
Source: https://webassembly.github.io/spec/core/syntax/instructions.html
Unsupported instructions are deliberately absent from this fragment.
-/

namespace Wasm

/-- Heap types in the function/external hierarchies. -/
abbrev RefKind := Types.HeapType

structure FuncAddr where
  index : Nat
  deriving DecidableEq, Repr

structure StructAddr where
  index : Nat
  deriving DecidableEq, Repr

structure ArrayAddr where
  index : Nat
  deriving DecidableEq, Repr

structure TagAddr where
  index : Nat
  deriving DecidableEq, Repr

structure ExnAddr where
  index : Nat
  deriving DecidableEq, Repr

inductive Catch where
  | tag (index depth : Nat) (reference : Bool)
  | all (depth : Nat) (reference : Bool)
  deriving DecidableEq, Repr

inductive RefValue where
  | null (kind : RefKind)
  | func (address : FuncAddr)
  | exn (address : ExnAddr)
  | extern (identifier : Nat)
  | struct_ (address : StructAddr)
  | array (address : ArrayAddr)
  | i31 (bits : BitVec 31)
  | host (identifier : Nat)
  | external (reference : RefValue)
  deriving DecidableEq, Repr

def RefValue.kind : RefValue → RefKind
  | .null kind => kind
  | .func _ => .func
  | .exn _ => .exn
  | .extern _ | .external _ => .extern
  | .struct_ _ => .struct_
  | .array _ => .array
  | .i31 _ => .i31
  | .host _ => .any

inductive ValType where
  | i32 | i64 | f32 | f64 | v128
  | ref (kind : RefKind)
  | refNonNull (heap : RefKind)
  deriving DecidableEq, Repr

/-- Integer constants are bit patterns, with signedness chosen by the instruction. -/
inductive Value where
  | i32 (bits : BitVec 32)
  | i64 (bits : BitVec 64)
  | f32 (bits : BitVec 32)
  | f64 (bits : BitVec 64)
  | v128 (bits : BitVec 128)
  | ref (reference : RefValue)
  deriving DecidableEq, Repr

/-- Erased type for the integer typing layer. Reference typing uses `Value.type? store`. -/
def Value.type : Value → ValType
  | .i32 _ => .i32
  | .i64 _ => .i64
  | .f32 _ => .f32
  | .f64 _ => .f64
  | .v128 _ => .v128
  | .ref r => .ref r.kind

def ValType.IsInteger : ValType → Prop
  | .i32 | .i64 => True
  | _ => False

instance (t : ValType) : Decidable t.IsInteger := by cases t <;> unfold ValType.IsInteger <;>
  infer_instance

def ValType.IsNumber : ValType → Prop
  | .i32 | .i64 | .f32 | .f64 | .v128 => True
  | _ => False

instance (t : ValType) : Decidable t.IsNumber := by
  cases t <;> unfold ValType.IsNumber <;> infer_instance

inductive NumWidth where
  | w32 | w64
  deriving DecidableEq, Repr

def NumWidth.intType : NumWidth → ValType
  | .w32 => .i32 | .w64 => .i64

def NumWidth.floatType : NumWidth → ValType
  | .w32 => .f32 | .w64 => .f64

inductive FloatUnaryOp where
  | abs | neg | ceil | floor | trunc | nearest | sqrt
  deriving DecidableEq, Repr

inductive FloatBinaryOp where
  | add | sub | mul | div | min | max | copysign
  deriving DecidableEq, Repr

inductive FloatRelOp where
  | eq | ne | lt | gt | le | ge
  deriving DecidableEq, Repr

inductive FloatConversion where
  | trunc (integer float : NumWidth) (signed saturating : Bool)
  | convert (float integer : NumWidth) (signed : Bool)
  | demote | promote
  | reinterpretI32 | reinterpretI64 | reinterpretF32 | reinterpretF64
  deriving DecidableEq, Repr

def FloatConversion.inputType : FloatConversion → ValType
  | .trunc _ width _ _ => width.floatType
  | .convert _ width _ => width.intType
  | .demote | .reinterpretI64 => .f64
  | .promote | .reinterpretI32 => .f32
  | .reinterpretF32 => .i32 | .reinterpretF64 => .i64

def FloatConversion.outputType : FloatConversion → ValType
  | .trunc width _ _ _ => width.intType
  | .convert width _ _ => width.floatType
  | .demote | .reinterpretF32 => .f32
  | .promote | .reinterpretF64 => .f64
  | .reinterpretI32 => .i32 | .reinterpretI64 => .i64

inductive IntBinOp where
  | add | sub | mul
  deriving DecidableEq, Repr

inductive IntUnaryOp where
  | clz | ctz | popcnt
  deriving DecidableEq, Repr

/-- Integer binary operations beyond the existing modular add/sub/mul family. -/
inductive IntBinaryOp where
  | divS | divU | remS | remU
  | and_ | or_ | xor | shl | shrS | shrU | rotl | rotr
  deriving DecidableEq, Repr

inductive IntRelOp where
  | eq | ne | ltS | ltU | gtS | gtU | leS | leU | geS | geU
  deriving DecidableEq, Repr

/-- Integer-only conversions; constructors rule out nonexistent i32.extend32_s. -/
inductive IntConversion where
  | wrapI64 | extendI32S | extendI32U
  | extendI32_8S | extendI32_16S
  | extendI64_8S | extendI64_16S | extendI64_32S
  deriving DecidableEq, Repr

def IntConversion.inputType : IntConversion → ValType
  | .wrapI64 | .extendI64_8S | .extendI64_16S | .extendI64_32S => .i64
  | _ => .i32

def IntConversion.outputType : IntConversion → ValType
  | .wrapI64 | .extendI32_8S | .extendI32_16S => .i32
  | _ => .i64

structure FuncType where
  params : List ValType
  results : List ValType
  deriving DecidableEq, Repr

/-- The source block-type forms; indexed types resolve through the module type context. -/
inductive BlockType where
  | val (result : Option ValType)
  | typeIdx (index : Nat)
  deriving DecidableEq, Repr

/-- Expanded function signatures; recursive type identities are stored separately. -/
inductive CompositeType where
  | func (type : FuncType)
  | struct_ (fields : List Types.FieldType)
  | array (field : Types.FieldType)
  deriving DecidableEq, Repr

instance : Coe FuncType CompositeType := ⟨CompositeType.func⟩

def CompositeType.func? : CompositeType → Option FuncType
  | .func type => some type
  | _ => none

abbrev TypeContext := List CompositeType

def TypeContext.func? (types : TypeContext) (index : Nat) : Option FuncType :=
  types[index]?.bind CompositeType.func?

inductive Mutability where
  | const
  | var
  deriving DecidableEq, Repr

structure GlobalType where
  mutability : Mutability
  valType : ValType
  deriving DecidableEq, Repr

def ValType.bits : ValType → Nat
  | .i32 | .f32 => 32
  | .i64 | .f64 => 64
  | .v128 => 128
  | .ref _ | .refNonNull _ => 0

structure MemoryType where
  addrType : ValType
  min : Nat := 0
  max : Option Nat := none
  deriving DecidableEq, Repr

structure TableType where
  addrType : ValType
  min : Nat := 0
  max : Option Nat := none
  kind : RefKind := .func
  nullable : Bool := true
  deriving DecidableEq, Repr

structure MemArg where
  align : Nat := 0
  offset : Nat := 0
  deriving DecidableEq, Repr

structure VectorOp where
  opcode : VectorOpcode
  lanes : List Nat := []
  memory : Nat := 0
  arg : MemArg := {}
  deriving DecidableEq, Repr

inductive LoadOp where
  | i32 | i64 | f32 | f64
  | i32_8S | i32_8U | i32_16S | i32_16U
  | i64_8S | i64_8U | i64_16S | i64_16U | i64_32S | i64_32U
  deriving DecidableEq, Repr

def LoadOp.type : LoadOp → ValType
  | .f32 => .f32 | .f64 => .f64
  | .i32 | .i32_8S | .i32_8U | .i32_16S | .i32_16U => .i32
  | _ => .i64

def LoadOp.bytes : LoadOp → Nat
  | .i32_8S | .i32_8U | .i64_8S | .i64_8U => 1
  | .i32_16S | .i32_16U | .i64_16S | .i64_16U => 2
  | .i32 | .f32 | .i64_32S | .i64_32U => 4
  | .i64 | .f64 => 8

def LoadOp.signed : LoadOp → Bool
  | .i32_8S | .i32_16S | .i64_8S | .i64_16S | .i64_32S => true
  | _ => false

inductive StoreOp where
  | f32 | f64 | i32 | i64 | i32_8 | i32_16 | i64_8 | i64_16 | i64_32
  deriving DecidableEq, Repr

def StoreOp.type : StoreOp → ValType
  | .f32 => .f32 | .f64 => .f64
  | .i32 | .i32_8 | .i32_16 => .i32
  | _ => .i64

def StoreOp.bytes : StoreOp → Nat
  | .i32_8 | .i64_8 => 1
  | .i32_16 | .i64_16 => 2
  | .i32 | .f32 | .i64_32 => 4
  | .i64 | .f64 => 8

def BlockType.resolve (types : TypeContext) : BlockType → Option FuncType
  | .val result => some ⟨[], result.toList⟩
  | .typeIdx index => types.func? (index)

inductive GCReferenceOp where
  | i31New | i31GetS | i31GetU | eq | anyConvertExtern | externConvertAny
  deriving DecidableEq, Repr

def GCReferenceOp.signature (nullable : Bool := true) : GCReferenceOp → FuncType
  | .i31New => ⟨[.i32], [.refNonNull .i31]⟩
  | .i31GetS | .i31GetU => ⟨[.ref .i31], [.i32]⟩
  | .eq => ⟨[.ref .eq, .ref .eq], [.i32]⟩
  | .anyConvertExtern =>
    ⟨[if nullable then .ref .extern else .refNonNull .extern],
      [if nullable then .ref .any else .refNonNull .any]⟩
  | .externConvertAny =>
    ⟨[if nullable then .ref .any else .refNonNull .any],
      [if nullable then .ref .extern else .refNonNull .extern]⟩

inductive ArrayOp where
  | new_ (typeIdx : Nat) (default : Bool)
  | newFixed (typeIdx count : Nat)
  | newData (typeIdx data : Nat)
  | newElem (typeIdx elem : Nat)
  | get (typeIdx : Nat) (signed : Option Bool)
  | set (typeIdx : Nat)
  | len
  | fill (typeIdx : Nat)
  | copy (destination source : Nat)
  | initData (typeIdx data : Nat)
  | initElem (typeIdx elem : Nat)
  deriving DecidableEq, Repr

inductive Instr where
  | const (value : Value)
  | nop
  | unreachable
  | drop
  | select (types : Option (List ValType))
  | binop (type : ValType) (op : IntBinOp)
  | eqz (type : ValType)
  | intUnary (type : ValType) (op : IntUnaryOp)
  | intBinary (type : ValType) (op : IntBinaryOp)
  | intRel (type : ValType) (op : IntRelOp)
  | intConvert (op : IntConversion)
  | vector (operation : VectorOp)
  | floatUnary (width : NumWidth) (op : FloatUnaryOp)
  | floatBinary (width : NumWidth) (op : FloatBinaryOp)
  | floatRel (width : NumWidth) (op : FloatRelOp)
  | floatConvert (op : FloatConversion)
  | localGet (index : Nat)
  | localSet (index : Nat)
  | localTee (index : Nat)
  | globalGet (index : Nat)
  | globalSet (index : Nat)
  | load (op : LoadOp) (memory : Nat) (arg : MemArg)
  | store (op : StoreOp) (memory : Nat) (arg : MemArg)
  | memorySize (memory : Nat)
  | memoryGrow (memory : Nat)
  | memoryFill (memory : Nat)
  | memoryCopy (destination source : Nat)
  | memoryInit (memory data : Nat)
  | dataDrop (data : Nat)
  | call (index : Nat)
  | returnCall (index : Nat)
  | returnCallIndirect (table typeIdx : Nat)
  | returnCallRef (typeIdx : Nat)
  | callIndirect (table typeIdx : Nat)
  | refNull (kind : RefKind)
  | refFunc (index : Nat)
  | refIsNull
  | gcReference (operation : GCReferenceOp)
  | structNew (typeIdx : Nat) (default : Bool)
  | structGet (typeIdx fieldIdx : Nat) (signed : Option Bool)
  | structSet (typeIdx fieldIdx : Nat)
  | arrayOp (operation : ArrayOp)
  | refAsNonNull
  | refTest (nullable : Bool) (heap : RefKind)
  | refCast (nullable : Bool) (heap : RefKind)
  | callRef (typeIdx : Nat)
  | brOnCast (fail : Bool) (depth : Nat) (source target : Types.RefType)
  | brOnNull (depth : Nat)
  | brOnNonNull (depth : Nat)
  | tableGet (table : Nat)
  | tableSet (table : Nat)
  | tableSize (table : Nat)
  | tableGrow (table : Nat)
  | tableFill (table : Nat)
  | tableCopy (destination source : Nat)
  | tableInit (table elem : Nat)
  | elemDrop (elem : Nat)
  | throw_ (tag : Nat)
  | throwRef
  | tryTable (type : BlockType) (catches : List Catch) (body : List Instr)
  | return_
  | block (type : BlockType) (body : List Instr)
  | loop (type : BlockType) (body : List Instr)
  | if_ (type : BlockType) (thenBody elseBody : List Instr)
  | br (depth : Nat)
  | brIf (depth : Nat)
  | brTable (depths : List Nat) (defaultDepth : Nat)
  deriving BEq, Repr

structure GlobalAddr where
  index : Nat
  deriving DecidableEq, Repr

structure MemAddr where
  index : Nat
  deriving DecidableEq, Repr

structure DataAddr where
  index : Nat
  deriving DecidableEq, Repr

structure TableAddr where
  index : Nat
  deriving DecidableEq, Repr

structure ElemAddr where
  index : Nat
  deriving DecidableEq, Repr

/-- External addresses in the represented function, global and memory index spaces. -/
inductive ExternAddr where
  | func (address : FuncAddr)
  | global (address : GlobalAddr)
  | memory (address : MemAddr)
  | table (address : TableAddr)
  | tag (address : TagAddr)
  deriving DecidableEq, Repr

structure ExportInst where
  name : String
  address : ExternAddr
  deriving DecidableEq, Repr

/-- Function/global/memory/data projection of a module instance. -/
structure ModuleInst where
  types : TypeContext := []
  funcs : List FuncAddr := []
  exports : List ExportInst := []
  globals : List GlobalAddr := []
  mems : List MemAddr := []
  datas : List DataAddr := []
  tables : List TableAddr := []
  elems : List ElemAddr := []
  tags : List TagAddr := []
  definedTypes : List Types.DefinedType := []
  funcTypeIndices : List Nat := []
  deriving DecidableEq, Repr

/-- Frame state; the return arity belongs to its administrative activation. -/
structure Frame where
  locals : List (Option Value) := []
  module : ModuleInst := {}
  deriving DecidableEq, Repr

/-- Runtime traps, labels, and activations are distinct from source instructions. -/
inductive AdminInstr where
  | instr (instruction : Instr)
  | trap
  | label (arity : Nat) (continuation : List Instr) (body : List AdminInstr)
  | frame (arity : Nat) (state : Frame) (body : List AdminInstr)
  /-- Projection of the non-null `ref.func address; call_ref type` intermediate pair. -/
  | invoke (address : FuncAddr) (type : FuncType)
  | castFunc (type : FuncType)
  | invokeRef (type : FuncType)
  | castDefined (type : Types.DefinedType)
  | invokeDefined (type : Types.DefinedType)
  | returnInvoke (address : FuncAddr) (type : FuncType)
  | returnInvokeRef (type : FuncType)
  | returnInvokeDefined (type : Types.DefinedType)
  | tailActivation (body : List AdminInstr)
  | throwing (address : ExnAddr)
  | handler (catches : List Catch) (body : List AdminInstr)
  deriving BEq, Repr

def values (vs : List Value) : List AdminInstr := vs.map (fun v => .instr (.const v))

def instructions (code : List Instr) : List AdminInstr := code.map .instr

end Wasm
