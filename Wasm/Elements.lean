import Wasm.DataValidation

namespace Wasm

structure Table where
  type : TableType
  init : List Instr := [.refNull type.kind]
  deriving BEq, Repr

inductive ElemMode where
  | passive
  | declarative
  | active (table : Nat) (offset : List Instr)
  deriving BEq, Repr

structure Elem where
  kind : RefKind := .func
  init : List (List Instr) := []
  mode : ElemMode := .passive
  nullable : Bool := true
  deriving BEq, Repr

def Elem.refType (elem : Elem) : ValType :=
  if elem.nullable then .ref elem.kind else .refNonNull elem.kind

def Elem.initializer (elem : Elem) (index : Nat) : List Instr :=
  match elem.mode with
  | .passive => []
  | .declarative => [.elemDrop index]
  | .active table offset => offset ++
      [.const (.i32 0), .const (Value.ofNat .i32 elem.init.length),
        .tableInit table index, .elemDrop index]

structure TableTyping (context : FunctionContext) (table : Table) : Prop where
  type : table.type.Valid
  init : RuntimeSeqTyping context [] table.init [] [table.type.refType]
  constant : ∀ i ∈ table.init, ConstantInstr context.globals i

inductive ElemModeTyping (context : FunctionContext) (type : ValType) : ElemMode → Prop where
  | passive : ElemModeTyping context type .passive
  | declarative : ElemModeTyping context type .declarative
  | active (ht : context.tables[x]? = some table)
      (hk : Types.ValMatches ⟨context.definedTypes, []⟩
        (Types.embedVal type) (Types.embedVal table.refType))
      (ho : RuntimeSeqTyping context [] offset [] [table.addrType])
      (hc : ∀ i ∈ offset, ConstantInstr context.globals i) :
      ElemModeTyping context type (.active x offset)

structure ElemTyping (context : FunctionContext) (elem : Elem) : Prop where
  init : ∀ expression ∈ elem.init, RuntimeSeqTyping context [] expression [] [elem.refType]
  constant : ∀ expression ∈ elem.init, ∀ i ∈ expression, ConstantInstr context.globals i
  mode : ElemModeTyping context elem.refType elem.mode

end Wasm
