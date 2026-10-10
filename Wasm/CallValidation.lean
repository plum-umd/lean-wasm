import Wasm.LocalValidation
import Wasm.LocalInitialization
import Wasm.Runtime
import Wasm.GlobalValidation
import Wasm.MemoryValidation
import Wasm.BulkMemoryValidation
import Wasm.TableValidation

namespace Wasm

/-- Static module function indices are signatures, distinct from runtime store addresses.
An absent return type describes expressions; `some []` describes a void function.
-/
structure FunctionContext where
  types : TypeContext := []
  locals : List ValType := []
  funcs : List FuncType := []
  returns : Option (List ValType) := none
  globals : List GlobalType := []
  mems : List MemoryType := []
  dataCount : Nat := 0
  tables : List TableType := []
  elems : List RefKind := []
  declaredRefs : List Nat := []
  definedTypes : List Types.DefinedType := []
  funcTypeIndices : List Nat := []
  elemTypes : List ValType := []
  deriving DecidableEq, Repr

mutual
  inductive RuntimeInstrTyping (context : FunctionContext) :
      LabelContext → Instr → List ValType → List ValType → Prop where
    | plain : FunctionInstrTyping context.types context.locals labels i input output →
        RuntimeInstrTyping context labels i input output
    | global : GlobalInstrTyping context.globals i input output →
        RuntimeInstrTyping context labels i input output
    | memory : MemoryInstrTyping context.mems i input output →
        RuntimeInstrTyping context labels i input output
    | bulk : BulkInstrTyping context.mems context.dataCount i input output →
        RuntimeInstrTyping context labels i input output
    | references : ReferenceInstrTyping context.funcs context.declaredRefs i input output →
        RuntimeInstrTyping context labels i input output
    | typedFunc (hf : context.funcs[x]? = some ft)
        (ht : context.funcTypeIndices[x]? = some typeIdx) (hd : x ∈ context.declaredRefs) :
        RuntimeInstrTyping context labels (.refFunc x) [] [.refNonNull (.typeIdx typeIdx)]
    | tables : TableInstrTyping context.types context.tables context.elems i input output →
        RuntimeInstrTyping context labels i input output
    | indirectTyped (ht : context.tables[x]? = some table)
        (hk : Types.HeapMatches ⟨context.definedTypes, []⟩ table.kind .func)
        (hf : context.types[y]? = some ft) :
        RuntimeInstrTyping context labels (.callIndirect x y)
          (ft.params ++ [table.addrType]) ft.results
    | tableCopy (hd : context.tables[x]? = some dst) (hs : context.tables[y]? = some src)
        (hk : Types.ValMatches ⟨context.definedTypes, []⟩
          (Types.embedVal src.refType) (Types.embedVal dst.refType)) :
        RuntimeInstrTyping context labels (.tableCopy x y)
          [dst.addrType, src.addrType, dst.addrType.minAddress src.addrType] []
    | tableInit (ht : context.tables[x]? = some table) (he : context.elems[y]? = some heap)
        (hk : Types.ValMatches ⟨context.definedTypes, []⟩
          (.ref true heap) (Types.embedVal table.refType)) :
        RuntimeInstrTyping context labels (.tableInit x y) [table.addrType, .i32, .i32] []
    | tableInitTyped (ht : context.tables[x]? = some table)
        (he : context.elemTypes[y]? = some type)
        (hk : Types.ValMatches ⟨context.definedTypes, []⟩
          (Types.embedVal type) (Types.embedVal table.refType)) :
        RuntimeInstrTyping context labels (.tableInit x y) [table.addrType, .i32, .i32] []
    | call (h : context.funcs[x]? = some ft) :
        RuntimeInstrTyping context labels (.call x) ft.params ft.results
    | return_ (h : context.returns = some results) :
        RuntimeInstrTyping context labels .return_ (input ++ results) output
    | block (ht : bt.resolve context.types = some ft)
        (hb : RuntimeSeqTyping context (ft.results :: labels) body ft.params ft.results) :
        RuntimeInstrTyping context labels (.block bt body) ft.params ft.results
    | loop (ht : bt.resolve context.types = some ft)
        (hb : RuntimeSeqTyping context (ft.params :: labels) body ft.params ft.results) :
        RuntimeInstrTyping context labels (.loop bt body) ft.params ft.results
    | if_ (ht : bt.resolve context.types = some ft)
        (hy : RuntimeSeqTyping context (ft.results :: labels) yes ft.params ft.results)
        (hn : RuntimeSeqTyping context (ft.results :: labels) no ft.params ft.results) :
        RuntimeInstrTyping context labels (.if_ bt yes no) (ft.params ++ [.i32]) ft.results
    | weaken : RuntimeInstrTyping context labels i input output →
        RuntimeInstrTyping context labels i (ts₀ ++ input) (ts₀ ++ output)
    | subtype : RuntimeInstrTyping context labels i input output →
        Types.ResultMatches ⟨context.definedTypes, []⟩
          (input'.map Types.embedVal) (input.map Types.embedVal) →
        Types.ResultMatches ⟨context.definedTypes, []⟩
          (output.map Types.embedVal) (output'.map Types.embedVal) →
        RuntimeInstrTyping context labels i input' output'

  inductive RuntimeSeqTyping (context : FunctionContext) :
      LabelContext → List Instr → List ValType → List ValType → Prop where
    | plain : FunctionSeqTyping context.types context.locals labels code input output →
        RuntimeSeqTyping context labels code input output
    | empty : RuntimeSeqTyping context labels [] ts ts
    | cons : RuntimeInstrTyping context labels i input middle →
        RuntimeSeqTyping context labels rest middle output →
        RuntimeSeqTyping context labels (i :: rest) input output
    | weaken : RuntimeSeqTyping context labels code input output →
        RuntimeSeqTyping context labels code (ts₀ ++ input) (ts₀ ++ output)
    | subtype : RuntimeSeqTyping context labels code input output →
        Types.ResultMatches ⟨context.definedTypes, []⟩
          (input'.map Types.embedVal) (input.map Types.embedVal) →
        Types.ResultMatches ⟨context.definedTypes, []⟩
          (output.map Types.embedVal) (output'.map Types.embedVal) →
        RuntimeSeqTyping context labels code input' output'
end

theorem FunctionSeqTyping.toRuntimeSeqTyping
    (h : FunctionSeqTyping context.types context.locals labels code input output) :
    RuntimeSeqTyping context labels code input output := .plain h

/-- A function body starts with an empty stack and its implicit result label.
Parameters and defaultable locals start initialized; `Initialized` checks the remaining effects.
-/
inductive FuncTyping (types : TypeContext) (funcs : List FuncType) (globals : List GlobalType)
    (mems : List MemoryType) (dataCount : Nat) :
    Func → FuncType → (tables : List TableType := []) → (elems : List RefKind := []) →
      (declaredRefs : List Nat := []) →
      (definedTypes : List Types.DefinedType := []) →
      (funcTypeIndices : List Nat := []) → (elemTypes : List ValType := []) → Prop where
  | wasm (ht : types[function.typeIdx]? = some ft)
      (hi : function.Initialized ft)
      (hb : RuntimeSeqTyping
        { types, locals := ft.params ++ function.locals, funcs, returns := some ft.results,
          globals, mems, dataCount, tables, elems, declaredRefs, definedTypes, funcTypeIndices, elemTypes }
        [ft.results] function.body [] ft.results) :
      FuncTyping types funcs globals mems dataCount
        (tables := tables) (elems := elems) (declaredRefs := declaredRefs)
        (definedTypes := definedTypes) (funcTypeIndices := funcTypeIndices)
        (elemTypes := elemTypes) function ft

theorem FuncTyping.initialized
    (h : FuncTyping types funcs globals mems dataCount function ft
      (tables := tables) (elems := elems) (declaredRefs := declaredRefs)
      (definedTypes := definedTypes) (funcTypeIndices := funcTypeIndices) (elemTypes := elemTypes)) :
    function.Initialized ft := by
  cases h with
  | wasm _ hi _ => exact hi

end Wasm
