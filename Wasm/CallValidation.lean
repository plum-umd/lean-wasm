import Wasm.LocalValidation
import Wasm.LocalInitialization
import Wasm.Runtime
import Wasm.GlobalValidation
import Wasm.MemoryValidation
import Wasm.VectorValidation
import Wasm.BulkMemoryValidation
import Wasm.ArrayValidation
import Wasm.StructValidation
import Wasm.TableValidation

namespace Wasm

/-- Static module function indices are signatures, distinct from runtime store addresses.
An absent return type describes expressions; `some []` describes a void function.
-/
structure FunctionContext where
  types : TypeContext := []
  locals : List ValType := []
  funcs : List FuncType := []
  tags : List FuncType := []
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

def FunctionContext.referenceElemTypes (context : FunctionContext) : List ValType :=
  if context.elemTypes.isEmpty then context.elems.map ValType.ref else context.elemTypes

inductive CatchTyping (context : FunctionContext) (labels : LabelContext) : Catch → Prop where
  | tag (ht : context.tags[x]? = some ft) (hl : labels[d]? = some target)
      (hm : Types.ResultMatches ⟨context.definedTypes, []⟩
        ((ft.params ++ if reference then [ValType.refNonNull .exn] else []).map Types.embedVal)
        (target.map Types.embedVal)) : CatchTyping context labels (.tag x d reference)
  | all (hl : labels[d]? = some target)
      (hm : Types.ResultMatches ⟨context.definedTypes, []⟩
        ((if reference then [ValType.refNonNull .exn] else []).map Types.embedVal)
        (target.map Types.embedVal)) : CatchTyping context labels (.all d reference)

mutual
  inductive RuntimeInstrTyping (context : FunctionContext) :
      LabelContext → Instr → List ValType → List ValType → Prop where
    | arrays : ArrayInstrTyping context.types context.definedTypes context.referenceElemTypes
        context.dataCount op input output →
        RuntimeInstrTyping context labels (.arrayOp op) input output
    | structures : StructInstrTyping context.types i input output →
        RuntimeInstrTyping context labels i input output
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
    | nonNullFunc (hf : context.funcs[x]? = some ft) (hd : x ∈ context.declaredRefs) :
        RuntimeInstrTyping context labels (.refFunc x) [] [.refNonNull .func]
    | typedFunc (hf : context.funcs[x]? = some ft)
        (ht : context.funcTypeIndices[x]? = some typeIdx) (hd : x ∈ context.declaredRefs) :
        RuntimeInstrTyping context labels (.refFunc x) [] [.refNonNull (.typeIdx typeIdx)]
    | tables : TableInstrTyping context.types context.tables context.elems i input output →
        RuntimeInstrTyping context labels i input output
    | indirectTyped (ht : context.tables[x]? = some table)
        (hk : Types.HeapMatches ⟨context.definedTypes, []⟩ table.kind .func)
        (hf : context.types.func? (y) = some ft) :
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
    | callRef (h : context.types.func? (x) = some ft) :
        RuntimeInstrTyping context labels (.callRef x)
          (ft.params ++ [.ref (.typeIdx x)]) ft.results
    | refTest (hv : (Types.ValType.ref nullable heap).Valid ⟨context.definedTypes, []⟩)
        (ht : Types.HeapMatches ⟨context.definedTypes, []⟩ heap top)
        (hb : top ∈ [Types.HeapType.any, .func, .extern, .exn]) :
        RuntimeInstrTyping context labels (.refTest nullable heap) [.ref top] [.i32]
    | refCast (hv : (Types.ValType.ref nullable heap).Valid ⟨context.definedTypes, []⟩)
        (ht : Types.HeapMatches ⟨context.definedTypes, []⟩ heap top)
        (hb : top ∈ [Types.HeapType.any, .func, .extern, .exn]) :
        RuntimeInstrTyping context labels (.refCast nullable heap) [.ref top]
          [if nullable then .ref heap else .refNonNull heap]
    | vector (ht : VectorInstrTyping context.mems op input output) :
        RuntimeInstrTyping context labels (.vector op) input output
    | gcReference {nullable : Bool} : RuntimeInstrTyping context labels (.gcReference op)
        (op.signature nullable).params (op.signature nullable).results
    | refAsNonNull : RuntimeInstrTyping context labels .refAsNonNull
        [.ref heap] [.refNonNull heap]
    | brOnNull (h : labels[x]? = some ts) :
        RuntimeInstrTyping context labels (.brOnNull x)
          (ts ++ [.ref heap]) (ts ++ [.refNonNull heap])
    | brOnNonNull {nullable : Bool} (h : labels[x]? =
        some (ts ++ [if nullable then .ref heap else .refNonNull heap])) :
        RuntimeInstrTyping context labels (.brOnNonNull x) (ts ++ [.ref heap]) ts
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
    | validation : ValidationSeqTyping context labels code
        (input.map Types.embedVal) (output.map Types.embedVal) →
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

  /- Validation stack types include bottom, which has no source or runtime value. -/
  inductive ValidationInstrTyping (context : FunctionContext) :
      LabelContext → Instr → List Types.ValType → List Types.ValType → Prop where
    | legacy : RuntimeInstrTyping context labels i input output →
        ValidationInstrTyping context labels i
          (input.map Types.embedVal) (output.map Types.embedVal)
    | brOnCast (hl : labels[x]? = some (ts ++ [label]))
        (hs : source.val.Valid ⟨context.definedTypes, []⟩)
        (ht : target.val.Valid ⟨context.definedTypes, []⟩)
        (hm : Types.ValMatches ⟨context.definedTypes, []⟩ target.val source.val)
        (hb : Types.ValMatches ⟨context.definedTypes, []⟩
          (if fail then (source.difference target).val else target.val) (Types.embedVal label)) :
        ValidationInstrTyping context labels (.brOnCast fail x source target)
          (ts.map Types.embedVal ++ [source.val])
          (ts.map Types.embedVal ++
            [if fail then target.val else (source.difference target).val])
    | drop : ValidationInstrTyping context labels .drop [t] []
    | select (ht : t = .bot ∨ t = .i32 ∨ t = .i64 ∨ t = .f32 ∨ t = .f64 ∨ t = .v128) :
        ValidationInstrTyping context labels (.select none) [t, t, .i32] [t]
    | unreachable : ValidationInstrTyping context labels .unreachable input output
    | br (h : labels[x]? = some ts) :
        ValidationInstrTyping context labels (.br x) (input ++ ts.map Types.embedVal) output
    | brTable (hd : labels[fallback]? = some ts)
        (ht : ∀ x ∈ targets, labels[x]? = some ts) :
        ValidationInstrTyping context labels (.brTable targets fallback)
          (input ++ (ts ++ [ValType.i32]).map Types.embedVal) output
    | brTableMatches
        (ht : ∀ x ∈ fallback :: targets, ∃ ts, labels[x]? = some ts ∧
          Types.ResultMatches ⟨context.definedTypes, []⟩ arguments (ts.map Types.embedVal)) :
        ValidationInstrTyping context labels (.brTable targets fallback)
          (input ++ (arguments ++ [.i32])) output
    | throw_ (ht : context.tags[x]? = some ft) :
        ValidationInstrTyping context labels (.throw_ x)
          (input ++ ft.params.map Types.embedVal) output
    | throwRef : ValidationInstrTyping context labels .throwRef
        (input ++ [.ref true .exn]) output
    | tryTable (ht : bt.resolve context.types = some ft)
        (hc : ∀ c ∈ catches, CatchTyping context labels c)
        (hb : ValidationSeqTyping context (ft.results :: labels) body
          (ft.params.map Types.embedVal) (ft.results.map Types.embedVal)) :
        ValidationInstrTyping context labels (.tryTable bt catches body)
          (ft.params.map Types.embedVal) (ft.results.map Types.embedVal)
    | returnCall (hf : context.funcs[x]? = some ft)
        (hr : context.returns = some results)
        (hm : Types.ResultMatches ⟨context.definedTypes, []⟩
          (ft.results.map Types.embedVal) (results.map Types.embedVal)) :
        ValidationInstrTyping context labels (.returnCall x)
          (input ++ ft.params.map Types.embedVal) output
    | returnCallRef (hf : context.types.func? (x) = some ft)
        (hr : context.returns = some results)
        (hm : Types.ResultMatches ⟨context.definedTypes, []⟩
          (ft.results.map Types.embedVal) (results.map Types.embedVal)) :
        ValidationInstrTyping context labels (.returnCallRef x)
          (input ++ (ft.params.map Types.embedVal ++ [.ref true (.typeIdx x)])) output
    | returnCallIndirect (ht : context.tables[x]? = some table)
        (hk : Types.HeapMatches ⟨context.definedTypes, []⟩ table.kind .func)
        (hf : context.types.func? (y) = some ft) (hr : context.returns = some results)
        (hm : Types.ResultMatches ⟨context.definedTypes, []⟩
          (ft.results.map Types.embedVal) (results.map Types.embedVal)) :
        ValidationInstrTyping context labels (.returnCallIndirect x y)
          (input ++ (ft.params ++ [table.addrType]).map Types.embedVal) output
    | return_ (h : context.returns = some results) :
        ValidationInstrTyping context labels .return_
          (input ++ results.map Types.embedVal) output
    | block (ht : bt.resolve context.types = some ft)
        (hb : ValidationSeqTyping context (ft.results :: labels) body
          (ft.params.map Types.embedVal) (ft.results.map Types.embedVal)) :
        ValidationInstrTyping context labels (.block bt body)
          (ft.params.map Types.embedVal) (ft.results.map Types.embedVal)
    | loop (ht : bt.resolve context.types = some ft)
        (hb : ValidationSeqTyping context (ft.params :: labels) body
          (ft.params.map Types.embedVal) (ft.results.map Types.embedVal)) :
        ValidationInstrTyping context labels (.loop bt body)
          (ft.params.map Types.embedVal) (ft.results.map Types.embedVal)
    | if_ (ht : bt.resolve context.types = some ft)
        (hy : ValidationSeqTyping context (ft.results :: labels) yes
          (ft.params.map Types.embedVal) (ft.results.map Types.embedVal))
        (hn : ValidationSeqTyping context (ft.results :: labels) no
          (ft.params.map Types.embedVal) (ft.results.map Types.embedVal)) :
        ValidationInstrTyping context labels (.if_ bt yes no)
          ((ft.params ++ [ValType.i32]).map Types.embedVal) (ft.results.map Types.embedVal)
    | weaken : ValidationInstrTyping context labels i input output →
        ValidationInstrTyping context labels i (base ++ input) (base ++ output)
    | subtype : ValidationInstrTyping context labels i input output →
        Types.ResultMatches ⟨context.definedTypes, []⟩ input' input →
        Types.ResultMatches ⟨context.definedTypes, []⟩ output output' →
        ValidationInstrTyping context labels i input' output'

  inductive ValidationSeqTyping (context : FunctionContext) :
      LabelContext → List Instr → List Types.ValType → List Types.ValType → Prop where
    | legacy : RuntimeSeqTyping context labels code input output →
        ValidationSeqTyping context labels code
          (input.map Types.embedVal) (output.map Types.embedVal)
    | empty : ValidationSeqTyping context labels [] ts ts
    | cons : ValidationInstrTyping context labels i input middle →
        ValidationSeqTyping context labels rest middle output →
        ValidationSeqTyping context labels (i :: rest) input output
    | weaken : ValidationSeqTyping context labels code input output →
        ValidationSeqTyping context labels code (base ++ input) (base ++ output)
    | subtype : ValidationSeqTyping context labels code input output →
        Types.ResultMatches ⟨context.definedTypes, []⟩ input' input →
        Types.ResultMatches ⟨context.definedTypes, []⟩ output output' →
        ValidationSeqTyping context labels code input' output'
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
      (funcTypeIndices : List Nat := []) → (elemTypes : List ValType := []) →
      (tags : List FuncType := []) → Prop where
  | wasm (ht : types.func? (function.typeIdx) = some ft)
      (hi : function.Initialized ft)
      (hb : RuntimeSeqTyping
        { types, locals := ft.params ++ function.locals, funcs, returns := some ft.results,
          globals, mems, dataCount, tables, elems, declaredRefs, definedTypes, funcTypeIndices, elemTypes, tags }
        [ft.results] function.body [] ft.results) :
      FuncTyping types funcs globals mems dataCount
        (tables := tables) (elems := elems) (declaredRefs := declaredRefs)
        (definedTypes := definedTypes) (funcTypeIndices := funcTypeIndices)
        (elemTypes := elemTypes) (tags := tags) function ft

  | wasmValidation (ht : types.func? (function.typeIdx) = some ft)
      (hi : function.Initialized ft)
      (hb : ValidationSeqTyping
        { types, locals := ft.params ++ function.locals, funcs, returns := some ft.results,
          globals, mems, dataCount, tables, elems, declaredRefs, definedTypes,
          funcTypeIndices, elemTypes, tags }
        [ft.results] function.body [] (ft.results.map Types.embedVal)) :
      FuncTyping types funcs globals mems dataCount
        (tables := tables) (elems := elems) (declaredRefs := declaredRefs)
        (definedTypes := definedTypes) (funcTypeIndices := funcTypeIndices)
        (elemTypes := elemTypes) (tags := tags) function ft

theorem FuncTyping.initialized
    (h : FuncTyping types funcs globals mems dataCount function ft
      (tables := tables) (elems := elems) (declaredRefs := declaredRefs)
      (definedTypes := definedTypes) (funcTypeIndices := funcTypeIndices)
      (elemTypes := elemTypes) (tags := tags)) :
    function.Initialized ft := by
  cases h with
  | wasm _ hi _ | wasmValidation _ hi _ => exact hi

end Wasm
