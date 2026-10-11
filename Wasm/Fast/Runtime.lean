import Wasm.Fast.Store

namespace Wasm.Fast

/-- Function reference types come from the store. Null uses its hierarchy bottom. -/
def RefValue.type? (store : Store) : RefValue → Option ValType
  | .func address => (store.func? address).map fun function =>
      .refNonNull function.runtimeType.heap
  | .struct_ address => (store.structs[address.index]?).map fun object =>
      .refNonNull object.type.heap
  | .array address => (store.arrays[address.index]?).map fun object =>
      .refNonNull object.type.heap
  | .exn _ => some (.refNonNull .exn)
  | .extern _ | .external _ => some (.refNonNull .extern)
  | .i31 _ => some (.refNonNull .i31)
  | .host _ => some (.refNonNull .any)
  | .null heap => match heap with
    | .func | .nofunc => some (.ref .nofunc)
    | .defined group index =>
      match (Types.DefinedType.mk group index).expandComposite? with
      | some (.func _) => some (.ref .nofunc)
      | some (.struct_ _) | some (.array _) => some (.ref .none)
      | none => none
    | .extern | .noextern => some (.ref .noextern)
    | .exn | .noexn => some (.ref .noexn)
    | .any | .eq | .i31 | .struct_ | .array | .none => some (.ref .none)
    | _ => none

def Value.type? (store : Store) : Value → Option ValType
  | .i32 _ => some .i32
  | .i64 _ => some .i64
  | .f32 _ => some .f32
  | .f64 _ => some .f64
  | .v128 _ => some .v128
  | .ref reference => RefValue.type? store reference

abbrev Typed (store : Store) (value : Value) (type : ValType) : Prop :=
  ∃ actual, Value.type? store value = some actual ∧
    Types.ValMatches {} (Types.embedVal actual) (Types.embedVal type)

def checkRuntimeHeap (a b : Types.HeapType) : Types.Checked (Types.HeapMatches {} a b) :=
  Types.checkHeap (Types.matchingBudget a b) {} a b

def searchRuntimeVal (a b : ValType) : Types.Search
    (Types.ValMatches {} (Types.embedVal a) (Types.embedVal b)) :=
  Types.searchVal (match a, b with
    | .ref a, .ref b | .refNonNull a, .ref b | .ref a, .refNonNull b
    | .refNonNull a, .refNonNull b => Types.matchingBudget a b
    | _, _ => 1) {} (Types.embedVal a) (Types.embedVal b)

def checkRuntimeVal (a b : ValType) : Types.Checked
    (Types.ValMatches {} (Types.embedVal a) (Types.embedVal b)) :=
  (searchRuntimeVal a b).toOption

/-- Unknown addresses and exhausted search remain inconclusive, never cast failures. -/
def searchValue (store : Store) (value : Value) (type : ValType) :
    Types.Search (Typed store value type) :=
  match found : Value.type? store value with
  | none => .inconclusive
  | some actual => (searchRuntimeVal actual type).map fun h => ⟨⟨actual, found, h.down⟩⟩

/-- Every successful check carries a derivation; inconclusive checks leave execution stuck. -/
def checkValue (store : Store) (value : Value) (type : ValType) :
    Types.Checked (Typed store value type) :=
  (searchValue store value type).toOption

theorem checkValue_sound (h : (checkValue store value type).isSome = true) :
    Typed store value type := by
  cases hc : checkValue store value type with
  | none => simp [hc] at h
  | some proof => exact proof.down

def TableType.refType (type : TableType) : ValType :=
  if type.nullable then .ref type.kind else .refNonNull type.kind

def ElemInst.refType (elem : ElemInst) : ValType :=
  if elem.nullable then .ref elem.kind else .refNonNull elem.kind

inductive ArgsTyped (store : Store) : List Value → List ValType → Prop where
  | nil : ArgsTyped store [] []
  | cons : Typed store value type → ArgsTyped store vs ts →
      ArgsTyped store (value :: vs) (type :: ts)

def checkArgs (store : Store) : (args : List Value) → (types : List ValType) →
    Types.Checked (ArgsTyped store args types)
  | [], [] => some ⟨.nil⟩
  | value :: values, type :: types => do
    let head ← checkValue store value type
    let tail ← checkArgs store values types
    return ⟨.cons head.down tail.down⟩
  | _, _ => none

def GlobalInst.Valid (store : Store) (global : GlobalInst) : Prop :=
  Typed store global.value global.type.valType

def TableInst.ReferencesValid (store : Store) (table : TableInst) : Prop :=
  ∀ reference ∈ table.refs.toList, Typed store (.ref reference) table.type.refType

def ElemInst.ReferencesValid (store : Store) (elem : ElemInst) : Prop :=
  ∀ reference ∈ elem.refs.toList, Typed store (.ref reference) elem.refType

theorem Typed.store_funcs (h : Typed store value type) (same : next.funcs = store.funcs)
    (sameStructs : next.structs = store.structs) (sameArrays : next.arrays = store.arrays) :
    Typed next value type := by
  obtain ⟨actual, found, matched⟩ := h
  refine ⟨actual, ?_, matched⟩
  cases value with
  | i32 _ | i64 _ | f32 _ | f64 _ | v128 _ => exact found
  | ref reference =>
    cases reference <;>
      simpa [Value.type?, RefValue.type?, Store.func?, same, sameStructs, sameArrays] using found

/-- Prepare an activation using store-dependent argument typing and optional local defaults. -/
def FuncInst.activation? (function : FuncInst) (args : List Value)
    (store : Store := {}) : Option AdminInstr :=
  match function.code with
  | .host _ | .hostTyped _ _ => none
  | .wasm code =>
    if function.module.types.func? (code.typeIdx) = some function.type then
      match checkArgs store args function.type.params with
      | none => none
      | some _ =>
        let frame := Frame.initialize function.module args code.locals
        let arity := function.type.results.length
        some (.frame arity frame [.label arity [] (instructions code.body)])
    else none

inductive Invokes (store : Store) : FuncInst → List Value → AdminInstr → Prop where
  | wasm (hs : module.types.func? (code.typeIdx) = some type)
      (ha : ArgsTyped store args type.params) :
      Invokes store ⟨type, module, .wasm code⟩ args
        (.frame type.results.length (Frame.initialize module args code.locals)
          [.label type.results.length [] (instructions code.body)])

theorem FuncInst.activation?_sound
    (h : FuncInst.activation? function args store = some activation) :
    Invokes store function args activation := by
  cases function with
  | mk type module code =>
    cases code with
    | host id => simp [FuncInst.activation?] at h
    | hostTyped id type => simp [FuncInst.activation?] at h
    | wasm code =>
      simp only [FuncInst.activation?] at h
      split at h
      · rename_i valid
        cases hc : checkArgs store args type.params with
        | none => simp [hc] at h
        | some checked =>
          simp only [hc] at h
          cases h
          exact .wasm valid checked.down
      · cases h

/-- Completeness is conditional on successful bounded argument search. -/
theorem FuncInst.activation?_complete (h : Invokes store function args activation)
    (checked : (checkArgs store args function.type.params).isSome = true) :
    FuncInst.activation? function args store = some activation := by
  cases h with
  | wasm hs ha =>
    simp only [FuncInst.activation?, hs, ↓reduceIte]
    cases hc : checkArgs store args _ with
    | none => simp [hc] at checked
    | some proof => rfl


@[simp] theorem RefValue.type?_toSpec (s : Store) (r : RefValue) :
    Wasm.RefValue.type? s.toSpec r = RefValue.type? s r := by
  cases r <;> simp [Wasm.RefValue.type?, RefValue.type?, Store.toSpec, Store.func?,
    Wasm.Store.func?] <;> rfl

@[simp] theorem Value.type?_toSpec (s : Store) (v : Value) :
    Wasm.Value.type? s.toSpec v = Value.type? s v := by
  cases v <;> simp [Wasm.Value.type?, Value.type?]

@[simp] theorem typed_toSpec (s : Store) (v : Value) (t : ValType) :
    Wasm.Typed s.toSpec v t ↔ Typed s v t := by
  simp [Wasm.Typed, Typed]

theorem ArgsTyped.toSpec (h : ArgsTyped s vs ts) : Wasm.ArgsTyped s.toSpec vs ts := by
  induction h with
  | nil => exact .nil
  | cons hv _ ih => exact .cons ((typed_toSpec _ _ _).mpr hv) ih

theorem Invokes.toSpec (h : Invokes s f vs activation) :
    Wasm.Invokes s.toSpec f vs activation := by
  cases h with
  | wasm hs ha => exact .wasm hs ha.toSpec

@[simp] theorem searchValue_rejected_toSpec (s : Store) (v : Value) (t : ValType) :
    (Wasm.searchValue s.toSpec v t).isRejected = (searchValue s v t).isRejected := by
  have same := Value.type?_toSpec s v
  unfold Wasm.searchValue searchValue
  split <;> split <;> simp_all [Value.type?_toSpec, Types.Search.isRejected]
  rename_i actual hleft other hright
  subst other
  rw [show Wasm.searchRuntimeVal actual t = searchRuntimeVal actual t from rfl]
  cases searchRuntimeVal actual t <;> rfl

@[simp] theorem argsTyped_toSpec (s : Store) (vs : List Value) (ts : List ValType) :
    Wasm.ArgsTyped s.toSpec vs ts ↔ ArgsTyped s vs ts := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | cons hv _ ih => exact .cons ((typed_toSpec _ _ _).mp hv) ih
  · exact ArgsTyped.toSpec

@[simp] theorem invokes_toSpec (s : Store) (f : FuncInst) (vs : List Value)
    (activation : AdminInstr) :
    Wasm.Invokes s.toSpec f vs activation ↔ Invokes s f vs activation := by
  constructor
  · intro h
    cases h with
    | wasm hs ha => exact .wasm hs ((argsTyped_toSpec _ _ _).mp ha)
  · exact Invokes.toSpec

@[simp] theorem checkValue_isSome_toSpec (s : Store) (v : Value) (t : ValType) :
    (Wasm.checkValue s.toSpec v t).isSome = (checkValue s v t).isSome := by
  have same := Value.type?_toSpec s v
  unfold Wasm.checkValue checkValue Wasm.searchValue searchValue
  split <;> split <;> simp_all [Value.type?_toSpec, Types.Search.toOption]
  rename_i actual hleft other hright
  subst other
  rw [show Wasm.searchRuntimeVal actual t = searchRuntimeVal actual t from rfl]
  cases searchRuntimeVal actual t <;> rfl

@[simp] theorem checkArgs_isSome_toSpec (s : Store) (vs : List Value) (ts : List ValType) :
    (Wasm.checkArgs s.toSpec vs ts).isSome = (checkArgs s vs ts).isSome := by
  induction vs generalizing ts with
  | nil => cases ts <;> rfl
  | cons v vs ih =>
    cases ts with
    | nil => rfl
    | cons t ts =>
      have hv := checkValue_isSome_toSpec s v t
      have ht := ih ts
      clear ih
      simp only [Wasm.checkArgs, checkArgs]
      cases h1 : Wasm.checkValue s.toSpec v t <;> cases h2 : checkValue s v t <;>
        simp_all
      cases h3 : Wasm.checkArgs s.toSpec vs ts <;> cases h4 : checkArgs s vs ts <;>
        simp_all

@[simp] theorem activation_toSpec (s : Store) (f : FuncInst) (vs : List Value) :
    Wasm.FuncInst.activation? f vs s.toSpec = FuncInst.activation? f vs s := by
  cases f with
  | mk type module code =>
    cases code <;> simp only [Wasm.FuncInst.activation?, FuncInst.activation?]
    split
    · have same := checkArgs_isSome_toSpec s vs type.params
      split <;> split <;> simp_all
    · rfl

end Wasm.Fast
