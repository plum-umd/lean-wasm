import Wasm.Runtime

/-!
Declarative type invariants for execution completeness. These conditions do not mention an
executable matching check or its fuel. They cover runtime type identities and the agreement
between module projections; typing of object contents and instruction bodies remains separate.
-/

namespace Wasm

/-- A runtime type is closed and has valid rolled recursive declarations. -/
def Types.DefinedType.RuntimeValid (type : Types.DefinedType) : Prop :=
  type.closed ∧ Types.HeapValid {} type.heap

/-- Function references carry the same signature used for invocation. -/
def FuncInst.RuntimeTypeValid (function : FuncInst) : Prop :=
  function.runtimeType.RuntimeValid ∧
    function.runtimeType.expand? = some (Types.embedFunc function.type)

/-- A stored structure has a valid type in the structure hierarchy. -/
def StructInst.RuntimeTypeValid (object : StructInst) : Prop :=
  object.type.RuntimeValid ∧ ∃ fields, object.type.expandComposite? = some (.struct_ fields)

/-- A stored array has a valid type in the array hierarchy. -/
def ArrayInst.RuntimeTypeValid (object : ArrayInst) : Prop :=
  object.type.RuntimeValid ∧ ∃ field, object.type.expandComposite? = some (.array field)

/-- The type-facing part of store well-formedness, independent of executable matching. -/
structure Store.RuntimeTypesValid (store : Store) : Prop where
  functions : ∀ function ∈ store.funcs, function.RuntimeTypeValid
  structures : ∀ object ∈ store.structs, object.RuntimeTypeValid
  arrays : ∀ object ∈ store.arrays, object.RuntimeTypeValid
  tags : ∀ tag ∈ store.tags, tag.definedType.RuntimeValid ∧
    tag.definedType.expand? = some (Types.embedFunc tag.type)

/-- Static arity/field projections and runtime type identities describe the same module types. -/
structure ModuleInst.RuntimeTypesCoherent (module : ModuleInst) : Prop where
  length : module.types.length = module.definedTypes.length
  projection : ∀ (index : Nat) (source : CompositeType), module.types[index]? = some source →
    ∃ type : Types.DefinedType, module.definedTypes[index]? = some type ∧ type.RuntimeValid ∧
      type.expandComposite? = some (Types.embedComposite source)

variable {store : Store} {address : FuncAddr} {function : FuncInst}
  {reference : RefValue} {value : Value} {type : ValType}

theorem Store.RuntimeTypesValid.function_heap (valid : store.RuntimeTypesValid)
    (lookup : store.func? address = some function) :
    Types.HeapValid {} function.runtimeType.heap := by
  exact (valid.functions function (List.mem_of_getElem? lookup)).1.2

theorem RefValue.type?_valid (valid : store.RuntimeTypesValid)
    (found : reference.type? store = some type) :
    Types.RuntimeValValid {} (Types.embedVal type) := by
  cases reference with
  | func address =>
    obtain ⟨function, lookup, same⟩ := Option.map_eq_some_iff.mp found
    subst type
    exact .ref (valid.function_heap lookup)
  | struct_ address =>
    obtain ⟨object, lookup, same⟩ := Option.map_eq_some_iff.mp found
    subst type
    exact .ref (valid.structures object (List.mem_of_getElem? lookup)).1.2
  | array address =>
    obtain ⟨object, lookup, same⟩ := Option.map_eq_some_iff.mp found
    subst type
    exact .ref (valid.arrays object (List.mem_of_getElem? lookup)).1.2
  | null heap =>
    cases heap <;> simp only [RefValue.type?, Option.some.injEq] at found
    all_goals try { subst type; exact .ref (.abstract (by simp)) }
    all_goals try contradiction
    split at found <;> try contradiction
    all_goals simp only [Option.some.injEq] at found; subst type; exact .ref (.abstract (by simp))
  | _ =>
    simp only [RefValue.type?, Option.some.injEq] at found
    subst type
    exact .ref (.abstract (by simp))

theorem Value.type?_valid (valid : store.RuntimeTypesValid)
    (found : value.type? store = some type) :
    Types.RuntimeValValid {} (Types.embedVal type) := by
  cases value with
  | ref reference => exact reference.type?_valid valid found
  | _ =>
    simp only [Value.type?, Option.some.injEq] at found
    subst type
    exact .number (by simp [Types.embedVal])

/-- A semantic typing derivation starts from a valid actual type on the invariant domain. -/
theorem Typed.actual_valid (typed : Typed store value type) (valid : store.RuntimeTypesValid) :
    ∃ actual, value.type? store = some actual ∧
      Types.RuntimeValValid {} (Types.embedVal actual) ∧
      Types.ValMatches {} (Types.embedVal actual) (Types.embedVal type) := by
  obtain ⟨actual, found, matched⟩ := typed
  exact ⟨actual, found, value.type?_valid valid found, matched⟩

/-- Every semantically typed argument has a valid actual type on this store domain. -/
theorem ArgsTyped.actual_valid {values : List Value} {types : List ValType}
    (typed : ArgsTyped store values types) (valid : store.RuntimeTypesValid) :
    ∀ value ∈ values, ∃ actual, value.type? store = some actual ∧
      Types.RuntimeValValid {} (Types.embedVal actual) := by
  induction typed with
  | nil => simp
  | cons head tail ih =>
    intro value member
    rcases List.mem_cons.mp member with same | member
    · subst value
      obtain ⟨actual, found, validType, matched⟩ := head.actual_valid valid
      exact ⟨actual, found, validType⟩
    · exact ih value member

theorem ModuleInst.runtimeTypesCoherent_empty : ({} : ModuleInst).RuntimeTypesCoherent := by
  constructor
  · rfl
  · intro index source found
    simp at found

/-- The empty store supplies a non-vacuous base case for the invariant. -/
theorem Store.runtimeTypesValid_empty : ({} : Store).RuntimeTypesValid := by
  constructor <;> simp

/-- Either module projection yields the same valid runtime type identity. -/
theorem ModuleInst.RuntimeTypesCoherent.lookup
    {module : ModuleInst} (coherent : module.RuntimeTypesCoherent)
    {index : Nat} {source : CompositeType} {runtime : Types.DefinedType}
    (static : module.types[index]? = some source)
    (dynamic : module.definedTypes[index]? = some runtime) :
    runtime.RuntimeValid ∧
      runtime.expandComposite? = some (Types.embedComposite source) := by
  obtain ⟨type, found, valid, projection⟩ := coherent.projection index source static
  have same : type = runtime := Option.some.inj (found.symm.trans dynamic)
  subst type
  exact ⟨valid, projection⟩

#print axioms RefValue.type?_valid
#print axioms Value.type?_valid
#print axioms Typed.actual_valid
#print axioms ArgsTyped.actual_valid
#print axioms ModuleInst.RuntimeTypesCoherent.lookup

end Wasm
