import Wasm.RuntimeTypeInvariant
import Wasm.StructValidation

/-! Declarative validity of the value types expected by runtime instructions. -/
namespace Wasm

/-- Expanded declaration fields and signatures expose valid runtime value types. -/
def ModuleInst.RuntimeExpectedTypesValid (module : ModuleInst) : Prop :=
  ∀ type ∈ module.definedTypes, ∀ comp, type.expandComposite? = some comp →
    ∀ valueType ∈ comp.valTypes, Types.RuntimeValValid {} valueType

/-- Frame declarations supply valid type identities, coherent projections, and valid fields. -/
def Frame.RuntimeTypesReady (state : Frame) : Prop :=
  state.module.RuntimeTypesCoherent ∧ state.module.RuntimeExpectedTypesValid

private theorem embed_project {type : Types.ValType} {projected : ValType}
    (found : Types.projectVal type = some projected) : Types.embedVal projected = type := by
  cases type <;> simp only [Types.projectVal] at found
  all_goals try contradiction
  all_goals try { cases found; rfl }
  rename_i nullable heap
  cases nullable <;> simp only [Option.some.injEq] at found
  all_goals subst projected; rfl

variable {state : Frame} {index fieldIndex : Nat} {type : Types.DefinedType}
  {field : Types.FieldType} {fields : List Types.FieldType} {valueType : ValType}
  {valueTypes : List ValType}

theorem Frame.RuntimeTypesReady.heap (ready : state.RuntimeTypesReady)
    (lookup : state.module.definedTypes[index]? = some type) : Types.HeapValid {} type.heap := by
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  cases static : state.module.types[index]? with
  | none =>
    have outside := List.getElem?_eq_none_iff.mp static
    have length := ready.1.length
    omega
  | some source => exact (ready.1.lookup static lookup).1.2

theorem Frame.RuntimeTypesReady.array_value (ready : state.RuntimeTypesReady)
    (lookup : state.module.definedTypes[index]? = some type)
    (expanded : type.expandComposite? = some (.array field))
    (projected : Types.projectVal field.storage.unpack = some valueType) :
    Types.RuntimeValValid {} (Types.embedVal valueType) := by
  rw [embed_project projected]
  exact ready.2 type (List.mem_of_getElem? lookup) _ expanded _ (by simp [Types.CompType.valTypes])

theorem Frame.RuntimeTypesReady.struct_values (ready : state.RuntimeTypesReady)
    (lookup : state.module.definedTypes[index]? = some type)
    (expanded : type.expandComposite? = some (.struct_ fields))
    (projected : structFieldTypes fields = some valueTypes) :
    ∀ valueType ∈ valueTypes, Types.RuntimeValValid {} (Types.embedVal valueType) := by
  intro valueType member
  have origin : ∃ field ∈ fields, Types.projectVal field.storage.unpack = some valueType := by
    clear ready lookup expanded
    induction fields generalizing valueTypes with
    | nil => simp [structFieldTypes] at projected; subst valueTypes; simp at member
    | cons field fields ih =>
      simp only [structFieldTypes, List.mapM_cons, Option.bind_eq_bind, Option.bind] at projected
      split at projected <;> try contradiction
      dsimp only at projected
      split at projected <;> try contradiction
      simp only [Option.pure_def, Option.some.injEq] at projected
      cases projected
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨field, by simp, by assumption⟩
      · obtain ⟨origin, found, same⟩ := ih (by assumption) member
        exact ⟨origin, by simp [found], same⟩
  obtain ⟨field, member, found⟩ := origin
  rw [embed_project found]
  exact ready.2 type (List.mem_of_getElem? lookup) _ expanded _
    (by simp only [Types.CompType.valTypes, List.mem_map]; exact ⟨field, member, rfl⟩)

theorem Frame.RuntimeTypesReady.struct_field (ready : state.RuntimeTypesReady)
    (lookup : state.module.definedTypes[index]? = some type)
    (expanded : type.expandComposite? = some (.struct_ fields))
    (fieldLookup : fields[fieldIndex]? = some field)
    (projected : Types.projectVal field.storage.unpack = some valueType) :
    Types.RuntimeValValid {} (Types.embedVal valueType) := by
  rw [embed_project projected]
  exact ready.2 type (List.mem_of_getElem? lookup) _ expanded _
    (by simp only [Types.CompType.valTypes, List.mem_map]
        exact ⟨field, List.mem_of_getElem? fieldLookup, rfl⟩)

/-- Structure allocation sees the same field count through either module projection. -/
theorem ModuleInst.RuntimeTypesCoherent.struct_lookup {module : ModuleInst} {index : Nat}
    {type : Types.DefinedType} {fields : List Types.FieldType}
    (coherent : module.RuntimeTypesCoherent) (lookup : module.definedTypes[index]? = some type)
    (expanded : type.expandComposite? = some (.struct_ fields)) :
    module.types[index]? = some (.struct_ fields) := by
  have bound := (List.getElem?_eq_some_iff.mp lookup).1
  cases static : module.types[index]? with
  | none =>
    have outside := List.getElem?_eq_none_iff.mp static
    have length := coherent.length
    omega
  | some source =>
    have projection := (coherent.lookup static lookup).2
    rw [expanded] at projection
    cases source <;> simp only [Types.embedComposite, Option.some.injEq] at projection
    all_goals try contradiction
    cases projection
    rfl

theorem ArgsTyped.length (typed : ArgsTyped store args types) : args.length = types.length := by
  induction typed with
  | nil => rfl
  | cons _ _ ih => simpa using congrArg Nat.succ ih

theorem structFieldTypes_length (projected : structFieldTypes fields = some types) :
    fields.length = types.length := by
  induction fields generalizing types with
  | nil => simp [structFieldTypes] at projected; subst types; rfl
  | cons field fields ih =>
    simp only [structFieldTypes, List.mapM_cons, Option.bind_eq_bind, Option.bind] at projected
    split at projected <;> try contradiction
    dsimp only at projected
    split at projected <;> try contradiction
    simp only [Option.pure_def, Option.some.injEq] at projected
    cases projected
    simpa using congrArg Nat.succ (ih (by assumption))

#print axioms Frame.RuntimeTypesReady.struct_values

end Wasm
