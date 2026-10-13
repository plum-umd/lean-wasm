import Wasm.RuntimeMatchingCompleteness

namespace Wasm

/-! Global instances use store addresses resolved through the active module.
Mutability and value types are validation premises, not dynamic trap conditions.
https://webassembly.github.io/spec/core/exec/instructions.html#variable-instructions
-/
def ModuleInst.globalAddr? (module : ModuleInst) (index : Nat) : Option GlobalAddr :=
  module.globals[index]?

def Store.global? (store : Store) (address : GlobalAddr) : Option GlobalInst :=
  store.globals[address.index]?

def Store.resolveGlobal? (store : Store) (module : ModuleInst) (index : Nat) : Option GlobalInst :=
  (module.globalAddr? index).bind store.global?

def Store.allocateGlobal (store : Store) (global : GlobalInst) : GlobalAddr × Store :=
  (⟨store.globals.length⟩, { store with globals := store.globals ++ [global] })

theorem Store.allocateGlobal_lookup (store : Store) (global : GlobalInst) :
    (store.allocateGlobal global).2.global? (store.allocateGlobal global).1 = some global := by
  simp [Store.allocateGlobal, Store.global?]

theorem Store.allocateGlobal_preserves (store : Store) (global : GlobalInst) (address : GlobalAddr)
    (h : address.index < store.globals.length) :
    (store.allocateGlobal global).2.global? address = store.global? address := by
  simp [Store.allocateGlobal, Store.global?, List.getElem?_append, h]

def Store.setGlobal (store : Store) (address : GlobalAddr) (global : GlobalInst) : Store :=
  { store with globals := store.globals.set address.index global }

theorem Store.setGlobal_types (store : Store) (address : GlobalAddr)
    (global : GlobalInst) (value : Value) (hg : store.global? address = some global) :
    (store.setGlobal address { global with value }).globals.map GlobalInst.type =
      store.globals.map GlobalInst.type := by
  apply List.ext_getElem?
  intro i
  by_cases h : address.index = i
  · subst i
    obtain ⟨bound, he⟩ := List.getElem?_eq_some_iff.mp hg
    simp [Store.setGlobal, bound, he]
  · simp [Store.setGlobal, List.getElem?_map, List.getElem?_set_ne h]

inductive GlobalStep : Store → Frame → List AdminInstr → Store → List AdminInstr → Prop where
  | get (ha : state.module.globalAddr? x = some address)
      (hg : store.global? address = some global) :
      GlobalStep store state [.instr (.globalGet x)] store (values [global.value])
  | set (ha : state.module.globalAddr? x = some address)
      (hg : store.global? address = some global) (hv : Typed store v global.type.valType) :
      GlobalStep store state [.instr (.const v), .instr (.globalSet x)]
        (store.setGlobal address { global with value := v }) []
  | context : GlobalStep store state es store' es' →
      GlobalStep store state (values vs ++ es ++ tail) store' (values vs ++ es' ++ tail)
  | label : GlobalStep store state body store' body' →
      GlobalStep store state [.label n continuation body] store' [.label n continuation body']
  | handler : GlobalStep store state body store' body' →
      GlobalStep store state [.handler catches body] store' [.handler catches body']
  | frame : GlobalStep store inner body store' body' →
      GlobalStep store state [.frame n inner body] store' [.frame n inner body']

abbrev CheckedGlobalStep (store : Store) (state : Frame) (es : List AdminInstr) :=
  Option { next : Store × List AdminInstr // GlobalStep store state es next.1 next.2 }

def checkedGlobalStep (store : Store) (state : Frame) (es : List AdminInstr) :
    CheckedGlobalStep store state es := by
  match es with
  | .instr (.globalGet x) :: tail =>
    match ha : state.module.globalAddr? x with
    | none => exact none
    | some address =>
      match hg : store.global? address with
      | none => exact none
      | some global =>
        exact some ⟨(store, values [global.value] ++ tail), by
          simpa [values] using GlobalStep.context (vs := []) (tail := tail) (.get ha hg)⟩
  | .instr (.const v) :: .instr (.globalSet x) :: tail =>
    match ha : state.module.globalAddr? x with
    | none => exact none
    | some address =>
      match hg : store.global? address with
      | none => exact none
      | some global =>
        match checkValue store v global.type.valType with
        | none => exact none
        | some proof =>
          exact some ⟨(store.setGlobal address {global with value := v}, tail), by
            simpa [values] using GlobalStep.context (vs := []) (tail := tail)
              (.set ha hg proof.down)⟩
  | .instr (.const v) :: tail =>
    exact (checkedGlobalStep store state tail).map fun next =>
      ⟨(next.val.1, .instr (.const v) :: next.val.2), by
        simpa [values] using GlobalStep.context (vs := [v]) (tail := []) next.property⟩
  | .label n continuation body :: tail =>
    exact (checkedGlobalStep store state body).map fun next =>
      ⟨(next.val.1, .label n continuation next.val.2 :: tail), by
        simpa [values] using GlobalStep.context (vs := []) (tail := tail)
          (.label next.property)⟩
  | .handler catches body :: tail =>
    exact (checkedGlobalStep store state body).map fun next =>
      ⟨(next.val.1, .handler catches next.val.2 :: tail), by
        simpa [values] using GlobalStep.context (vs := []) (tail := tail)
          (.handler next.property)⟩
  | .frame n inner body :: tail =>
    exact (checkedGlobalStep store inner body).map fun next =>
      ⟨(next.val.1, .frame n inner next.val.2 :: tail), by
        simpa [values] using GlobalStep.context (vs := []) (tail := tail)
          (.frame next.property)⟩
  | _ => exact none
termination_by sizeOf es
decreasing_by all_goals simp_wf; omega

def stepGlobals (store : Store) (state : Frame) (es : List AdminInstr) :
    Option (Store × List AdminInstr) :=
  (checkedGlobalStep store state es).map Subtype.val

theorem stepGlobals_sound (h : stepGlobals store state es = some next) :
    GlobalStep store state es next.1 next.2 := by
  unfold stepGlobals at h
  cases hs : checkedGlobalStep store state es with
  | none => simp [hs] at h
  | some s => simp [hs] at h; subst next; exact s.property

theorem GlobalStep.functions_preserved (h : GlobalStep store state es store' es') :
    store'.funcs = store.funcs := by
  induction h with
  | get | set => rfl
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem GlobalStep.length_preserved (h : GlobalStep store state es store' es') :
    store'.globals.length = store.globals.length := by
  induction h with
  | get => rfl
  | set => simp [Store.setGlobal]
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem GlobalStep.types_preserved (h : GlobalStep store state es store' es') :
    store'.globals.map GlobalInst.type = store.globals.map GlobalInst.type := by
  induction h with
  | get => rfl
  | set _ hg _ => exact Store.setGlobal_types _ _ _ _ hg
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

theorem GlobalInst.valid_set {store : Store} {global : GlobalInst} {value : Value}
    {address : GlobalAddr} (h : Typed store value global.type.valType) :
    ({ global with value } : GlobalInst).Valid
      (store.setGlobal address { global with value }) :=
  h.store_funcs rfl rfl rfl

/-- Expected global types are valid independently of their current values. -/
def Store.GlobalTypesValid (store : Store) : Prop :=
  ∀ global ∈ store.globals, Types.RuntimeValValid {} (Types.embedVal global.type.valType)

private theorem globals_eq (store : Store) (state : Frame) (code : List AdminInstr) :
    stepGlobals store state code = match code with
    | .instr (.globalGet x) :: tail => do
      let address ← state.module.globalAddr? x
      let global ← store.global? address
      some (store, values [global.value] ++ tail)
    | .instr (.const v) :: .instr (.globalSet x) :: tail => do
      let address ← state.module.globalAddr? x
      let global ← store.global? address
      let _ ← checkValue store v global.type.valType
      some (store.setGlobal address {global with value := v}, tail)
    | .instr (.const v) :: tail =>
      (stepGlobals store state tail).map fun next => (next.1, .instr (.const v) :: next.2)
    | .label n continuation body :: tail =>
      (stepGlobals store state body).map fun next => (next.1, .label n continuation next.2 :: tail)
    | .handler catches body :: tail =>
      (stepGlobals store state body).map fun next => (next.1, .handler catches next.2 :: tail)
    | .frame n inner body :: tail =>
      (stepGlobals store inner body).map fun next => (next.1, .frame n inner next.2 :: tail)
    | _ => none := by
  cases code with
  | nil => simp [stepGlobals, checkedGlobalStep]
  | cons head tail =>
    cases head with
    | instr op =>
      cases op <;> simp only [stepGlobals, checkedGlobalStep, Option.map_map, Function.comp_def]
      all_goals try rfl
      · cases tail with
        | nil => simp only [checkedGlobalStep, Option.map_map, Function.comp_def] <;> rfl
        | cons second rest =>
          cases second with
          | instr op =>
            cases op <;> simp only [checkedGlobalStep, Option.map_map, Function.comp_def]
            all_goals try rfl
            repeat first | split | simp_all [Option.bind]
          | _ => simp only [checkedGlobalStep, Option.map_map, Function.comp_def] <;> rfl
      · repeat first | split | simp_all [Option.bind]
    | _ => simp only [stepGlobals, checkedGlobalStep, Option.map_map, Function.comp_def] <;> rfl

private theorem globals_success_tail
    (success : stepGlobals store state code = some next) (tail : List AdminInstr) :
    stepGlobals store state (code ++ tail) = some (next.1, next.2 ++ tail) := by
  induction code generalizing state next with
  | nil => rw [globals_eq] at success; contradiction
  | cons head code ih =>
    rw [globals_eq] at success ⊢
    cases head with
    | instr op =>
      cases op <;> simp only [List.cons_append] at success ⊢
      all_goals try contradiction
      · rename_i value
        cases code with
        | nil => simp only [globals_eq, Option.map_none] at success; contradiction
        | cons second rest =>
          cases second with
          | instr op =>
            cases op <;> simp only [List.cons_append] at success ⊢
            all_goals first
              | obtain ⟨inner, found, same⟩ := Option.map_eq_some_iff.mp success
                subst next
                have lifted := congrArg
                  (Option.map (fun pair => (pair.1, .instr (.const value) :: pair.2))) (ih found)
                simpa only [List.cons_append, Option.map_some] using lifted
              | simp only [Option.bind_eq_bind] at success ⊢
                repeat first | split at success | simp_all [Option.bind]
                all_goals cases success; simp
          | _ =>
            obtain ⟨inner, found, same⟩ := Option.map_eq_some_iff.mp success
            subst next
            have lifted := congrArg
              (Option.map (fun pair => (pair.1, .instr (.const value) :: pair.2))) (ih found)
            simpa only [List.cons_append, Option.map_some] using lifted
      · repeat first | split at success | simp_all [Option.bind]
        all_goals cases success; simp [List.append_assoc]
    | label _ _ _ | handler _ _ | frame _ _ _ =>
      simp only [List.cons_append] at success ⊢
      obtain ⟨inner, found, same⟩ := Option.map_eq_some_iff.mp success
      cases same
      simp [found]
    | _ => contradiction

private theorem globals_success_const (success : stepGlobals store state code = some next)
    (value : Value) : stepGlobals store state (.instr (.const value) :: code) =
      some (next.1, .instr (.const value) :: next.2) := by
  cases code with
  | nil => rw [globals_eq] at success; contradiction
  | cons head tail =>
    rw [globals_eq]
    cases head with
    | instr op =>
      cases op <;> simp only
      all_goals first
        | rw [success]; rfl
        | rw [globals_eq] at success; contradiction
    | _ => simp only; rw [success]; rfl

private theorem globals_success_prefix (success : stepGlobals store state code = some next)
    (vs : List Value) : stepGlobals store state (values vs ++ code) =
      some (next.1, values vs ++ next.2) := by
  induction vs with
  | nil => simpa [values] using success
  | cons v vs ih => simpa [values] using globals_success_const ih v

/-- Global reads and writes, in every evaluation context, are recognized exactly. -/
theorem stepGlobals_complete (step : GlobalStep store state code next code')
    (valid : store.RuntimeTypesValid) (globals : store.GlobalTypesValid) :
    stepGlobals store state code = some (next, code') := by
  induction step with
  | get ha hg => simp [globals_eq, ha, hg, values]
  | set ha hg hv =>
    have success := checkValue_complete valid
      (globals _ (List.mem_of_getElem? hg)) hv
    obtain ⟨proof, found⟩ := Option.isSome_iff_exists.mp success
    simp [globals_eq, ha, hg, found]
  | context _ ih =>
    simpa [List.append_assoc] using
      globals_success_prefix (globals_success_tail (ih valid globals) _) _
  | label _ ih | handler _ ih | frame _ ih =>
    rw [globals_eq]
    simp only [ih valid globals, Option.map_some]

#print axioms stepGlobals_complete


end Wasm
