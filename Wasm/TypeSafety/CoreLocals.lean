import Wasm.TypeSafety.CorePreservation

namespace Wasm.TypeSafety

/-- Static local lookup retrieves an initialized runtime value of exactly that type. -/
theorem CoreFrameTyped.get {x : Nat} {t : ValType} (typed : CoreFrameTyped store frame context)
    (ht : context.locals[x]? = some t) :
    ∃ v : Value, frame.locals[x]? = some (some v) ∧ v.type = t ∧ t.IsInteger := by
  have hmap := congrArg (fun xs => xs[x]?) typed.2.1
  simp only [List.getElem?_map, ht, Option.map_some] at hmap
  have hi := typed.2.2 t (List.mem_of_getElem? ht)
  cases he : frame.locals[x]? with
  | none => simp [he] at hmap
  | some entry =>
    cases entry with
    | none => simp [he] at hmap
    | some v =>
      simp only [he, Option.map_some, Option.some.injEq] at hmap
      exact ⟨v, rfl, hmap, hi⟩

private theorem list_set_same {α : Type} {xs : List α} {x : Nat} {a : α}
    (h : xs[x]? = some a) : xs.set x a = xs := by
  induction xs generalizing x with
  | nil => simp at h
  | cons b rest ih =>
    cases x with
    | zero => simp at h; subst a; rfl
    | succ x => simpa using ih (by simpa using h)

/-- Assigning a value of the declared type preserves initialization and local typing. -/
theorem CoreFrameTyped.set {x : Nat} {t : ValType} {v : Value}
    (typed : CoreFrameTyped store frame context) (ht : context.locals[x]? = some t)
    (hv : v.type = t) :
    CoreFrameTyped store { frame with locals := frame.locals.set x (some v) } context := by
  refine ⟨typed.1, ?_, typed.2.2⟩
  change (frame.locals.set x (some v)).map (Option.map Value.type) = context.locals.map some
  rw [List.map_set, typed.2.1]
  apply list_set_same
  simp [List.getElem?_map, ht, hv]

/-- Local reductions preserve code typing and the caller's initialized local invariant. -/
theorem LocalStep.preserves_core (step : LocalStep frame code nextFrame next)
    (frameTyped : CoreFrameTyped store frame context)
    (typed : CoreTyping store context labels code input output) :
    CoreFrameTyped store nextFrame context ∧ CoreTyping store context labels next input output := by
  induction step generalizing context labels input output with
  | get lookup =>
    obtain ⟨t, below, ht, hi, ho⟩ :=
      (CoreTyping.single_iff.mp typed).localGet_shape
    obtain ⟨v, hv, he, hint⟩ := frameTyped.get ht
    have eqValue := Option.some.inj (lookup.symm.trans hv)
    cases eqValue
    simp only [List.append_nil] at hi
    refine ⟨frameTyped, ?_⟩
    rw [ho, ← hi, ← he]
    apply CoreTyping.values_typed
    intro w hw
    simp only [List.mem_singleton] at hw
    subst w
    rw [he]
    cases t <;> simp_all [ValType.IsInteger, ValType.IsNumber]
  | @set state x v bound =>
    simp only [CoreTyping.const_cons_iff, CoreTyping.single_iff] at typed
    obtain ⟨_, hop⟩ := typed
    obtain ⟨t, below, ht, hi, ho⟩ := hop.localSet_shape
    have hl := congrArg List.length hi
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    obtain ⟨hbelow, he⟩ := List.append_inj hi (by omega)
    have he := List.singleton_inj.mp he
    refine ⟨frameTyped.set ht he, ?_⟩
    simp only [List.append_nil] at ho
    rw [ho, ← hbelow]; exact .nil
  | @tee state v x =>
    simp only [CoreTyping.const_cons_iff, CoreTyping.single_iff] at typed
    obtain ⟨hn, hop⟩ := typed
    obtain ⟨t, below, ht, hi, ho⟩ := hop.localTee_shape
    have hl := congrArg List.length hi
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    obtain ⟨hbelow, he⟩ := List.append_inj hi (by omega)
    have he := List.singleton_inj.mp he
    refine ⟨frameTyped, ?_⟩
    rw [ho, ← hbelow, ← he]
    apply CoreTyping.const_cons_iff.mpr
    refine ⟨hn, CoreTyping.const_cons_iff.mpr ⟨hn, ?_⟩⟩
    apply CoreTyping.single_iff.mpr
    have hs := CoreInstrTyping.weaken (stackBelow := input ++ [v.type])
      (CoreInstrTyping.localSet (store := store) (labels := labels) ht)
    simpa [he] using hs
  | context _ ih =>
    obtain ⟨middle, left, right⟩ := typed.split
    obtain ⟨last, valuesTyped, body⟩ := left.split
    obtain ⟨hf, hb⟩ := ih frameTyped body
    exact ⟨hf, (valuesTyped.append hb).append right⟩
  | label _ ih =>
    obtain ⟨branch, results, hn, ho, hb, hc⟩ :=
      (CoreTyping.single_iff.mp typed).label_shape
    obtain ⟨hf, hb⟩ := ih frameTyped hb
    refine ⟨hf, ?_⟩
    rw [hn, ho]
    apply CoreTyping.single_iff.mpr
    simpa using CoreInstrTyping.weaken (stackBelow := input) (.label hb hc)
  | handler =>
    exact False.elim (CoreTyping.single_iff.mp typed).not_handler
  | frame _ ih =>
    obtain ⟨innerContext, results, hn, ho, hf, hr, hb⟩ :=
      (CoreTyping.single_iff.mp typed).frame_shape
    obtain ⟨hf, hb⟩ := ih hf hb
    refine ⟨frameTyped, ?_⟩
    rw [hn, ho]
    apply CoreTyping.single_iff.mpr
    simpa using CoreInstrTyping.weaken (stackBelow := input) (.frame hf hr hb)

end Wasm.TypeSafety
