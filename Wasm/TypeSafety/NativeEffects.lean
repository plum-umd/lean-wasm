import Wasm.TypeSafety.NativeInversion

namespace Wasm.TypeSafety

def NativeEffect (context : FunctionContext) (params results input output :
    List Wasm.Types.ValType) : Prop :=
  ∃ lower, StackMatches ⟨context.definedTypes, []⟩ input (lower ++ params) ∧
    StackMatches ⟨context.definedTypes, []⟩ (lower ++ results) output

theorem NativeEffect.weaken (h : NativeEffect context params results input output) :
    NativeEffect context params results (stackBelow ++ input) (stackBelow ++ output) := by
  obtain ⟨lower, hi, ho⟩ := h
  exact ⟨stackBelow ++ lower, by simpa only [List.append_assoc] using hi.weaken,
    by simpa only [List.append_assoc] using ho.weaken⟩

theorem NativeEffect.subtype (h : NativeEffect context params results input output)
    (hi : Wasm.Types.ResultMatches ⟨context.definedTypes, []⟩ input' input)
    (ho : Wasm.Types.ResultMatches ⟨context.definedTypes, []⟩ output output') :
    NativeEffect context params results input' output' := by
  obtain ⟨lower, hin, hout⟩ := h
  exact ⟨lower, .step hi hin, hout.trans (.step ho .refl)⟩

theorem NativeEffect.numeric (h : NativeEffect context params results input output)
    (number : ∀ t ∈ input, NativeNumber t) :
    ∃ lower, input = lower ++ params ∧
      StackMatches ⟨context.definedTypes, []⟩ (lower ++ results) output := by
  obtain ⟨lower, hi, ho⟩ := h
  exact ⟨lower, (hi.numeric number).symm, ho⟩

theorem NativeCoreInstrTyping.label_effect
    (typed : NativeCoreInstrTyping store context labels (.label n continuation body) input output) :
    ∃ (branch results : List ValType), n = branch.length ∧
      NativeCoreTyping store context (branch :: labels) body [] (results.map Wasm.Types.embedVal) ∧
      NativeCoreTyping store context labels (instructions continuation)
        (branch.map Wasm.Types.embedVal) (results.map Wasm.Types.embedVal) ∧
      NativeEffect context [] (results.map Wasm.Types.embedVal) input output := by
  generalize hi : AdminInstr.label n continuation body = admin at typed
  induction typed using NativeCoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | label hb hc ihb ihc => cases hi; exact ⟨_, _, rfl, hb, hc, [], .refl, .refl⟩
  | weaken _ ih =>
    obtain ⟨branch, results, hn, hb, hc, he⟩ := ih hi
    exact ⟨branch, results, hn, hb, hc, he.weaken⟩
  | subtype _ hin hout ih =>
    obtain ⟨branch, results, hn, hb, hc, he⟩ := ih hi
    exact ⟨branch, results, hn, hb, hc, he.subtype hin hout⟩
  | _ => first | trivial | cases hi

theorem NativeCoreInstrTyping.frame_effect
    (typed : NativeCoreInstrTyping store context labels (.frame n state body) input output) :
    ∃ (innerContext : FunctionContext) (results : List ValType),
      n = results.length ∧ CoreFrameTyped store state innerContext ∧
      innerContext.returns = some results ∧
      NativeCoreTyping store innerContext [] body [] (results.map Wasm.Types.embedVal) ∧
      NativeEffect context [] (results.map Wasm.Types.embedVal) input output := by
  generalize hi : AdminInstr.frame n state body = admin at typed
  induction typed using NativeCoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | frame hf hr hb ih => cases hi; exact ⟨_, _, rfl, hf, hr, hb, [], .refl, .refl⟩
  | weaken _ ih =>
    obtain ⟨inner, results, hn, hf, hr, hb, he⟩ := ih hi
    exact ⟨inner, results, hn, hf, hr, hb, he.weaken⟩
  | subtype _ hin hout ih =>
    obtain ⟨inner, results, hn, hf, hr, hb, he⟩ := ih hi
    exact ⟨inner, results, hn, hf, hr, hb, he.subtype hin hout⟩
  | _ => first | trivial | cases hi

theorem NativeCoreInstrTyping.invoke_effect
    (typed : NativeCoreInstrTyping store context labels (.invoke address type) input output) :
    ∃ function, store.func? address = some function ∧ type = function.type ∧
      NativeEffect context (function.type.params.map Wasm.Types.embedVal)
        (function.type.results.map Wasm.Types.embedVal) input output := by
  generalize hi : AdminInstr.invoke address type = admin at typed
  induction typed using NativeCoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | invoke hf => cases hi; exact ⟨_, hf, rfl, [], .refl, .refl⟩
  | weaken _ ih =>
    obtain ⟨function, hf, ht, he⟩ := ih hi
    exact ⟨function, hf, ht, he.weaken⟩
  | subtype _ hin hout ih =>
    obtain ⟨function, hf, ht, he⟩ := ih hi
    exact ⟨function, hf, ht, he.subtype hin hout⟩
  | _ => first | trivial | cases hi

theorem NativeCoreTyping.heads
    (typed : NativeCoreTyping store context labels code input output) :
    ∀ i ∈ code, CoreHead i := by
  induction code generalizing input with
  | nil => simp
  | cons i rest ih =>
    obtain ⟨middle, head, tail⟩ := NativeCoreTyping.cons_iff.mp typed
    intro admin ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact head.head
    · exact ih tail admin ha

theorem native_numbers_append {a b : List Wasm.Types.ValType} (left : ∀ t ∈ a, NativeNumber t)
    (right : ∀ t ∈ b, NativeNumber t) : ∀ t ∈ a ++ b, NativeNumber t := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · exact left t ht
  · exact right t ht

theorem native_value_numbers {vs : List Value} (number : ∀ v ∈ vs, v.type.IsNumber) :
    ∀ t ∈ (vs.map Value.type).map Wasm.Types.embedVal, NativeNumber t := by
  apply native_numbers_map
  intro t ht
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ht
  exact number v hv

theorem NativeSourceTyping.localGet_effect
    (typed : NativeSourceTyping store context labels (.localGet x) input output) :
    ∃ t, context.locals[x]? = some t ∧
      NativeEffect context [] [Wasm.Types.embedVal t] input output := by
  generalize hi : Instr.localGet x = i at typed
  induction typed with
  | exact h =>
    cases hi
    obtain ⟨t, lower, ht, hin, hout⟩ := h.localGet_shape
    exact ⟨t, ht, lower.map Wasm.Types.embedVal,
      by simp only [hin, List.map_append, List.map_nil]; exact .refl,
      by simp only [hout, List.map_append, List.map_cons, List.map_nil]; exact .refl⟩
  | weaken _ ih => obtain ⟨t, ht, he⟩ := ih hi; exact ⟨t, ht, he.weaken⟩
  | subtype _ hin hout ih =>
    obtain ⟨t, ht, he⟩ := ih hi; exact ⟨t, ht, he.subtype hin hout⟩
  | _ => cases hi

theorem NativeSourceTyping.localSet_effect
    (typed : NativeSourceTyping store context labels (.localSet x) input output) :
    ∃ t, context.locals[x]? = some t ∧
      NativeEffect context [Wasm.Types.embedVal t] [] input output := by
  generalize hi : Instr.localSet x = i at typed
  induction typed with
  | exact h =>
    cases hi
    obtain ⟨t, lower, ht, hin, hout⟩ := h.localSet_shape
    exact ⟨t, ht, lower.map Wasm.Types.embedVal,
      by simp only [hin, List.map_append, List.map_cons, List.map_nil]; exact .refl,
      by simp only [hout, List.map_append, List.map_nil]; exact .refl⟩
  | weaken _ ih => obtain ⟨t, ht, he⟩ := ih hi; exact ⟨t, ht, he.weaken⟩
  | subtype _ hin hout ih =>
    obtain ⟨t, ht, he⟩ := ih hi; exact ⟨t, ht, he.subtype hin hout⟩
  | _ => cases hi

theorem NativeSourceTyping.localTee_effect
    (typed : NativeSourceTyping store context labels (.localTee x) input output) :
    ∃ t, context.locals[x]? = some t ∧
      NativeEffect context [Wasm.Types.embedVal t] [Wasm.Types.embedVal t] input output := by
  generalize hi : Instr.localTee x = i at typed
  induction typed with
  | exact h =>
    cases hi
    obtain ⟨t, lower, ht, hin, hout⟩ := h.localTee_shape
    exact ⟨t, ht, lower.map Wasm.Types.embedVal,
      by simp only [hin, List.map_append, List.map_cons, List.map_nil]; exact .refl,
      by simp only [hout, List.map_append, List.map_cons, List.map_nil]; exact .refl⟩
  | weaken _ ih => obtain ⟨t, ht, he⟩ := ih hi; exact ⟨t, ht, he.weaken⟩
  | subtype _ hin hout ih =>
    obtain ⟨t, ht, he⟩ := ih hi; exact ⟨t, ht, he.subtype hin hout⟩
  | _ => cases hi

theorem NativeSourceTyping.call_effect
    (typed : NativeSourceTyping store context labels (.call x) input output) :
    ∃ ft, context.funcs[x]? = some ft ∧ NativeEffect context
      (ft.params.map Wasm.Types.embedVal) (ft.results.map Wasm.Types.embedVal) input output := by
  generalize hi : Instr.call x = i at typed
  induction typed with
  | exact h =>
    cases hi
    obtain ⟨ft, lower, ht, hin, hout⟩ := h.call_shape
    exact ⟨ft, ht, lower.map Wasm.Types.embedVal,
      by simp only [hin, List.map_append]; exact .refl,
      by simp only [hout, List.map_append]; exact .refl⟩
  | weaken _ ih => obtain ⟨ft, ht, he⟩ := ih hi; exact ⟨ft, ht, he.weaken⟩
  | subtype _ hin hout ih =>
    obtain ⟨ft, ht, he⟩ := ih hi; exact ⟨ft, ht, he.subtype hin hout⟩
  | _ => cases hi

theorem NativeSourceTyping.block_effect
    (typed : NativeSourceTyping store context labels (.block bt body) input output) :
    ∃ ft, bt.resolve context.types = some ft ∧
      NativeCoreTyping store context (ft.results :: labels) (instructions body)
        (ft.params.map Wasm.Types.embedVal) (ft.results.map Wasm.Types.embedVal) ∧
      NativeEffect context (ft.params.map Wasm.Types.embedVal)
        (ft.results.map Wasm.Types.embedVal) input output := by
  generalize hi : Instr.block bt body = i at typed
  induction typed with
  | exact h =>
    cases hi
    obtain ⟨ft, lower, ht, hin, hout, hb⟩ := h.block_shape
    exact ⟨ft, ht, hb.toNativeCoreTyping, lower.map Wasm.Types.embedVal,
      by simp only [hin, List.map_append]; exact .refl,
      by simp only [hout, List.map_append]; exact .refl⟩
  | block ht hb => cases hi; exact ⟨_, ht, hb, [], .refl, .refl⟩
  | weaken _ ih => obtain ⟨ft, ht, hb, he⟩ := ih hi; exact ⟨ft, ht, hb, he.weaken⟩
  | subtype _ hin hout ih =>
    obtain ⟨ft, ht, hb, he⟩ := ih hi; exact ⟨ft, ht, hb, he.subtype hin hout⟩
  | _ => cases hi

theorem NativeSourceTyping.loop_effect
    (typed : NativeSourceTyping store context labels (.loop bt body) input output) :
    ∃ ft, bt.resolve context.types = some ft ∧
      NativeCoreTyping store context (ft.params :: labels) (instructions body)
        (ft.params.map Wasm.Types.embedVal) (ft.results.map Wasm.Types.embedVal) ∧
      NativeEffect context (ft.params.map Wasm.Types.embedVal)
        (ft.results.map Wasm.Types.embedVal) input output := by
  generalize hi : Instr.loop bt body = i at typed
  induction typed with
  | exact h =>
    cases hi
    obtain ⟨ft, lower, ht, hin, hout, hb⟩ := h.loop_shape
    exact ⟨ft, ht, hb.toNativeCoreTyping, lower.map Wasm.Types.embedVal,
      by simp only [hin, List.map_append]; exact .refl,
      by simp only [hout, List.map_append]; exact .refl⟩
  | loop ht hb => cases hi; exact ⟨_, ht, hb, [], .refl, .refl⟩
  | weaken _ ih => obtain ⟨ft, ht, hb, he⟩ := ih hi; exact ⟨ft, ht, hb, he.weaken⟩
  | subtype _ hin hout ih =>
    obtain ⟨ft, ht, hb, he⟩ := ih hi; exact ⟨ft, ht, hb, he.subtype hin hout⟩
  | _ => cases hi

theorem NativeSourceTyping.if_effect
    (typed : NativeSourceTyping store context labels (.if_ bt yes no) input output) :
    ∃ ft, bt.resolve context.types = some ft ∧
      NativeCoreTyping store context (ft.results :: labels) (instructions yes)
        (ft.params.map Wasm.Types.embedVal) (ft.results.map Wasm.Types.embedVal) ∧
      NativeCoreTyping store context (ft.results :: labels) (instructions no)
        (ft.params.map Wasm.Types.embedVal) (ft.results.map Wasm.Types.embedVal) ∧
      NativeEffect context ((ft.params ++ [ValType.i32]).map Wasm.Types.embedVal)
        (ft.results.map Wasm.Types.embedVal) input output := by
  generalize hi : Instr.if_ bt yes no = i at typed
  induction typed with
  | exact h =>
    cases hi
    obtain ⟨ft, lower, ht, hin, hout, hy, hn⟩ := h.if_shape
    exact ⟨ft, ht, hy.toNativeCoreTyping, hn.toNativeCoreTyping, lower.map Wasm.Types.embedVal,
      by simp only [hin, List.map_append]; exact .refl,
      by simp only [hout, List.map_append]; exact .refl⟩
  | if_ ht hy hn => cases hi; exact ⟨_, ht, hy, hn, [], .refl, .refl⟩
  | weaken _ ih =>
    obtain ⟨ft, ht, hy, hn, he⟩ := ih hi; exact ⟨ft, ht, hy, hn, he.weaken⟩
  | subtype _ hin hout ih =>
    obtain ⟨ft, ht, hy, hn, he⟩ := ih hi; exact ⟨ft, ht, hy, hn, he.subtype hin hout⟩
  | _ => cases hi

theorem NativeSourceTyping.brIf_effect
    (typed : NativeSourceTyping store context labels (.brIf x) input output) :
    ∃ ts, labels[x]? = some ts ∧ NativeEffect context
      ((ts ++ [ValType.i32]).map Wasm.Types.embedVal)
      (ts.map Wasm.Types.embedVal) input output := by
  generalize hi : Instr.brIf x = i at typed
  induction typed with
  | exact h =>
    cases hi
    obtain ⟨ts, lower, ht, hin, hout⟩ := h.brIf_shape
    exact ⟨ts, ht, lower.map Wasm.Types.embedVal,
      by simp only [hin, List.map_append]; exact .refl,
      by simp only [hout, List.map_append]; exact .refl⟩
  | weaken _ ih => obtain ⟨ts, ht, he⟩ := ih hi; exact ⟨ts, ht, he.weaken⟩
  | subtype _ hin hout ih =>
    obtain ⟨ts, ht, he⟩ := ih hi; exact ⟨ts, ht, he.subtype hin hout⟩
  | _ => cases hi

theorem NativeSourceTyping.brTable_target
    (typed : NativeSourceTyping store context labels (.brTable targets fallback) input output)
    (number : ∀ t ∈ input, NativeNumber t) (target : x ∈ fallback :: targets) :
    ∃ ts lower, labels[x]? = some ts ∧
      input = lower ++ ts.map Wasm.Types.embedVal ++ [.i32] := by
  generalize hi : Instr.brTable targets fallback = i at typed
  induction typed with
  | exact h =>
    cases hi
    obtain ⟨ts, lower, hd, ht, hin⟩ := h.brTable_shape
    refine ⟨ts, lower.map Wasm.Types.embedVal, ?_, by simp [hin, Wasm.Types.embedVal]⟩
    rcases List.mem_cons.mp target with rfl | hx
    · exact hd
    · exact ht x hx
  | brTable ht =>
    cases hi
    rename_i arguments lower out
    obtain ⟨ts, hx, matching⟩ := ht x target
    have he := native_results_match_numeric matching (fun t h => number t (by simp [h]))
    refine ⟨ts, lower, hx, ?_⟩
    rw [he]
    exact (List.append_assoc _ _ _).symm
  | @weaken i input output below _ ih =>
    obtain ⟨ts, lower, ht, hin⟩ := ih (fun t h => number t (by simp [h])) hi
    exact ⟨ts, below ++ lower, ht, by simp [hin, List.append_assoc]⟩
  | subtype _ hin hout ih =>
    have equal := native_results_match_numeric hin number
    rw [← equal] at number ⊢
    exact ih number hi
  | _ => cases hi

end Wasm.TypeSafety
