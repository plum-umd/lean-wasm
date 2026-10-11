import Wasm.TypeSafety.FlatSafety
import Wasm.CallValidation

namespace Wasm.TypeSafety

/-- A module's function index space agrees with the shared store. -/
def CoreModuleTyped (store : Store) (module : ModuleInst) (context : FunctionContext) : Prop :=
  context.types = module.types ∧ context.funcs.length = module.funcs.length ∧
    ∀ x ft, context.funcs[x]? = some ft →
      ∃ address function, module.funcAddr? x = some address ∧
        store.func? address = some function ∧ function.type = ft

/-- Every local in the integer core is initialized and has its declared type. -/
def CoreFrameTyped (store : Store) (frame : Frame) (context : FunctionContext) : Prop :=
  CoreModuleTyped store frame.module context ∧
    frame.locals.map (Option.map Value.type) = context.locals.map some ∧
    ∀ t ∈ context.locals, t.IsInteger

mutual
  /-- Runtime typing for integer operations, control, locals, and direct calls. -/
  inductive CoreInstrTyping (store : Store) :
      FunctionContext → LabelContext → AdminInstr → List ValType → List ValType → Prop where
    | plain (typed : InstrTyping i input output) (supported : ScalarInstruction i) :
        CoreInstrTyping store context labels (.instr i) input output
    | trap : CoreInstrTyping store context labels .trap input output
    | block (ht : bt.resolve context.types = some ft)
        (bodyTyped : CoreTyping store context (ft.results :: labels)
          (instructions body) ft.params ft.results) :
        CoreInstrTyping store context labels (.instr (.block bt body)) ft.params ft.results
    | loop (ht : bt.resolve context.types = some ft)
        (bodyTyped : CoreTyping store context (ft.params :: labels)
          (instructions body) ft.params ft.results) :
        CoreInstrTyping store context labels (.instr (.loop bt body)) ft.params ft.results
    | if_ (ht : bt.resolve context.types = some ft)
        (yesTyped : CoreTyping store context (ft.results :: labels)
          (instructions yes) ft.params ft.results)
        (noTyped : CoreTyping store context (ft.results :: labels)
          (instructions no) ft.params ft.results) :
        CoreInstrTyping store context labels (.instr (.if_ bt yes no))
          (ft.params ++ [.i32]) ft.results
    | br (ht : labels[x]? = some ts) :
        CoreInstrTyping store context labels (.instr (.br x)) (input ++ ts) output
    | brIf (ht : labels[x]? = some ts) :
        CoreInstrTyping store context labels (.instr (.brIf x)) (ts ++ [.i32]) ts
    | brTable (hd : labels[fallback]? = some ts)
        (ht : ∀ x ∈ targets, labels[x]? = some ts) :
        CoreInstrTyping store context labels (.instr (.brTable targets fallback))
          (input ++ ts ++ [.i32]) output
    | localGet (ht : context.locals[x]? = some t) :
        CoreInstrTyping store context labels (.instr (.localGet x)) [] [t]
    | localSet (ht : context.locals[x]? = some t) :
        CoreInstrTyping store context labels (.instr (.localSet x)) [t] []
    | localTee (ht : context.locals[x]? = some t) :
        CoreInstrTyping store context labels (.instr (.localTee x)) [t] [t]
    | call (ht : context.funcs[x]? = some ft) :
        CoreInstrTyping store context labels (.instr (.call x)) ft.params ft.results
    | return_ (ht : context.returns = some results) :
        CoreInstrTyping store context labels (.instr .return_) (input ++ results) output
    | invoke (hf : store.func? address = some function) :
        CoreInstrTyping store context labels (.invoke address function.type)
          function.type.params function.type.results
    | label (bodyTyped : CoreTyping store context (branch :: labels) body [] results)
        (continuationTyped : CoreTyping store context labels
          (instructions continuation) branch results) :
        CoreInstrTyping store context labels (.label branch.length continuation body) [] results
    | frame (frameTyped : CoreFrameTyped store state innerContext)
        (returns : innerContext.returns = some results)
        (bodyTyped : CoreTyping store innerContext [] body [] results) :
        CoreInstrTyping store context labels (.frame results.length state body) [] results
    | weaken : CoreInstrTyping store context labels i input output →
        CoreInstrTyping store context labels i (stackBelow ++ input) (stackBelow ++ output)

  inductive CoreTyping (store : Store) :
      FunctionContext → LabelContext → List AdminInstr → List ValType → List ValType → Prop where
    | nil : CoreTyping store context labels [] ts ts
    | cons : CoreInstrTyping store context labels i input middle →
        CoreTyping store context labels rest middle output →
        CoreTyping store context labels (i :: rest) input output
end

theorem CoreTyping.weaken (h : CoreTyping store context labels code input output) :
    CoreTyping store context labels code (stackBelow ++ input) (stackBelow ++ output) := by
  induction h using CoreTyping.rec (motive_1 := fun _ _ _ _ _ _ => True) with
  | nil => exact .nil
  | cons h _ _ ih => exact .cons (.weaken h) ih
  | _ => trivial

theorem CoreTyping.append (h : CoreTyping store context labels a input middle)
    (tail : CoreTyping store context labels b middle output) :
    CoreTyping store context labels (a ++ b) input output := by
  induction h using CoreTyping.rec (motive_1 := fun _ _ _ _ _ _ => True) with
  | nil => exact tail
  | cons h _ _ ih => exact .cons h (ih tail)
  | _ => trivial

theorem CoreTyping.split (h : CoreTyping store context labels (a ++ b) input output) :
    ∃ middle, CoreTyping store context labels a input middle ∧
      CoreTyping store context labels b middle output := by
  induction a generalizing input with
  | nil => exact ⟨input, .nil, h⟩
  | cons i a ih =>
    cases h with
    | cons head tail =>
      obtain ⟨middle, left, right⟩ := ih tail
      exact ⟨middle, .cons head left, right⟩

@[simp] theorem CoreTyping.nil_iff :
    CoreTyping store context labels [] input output ↔ input = output := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst output; exact .nil

@[simp] theorem CoreTyping.single_iff :
    CoreTyping store context labels [i] input output ↔
      CoreInstrTyping store context labels i input output := by
  constructor
  · intro h; cases h with
    | cons head tail => cases tail; exact head
  · intro h; exact .cons h .nil

/-- The completed flat fragment embeds without changing its typing derivations. -/
theorem FlatTyping.toCoreTyping (typed : FlatTyping code input output)
    (supported : ScalarCode code) : CoreTyping store context labels code input output := by
  induction typed with
  | nil => exact .nil
  | cons head _ ih =>
    refine .cons ?_ (ih (fun i hi => supported i (by simp [hi])))
    cases head with
    | source h => exact .plain h (supported (.instr _) (by simp))
    | trap => exact .trap

end Wasm.TypeSafety

namespace Wasm.TypeSafety

/-- Exact value-stack effect, including any number of stack weakenings. -/
theorem CoreInstrTyping.const_shape
    (h : CoreInstrTyping store context labels (.instr (.const v)) input output) :
    output = input ++ [v.type] ∧ v.type.IsNumber := by
  generalize hi : AdminInstr.instr (.const v) = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | plain h _ => cases hi; exact Wasm.TypeSafety.const_shape h
  | weaken _ ih =>
    obtain ⟨shape, hn⟩ := ih hi
    exact ⟨by simp [shape, List.append_assoc], hn⟩
  | nil | cons => trivial
  | _ => cases hi

end Wasm.TypeSafety

namespace Wasm.TypeSafety

theorem CoreInstrTyping.of_scalar
    (h : CoreInstrTyping store context labels (.instr i) input output)
    (supported : ScalarInstruction i) : InstrTyping i input output := by
  generalize hi : AdminInstr.instr i = admin at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | plain h _ => cases hi; exact h
  | weaken _ ih => exact .weaken (ih hi)
  | nil | cons => trivial
  | trap | invoke | label | frame => cases hi
  | _ => cases hi; simp [ScalarInstruction] at supported

theorem CoreTyping.toFlatTyping (typed : CoreTyping store context labels code input output)
    (supported : ScalarCode code) : FlatTyping code input output := by
  induction code generalizing input with
  | nil => cases typed; exact .nil
  | cons i rest ih =>
    cases typed with
    | cons head tail =>
      have hr : ScalarCode rest := fun j hj => supported j (by simp [hj])
      refine .cons ?_ (ih tail hr)
      have hs := supported i (by simp)
      cases i with
      | instr i => exact .source (head.of_scalar hs)
      | trap => exact .trap
      | _ => exact False.elim hs

@[simp] theorem CoreTyping.const_cons_iff :
    CoreTyping store context labels (.instr (.const v) :: rest) input output ↔
      v.type.IsNumber ∧ CoreTyping store context labels rest (input ++ [v.type]) output := by
  constructor
  · intro h
    cases h with
    | cons head tail =>
      obtain ⟨shape, hn⟩ := head.const_shape
      exact ⟨hn, shape ▸ tail⟩
  · rintro ⟨hn, tail⟩
    exact .cons (.plain (by simpa using InstrTyping.weaken (ts₀ := input) (.const hn))
      (by trivial)) tail

theorem CoreTyping.values_typed (hn : ∀ v ∈ vs, v.type.IsNumber) :
    CoreTyping store context labels (values vs) input (input ++ vs.map Value.type) := by
  induction vs generalizing input with
  | nil => simp [values]
  | cons v vs ih =>
    simp only [values, List.map_cons, CoreTyping.const_cons_iff]
    refine ⟨hn v (by simp), ?_⟩
    simpa [values, List.append_assoc] using
      ih (input := input ++ [v.type]) (fun w hw => hn w (by simp [hw]))

theorem CoreTyping.after_values
    (typed : CoreTyping store context labels (values vs ++ tail) input output) :
    CoreTyping store context labels tail (input ++ vs.map Value.type) output := by
  induction vs generalizing input with
  | nil => simpa [values] using typed
  | cons v vs ih =>
    simp only [values, List.map_cons, List.cons_append, CoreTyping.const_cons_iff] at typed
    simpa [List.append_assoc] using ih typed.2

theorem CoreTyping.values_number
    (typed : CoreTyping store context labels (values vs ++ tail) input output) :
    ∀ v ∈ vs, v.type.IsNumber := by
  induction vs generalizing input with
  | nil => simp
  | cons v vs ih =>
    simp only [values, List.map_cons, List.cons_append, CoreTyping.const_cons_iff] at typed
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact typed.1
    · exact ih typed.2 w hw

theorem CoreInstrTyping.label_shape
    (h : CoreInstrTyping store context labels (.label n continuation body) input output) :
    ∃ branch results, n = branch.length ∧ output = input ++ results ∧
      CoreTyping store context (branch :: labels) body [] results ∧
      CoreTyping store context labels (instructions continuation) branch results := by
  generalize hi : AdminInstr.label n continuation body = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | label hb hc _ _ => cases hi; exact ⟨_, _, rfl, rfl, hb, hc⟩
  | weaken _ ih =>
    obtain ⟨branch, results, hn, ho, hb, hc⟩ := ih hi
    exact ⟨branch, results, hn, by simp [ho, List.append_assoc], hb, hc⟩
  | nil | cons => trivial
  | _ => cases hi

theorem CoreInstrTyping.frame_shape
    (h : CoreInstrTyping store context labels (.frame n state body) input output) :
    ∃ innerContext results, n = results.length ∧ output = input ++ results ∧
      CoreFrameTyped store state innerContext ∧ innerContext.returns = some results ∧
      CoreTyping store innerContext [] body [] results := by
  generalize hi : AdminInstr.frame n state body = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | frame hf hr hb _ => cases hi; exact ⟨_, _, rfl, rfl, hf, hr, hb⟩
  | weaken _ ih =>
    obtain ⟨ctx, results, hn, ho, hf, hr, hb⟩ := ih hi
    exact ⟨ctx, results, hn, by simp [ho, List.append_assoc], hf, hr, hb⟩
  | nil | cons => trivial
  | _ => cases hi

theorem CoreInstrTyping.br_shape
    (h : CoreInstrTyping store context labels (.instr (.br x)) input output) :
    ∃ ts stackBelow, labels[x]? = some ts ∧ input = stackBelow ++ ts := by
  generalize hi : AdminInstr.instr (.br x) = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | br ht => cases hi; exact ⟨_, _, ht, rfl⟩
  | @weaken context labels i input output stackBelow _ ih =>
    obtain ⟨ts, below, ht, hs⟩ := ih hi
    exact ⟨ts, stackBelow ++ below, ht, by simp [hs, List.append_assoc]⟩
  | plain _ supported => cases hi; contradiction
  | nil | cons => trivial
  | _ => cases hi

theorem CoreInstrTyping.return_shape
    (h : CoreInstrTyping store context labels (.instr .return_) input output) :
    ∃ results stackBelow, context.returns = some results ∧ input = stackBelow ++ results := by
  generalize hi : AdminInstr.instr .return_ = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | return_ ht => cases hi; exact ⟨_, _, ht, rfl⟩
  | @weaken context labels i input output stackBelow _ ih =>
    obtain ⟨ts, below, ht, hs⟩ := ih hi
    exact ⟨ts, stackBelow ++ below, ht, by simp [hs, List.append_assoc]⟩
  | plain _ supported => cases hi; contradiction
  | nil | cons => trivial
  | _ => cases hi

theorem CoreInstrTyping.block_shape
    (h : CoreInstrTyping store context labels (.instr (.block bt body)) input output) :
    ∃ ft stackBelow, bt.resolve context.types = some ft ∧
      input = stackBelow ++ ft.params ∧ output = stackBelow ++ ft.results ∧
      CoreTyping store context (ft.results :: labels) (instructions body) ft.params ft.results := by
  generalize hi : AdminInstr.instr (.block bt body) = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | block ht hb _ => cases hi; exact ⟨_, [], ht, rfl, rfl, hb⟩
  | @weaken context labels i input output stackBelow _ ih =>
    obtain ⟨ft, below, ht, ha, ho, hb⟩ := ih hi
    exact ⟨ft, stackBelow ++ below, ht, by simp [ha, List.append_assoc],
      by simp [ho, List.append_assoc], hb⟩
  | plain _ supported => cases hi; contradiction
  | nil | cons => trivial
  | _ => cases hi

theorem CoreInstrTyping.loop_shape
    (h : CoreInstrTyping store context labels (.instr (.loop bt body)) input output) :
    ∃ ft stackBelow, bt.resolve context.types = some ft ∧
      input = stackBelow ++ ft.params ∧ output = stackBelow ++ ft.results ∧
      CoreTyping store context (ft.params :: labels) (instructions body) ft.params ft.results := by
  generalize hi : AdminInstr.instr (.loop bt body) = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | loop ht hb _ => cases hi; exact ⟨_, [], ht, rfl, rfl, hb⟩
  | @weaken context labels i input output stackBelow _ ih =>
    obtain ⟨ft, below, ht, ha, ho, hb⟩ := ih hi
    exact ⟨ft, stackBelow ++ below, ht, by simp [ha, List.append_assoc],
      by simp [ho, List.append_assoc], hb⟩
  | plain _ supported => cases hi; contradiction
  | nil | cons => trivial
  | _ => cases hi

theorem CoreInstrTyping.if_shape
    (h : CoreInstrTyping store context labels (.instr (.if_ bt yes no)) input output) :
    ∃ ft stackBelow, bt.resolve context.types = some ft ∧
      input = stackBelow ++ (ft.params ++ [.i32]) ∧ output = stackBelow ++ ft.results ∧
      CoreTyping store context (ft.results :: labels) (instructions yes) ft.params ft.results ∧
      CoreTyping store context (ft.results :: labels) (instructions no) ft.params ft.results := by
  generalize hi : AdminInstr.instr (.if_ bt yes no) = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | if_ ht hy hn _ _ => cases hi; exact ⟨_, [], ht, rfl, rfl, hy, hn⟩
  | @weaken context labels i input output stackBelow _ ih =>
    obtain ⟨ft, below, ht, ha, ho, hy, hn⟩ := ih hi
    exact ⟨ft, stackBelow ++ below, ht, by simp [ha, List.append_assoc],
      by simp [ho, List.append_assoc], hy, hn⟩
  | plain _ supported => cases hi; contradiction
  | nil | cons => trivial
  | _ => cases hi

theorem CoreInstrTyping.brIf_shape
    (h : CoreInstrTyping store context labels (.instr (.brIf x)) input output) :
    ∃ ts stackBelow, labels[x]? = some ts ∧
      input = stackBelow ++ (ts ++ [.i32]) ∧ output = stackBelow ++ ts := by
  generalize hi : AdminInstr.instr (.brIf x) = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | brIf ht => cases hi; exact ⟨_, [], ht, rfl, rfl⟩
  | @weaken context labels i input output stackBelow _ ih =>
    obtain ⟨ts, below, ht, ha, ho⟩ := ih hi
    exact ⟨ts, stackBelow ++ below, ht, by simp [ha, List.append_assoc],
      by simp [ho, List.append_assoc]⟩
  | plain _ supported => cases hi; contradiction
  | nil | cons => trivial
  | _ => cases hi

theorem CoreInstrTyping.brTable_shape
    (h : CoreInstrTyping store context labels (.instr (.brTable targets fallback)) input output) :
    ∃ ts stackBelow, labels[fallback]? = some ts ∧
      (∀ x ∈ targets, labels[x]? = some ts) ∧ input = stackBelow ++ ts ++ [.i32] := by
  generalize hi : AdminInstr.instr (.brTable targets fallback) = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | brTable hd ht => cases hi; exact ⟨_, _, hd, ht, rfl⟩
  | @weaken context labels i input output stackBelow _ ih =>
    obtain ⟨ts, below, hd, ht, ha⟩ := ih hi
    exact ⟨ts, stackBelow ++ below, hd, ht, by simp [ha, List.append_assoc]⟩
  | plain _ supported => cases hi; contradiction
  | nil | cons => trivial
  | _ => cases hi

theorem CoreInstrTyping.localGet_shape
    (h : CoreInstrTyping store context labels (.instr (.localGet x)) input output) :
    ∃ t stackBelow, context.locals[x]? = some t ∧
      input = stackBelow ++ [] ∧ output = stackBelow ++ [t] := by
  generalize hi : AdminInstr.instr (.localGet x) = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | localGet ht => cases hi; exact ⟨_, [], ht, rfl, rfl⟩
  | @weaken context labels i input output stackBelow _ ih =>
    obtain ⟨t, below, ht, ha, ho⟩ := ih hi
    exact ⟨t, stackBelow ++ below, ht, by simp [ha],
      by simp [ho, List.append_assoc]⟩
  | plain _ supported => cases hi; contradiction
  | nil | cons => trivial
  | _ => cases hi

theorem CoreInstrTyping.localSet_shape
    (h : CoreInstrTyping store context labels (.instr (.localSet x)) input output) :
    ∃ t stackBelow, context.locals[x]? = some t ∧
      input = stackBelow ++ [t] ∧ output = stackBelow ++ [] := by
  generalize hi : AdminInstr.instr (.localSet x) = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | localSet ht => cases hi; exact ⟨_, [], ht, rfl, rfl⟩
  | @weaken context labels i input output stackBelow _ ih =>
    obtain ⟨t, below, ht, ha, ho⟩ := ih hi
    exact ⟨t, stackBelow ++ below, ht, by simp [ha, List.append_assoc],
      by simp [ho]⟩
  | plain _ supported => cases hi; contradiction
  | nil | cons => trivial
  | _ => cases hi

theorem CoreInstrTyping.localTee_shape
    (h : CoreInstrTyping store context labels (.instr (.localTee x)) input output) :
    ∃ t stackBelow, context.locals[x]? = some t ∧
      input = stackBelow ++ [t] ∧ output = stackBelow ++ [t] := by
  generalize hi : AdminInstr.instr (.localTee x) = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | localTee ht => cases hi; exact ⟨_, [], ht, rfl, rfl⟩
  | @weaken context labels i input output stackBelow _ ih =>
    obtain ⟨t, below, ht, ha, ho⟩ := ih hi
    exact ⟨t, stackBelow ++ below, ht, by simp [ha, List.append_assoc],
      by simp [ho, List.append_assoc]⟩
  | plain _ supported => cases hi; contradiction
  | nil | cons => trivial
  | _ => cases hi

end Wasm.TypeSafety

namespace Wasm.TypeSafety

theorem CoreInstrTyping.not_handler
    (h : CoreInstrTyping store context labels (.handler catches body) input output) : False := by
  generalize hi : AdminInstr.handler catches body = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | weaken _ ih => exact ih hi
  | nil | cons => trivial
  | _ => cases hi

end Wasm.TypeSafety

namespace Wasm.TypeSafety

/-- The instruction families admitted by core runtime typing. -/
def CoreHead : AdminInstr → Prop
  | .instr i => match i with
    | .block _ _ | .loop _ _ | .if_ _ _ _ | .br _ | .brIf _ | .brTable _ _
      | .localGet _ | .localSet _ | .localTee _ | .call _ | .return_ => True
    | _ => ScalarInstruction i
  | .trap | .label _ _ _ | .frame _ _ _ | .invoke _ _ => True
  | _ => False

theorem CoreInstrTyping.head (h : CoreInstrTyping store context labels i input output) :
    CoreHead i := by
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | plain h supported =>
    rename_i i _ _ _ _
    cases i <;> simp_all [CoreHead, ScalarInstruction]
  | weaken _ ih => exact ih
  | _ => trivial

theorem CoreTyping.heads (h : CoreTyping store context labels code input output) :
    ∀ i ∈ code, CoreHead i := by
  induction code generalizing input with
  | nil => simp
  | cons i rest ih =>
    cases h with
    | cons head tail =>
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact head.head
      · exact ih tail j hj

theorem CoreInstrTyping.call_shape
    (h : CoreInstrTyping store context labels (.instr (.call x)) input output) :
    ∃ ft stackBelow, context.funcs[x]? = some ft ∧
      input = stackBelow ++ ft.params ∧ output = stackBelow ++ ft.results := by
  generalize hi : AdminInstr.instr (.call x) = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | call ht => cases hi; exact ⟨_, [], ht, rfl, rfl⟩
  | @weaken context labels i input output stackBelow _ ih =>
    obtain ⟨ft, below, ht, ha, ho⟩ := ih hi
    exact ⟨ft, stackBelow ++ below, ht, by simp [ha, List.append_assoc],
      by simp [ho, List.append_assoc]⟩
  | plain _ supported => cases hi; contradiction
  | nil | cons => trivial
  | _ => cases hi

theorem CoreInstrTyping.invoke_shape
    (h : CoreInstrTyping store context labels (.invoke address type) input output) :
    ∃ function stackBelow, store.func? address = some function ∧ type = function.type ∧
      input = stackBelow ++ function.type.params ∧
      output = stackBelow ++ function.type.results := by
  generalize hi : AdminInstr.invoke address type = i at h
  induction h using CoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | invoke hf => cases hi; exact ⟨_, [], hf, rfl, rfl, rfl⟩
  | @weaken context labels i input output stackBelow _ ih =>
    obtain ⟨function, below, hf, ht, ha, ho⟩ := ih hi
    exact ⟨function, stackBelow ++ below, hf, ht, by simp [ha, List.append_assoc],
      by simp [ho, List.append_assoc]⟩
  | nil | cons => trivial
  | _ => cases hi

end Wasm.TypeSafety

namespace Wasm.TypeSafety

@[simp] theorem CoreTyping.cons_iff :
    CoreTyping store context labels (i :: rest) input output ↔
      ∃ middle, CoreInstrTyping store context labels i input middle ∧
        CoreTyping store context labels rest middle output := by
  constructor
  · intro h; cases h with
    | cons head tail => exact ⟨_, head, tail⟩
  · rintro ⟨middle, head, tail⟩; exact .cons head tail

end Wasm.TypeSafety
