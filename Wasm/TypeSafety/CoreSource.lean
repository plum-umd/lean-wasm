import Wasm.TypeSafety.CoreSafety

namespace Wasm.TypeSafety

/-- Syntactic fragment membership, independent of source or runtime typing. -/
inductive CoreSource : Instr → Prop where
  | scalar : ScalarInstruction i → CoreSource i
  | block : (∀ i ∈ body, CoreSource i) → CoreSource (.block bt body)
  | loop : (∀ i ∈ body, CoreSource i) → CoreSource (.loop bt body)
  | if_ : (∀ i ∈ yes, CoreSource i) → (∀ i ∈ no, CoreSource i) → CoreSource (.if_ bt yes no)
  | br : CoreSource (.br x)
  | brIf : CoreSource (.brIf x)
  | brTable : CoreSource (.brTable targets fallback)
  | localGet : CoreSource (.localGet x)
  | localSet : CoreSource (.localSet x)
  | localTee : CoreSource (.localTee x)
  | call : CoreSource (.call x)
  | return_ : CoreSource .return_

private theorem CoreSource.scalar_of_plain (typed : InstrTyping i input output)
    (supported : CoreSource i) : ScalarInstruction i := by
  induction typed with
  | floatUnary | floatBinary | floatRel | floatConvert => cases supported; assumption
  | weaken _ ih => exact ih supported
  | _ => trivial

private theorem CoreSource.block_body (h : CoreSource (.block bt body)) :
    ∀ i ∈ body, CoreSource i := by
  cases h with
  | block hb => exact hb
  | scalar hs => contradiction

private theorem CoreSource.loop_body (h : CoreSource (.loop bt body)) :
    ∀ i ∈ body, CoreSource i := by
  cases h with
  | loop hb => exact hb
  | scalar hs => contradiction

private theorem CoreSource.if_bodies (h : CoreSource (.if_ bt yes no)) :
    (∀ i ∈ yes, CoreSource i) ∧ (∀ i ∈ no, CoreSource i) := by
  cases h with
  | if_ hy hn => exact ⟨hy, hn⟩
  | scalar hs => contradiction

/-- Existing structured-control source typing embeds in runtime administrative typing. -/
theorem ControlSeqTyping.toCoreTyping
    (typed : ControlSeqTyping context.types labels code input output)
    (supported : ∀ i ∈ code, CoreSource i) :
    CoreTyping store context labels (instructions code) input output := by
  revert supported
  refine ControlSeqTyping.rec
    (motive_1 := fun labels i input output _ => CoreSource i →
      CoreInstrTyping store context labels (.instr i) input output)
    (motive_2 := fun labels code input output _ => (∀ i ∈ code, CoreSource i) →
      CoreTyping store context labels (instructions code) input output)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · intro i input output labels h hs
    exact .plain h (CoreSource.scalar_of_plain h hs)
  · intro ft labels body bt ht hb ih hs
    exact .block ht (ih hs.block_body)
  · intro ft labels body bt ht hb ih hs
    exact .loop ht (ih hs.loop_body)
  · intro ft labels yes no bt ht hy hn ihy ihn hs
    exact .if_ ht (ihy hs.if_bodies.1) (ihn hs.if_bodies.2)
  · intro labels l ts input output ht hs; exact .br ht
  · intro labels l ts ht hs; exact .brIf ht
  · intro labels fallback ts targets input output hd ht hs; exact .brTable hd ht
  · intro labels i input output below h ih hs; exact .weaken (ih hs)
  · intro labels ts hs; exact .nil
  · intro labels i input middle rest output head tail ihhead ihtail hs
    exact .cons (ihhead (hs i (by simp))) (ihtail (fun i hi => hs i (by simp [hi])))
  · intro labels code input output below h ih hs; exact (ih hs).weaken

theorem ControlInstrTyping.toCoreTyping
    (typed : ControlInstrTyping context.types labels i input output) (supported : CoreSource i) :
    CoreInstrTyping store context labels (.instr i) input output := by
  have hseq : ControlSeqTyping context.types labels [i] input output := .cons typed .empty
  have hs : ∀ j ∈ [i], CoreSource j := by simpa using supported
  exact CoreTyping.single_iff.mp (by
    simpa [instructions] using ControlSeqTyping.toCoreTyping hseq hs)

/-- The existing source judgment for locals and structured bodies embeds unchanged. -/
theorem FunctionSeqTyping.toCoreTyping
    (typed : FunctionSeqTyping context.types context.locals labels code input output)
    (supported : ∀ i ∈ code, CoreSource i) :
    CoreTyping store context labels (instructions code) input output := by
  revert supported
  refine FunctionSeqTyping.rec
    (motive_1 := fun labels i input output _ => CoreSource i →
      CoreInstrTyping store context labels (.instr i) input output)
    (motive_2 := fun labels code input output _ => (∀ i ∈ code, CoreSource i) →
      CoreTyping store context labels (instructions code) input output)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ typed
  · intro labels i input output h hs; exact ControlInstrTyping.toCoreTyping h hs
  · intro x t labels ht hs; exact .localGet ht
  · intro x t labels ht hs; exact .localSet ht
  · intro x t labels ht hs; exact .localTee ht
  · intro ft labels body bt ht hb ih hs; exact .block ht (ih hs.block_body)
  · intro ft labels body bt ht hb ih hs; exact .loop ht (ih hs.loop_body)
  · intro ft labels yes no bt ht hy hn ihy ihn hs
    exact .if_ ht (ihy hs.if_bodies.1) (ihn hs.if_bodies.2)
  · intro labels i input output below h ih hs; exact .weaken (ih hs)
  · intro labels ts hs; exact .nil
  · intro labels i input middle rest output head tail ihhead ihtail hs
    exact .cons (ihhead (hs i (by simp))) (ihtail (fun i hi => hs i (by simp [hi])))
  · intro labels code input output below h ih hs; exact (ih hs).weaken

theorem FunctionInstrTyping.toCoreTyping
    (typed : FunctionInstrTyping context.types context.locals labels i input output)
    (supported : CoreSource i) : CoreInstrTyping store context labels (.instr i) input output := by
  have hseq : FunctionSeqTyping context.types context.locals labels [i] input output :=
    .cons typed .empty
  have hs : ∀ j ∈ [i], CoreSource j := by simpa using supported
  exact CoreTyping.single_iff.mp (by
    simpa [instructions] using FunctionSeqTyping.toCoreTyping hseq hs)

/-- Source control/local typing yields a safety theorem for executions of the original code. -/
theorem FunctionSeqTyping.configuration_safety
    (sourceTyped : FunctionSeqTyping context.types context.locals [] source [] output)
    (supported : ∀ i ∈ source, CoreSource i) (storeTyped : CoreStoreTyped config.store)
    (frameTyped : CoreFrameTyped config.store config.frame context)
    (returns : context.returns = none) (code : config.code = instructions source)
    (steps : ConfigSteps config next) :
    CoreConfigurationTyped next output ∧
      (FlatTerminal next.code ∨ ∃ final, ConfigStep next final) := by
  apply core_configuration_safety (steps := steps)
  refine ⟨storeTyped, context, frameTyped, returns, ?_⟩
  rw [code]
  exact FunctionSeqTyping.toCoreTyping sourceTyped supported

end Wasm.TypeSafety
