import Wasm.Reduction
import Wasm.IntegerReduction
import Wasm.FrameReduction
import Wasm.Locals

/-!
Structured control rules from WebAssembly 3.0, including administrative label reduction.
https://webassembly.github.io/spec/core/exec/instructions.html#control-instructions
The function-only type context abstracts block-type resolution; activations use their own module.
-/

namespace Wasm

open AdminInstr Instr

/-- Local structured-control rules. Value lists use specification (bottom-to-top) order. -/
inductive ControlReduces (types : TypeContext) : List AdminInstr → List AdminInstr → Prop where
  | block (ht : bt.resolve types = some ft) (ha : args.length = ft.params.length) :
      ControlReduces types (values args ++ [instr (.block bt body)])
        [.label ft.results.length [] (values args ++ instructions body)]
  | loop (ht : bt.resolve types = some ft) (ha : args.length = ft.params.length) :
      ControlReduces types (values args ++ [instr (.loop bt body)])
        [.label ft.params.length [.loop bt body] (values args ++ instructions body)]
  | ifZero : ControlReduces types
      [instr (.const (.i32 0)), instr (.if_ bt yes no)] [instr (.block bt no)]
  | ifNonzero (h : c ≠ 0) : ControlReduces types
      [instr (.const (.i32 c)), instr (.if_ bt yes no)] [instr (.block bt yes)]
  | brIfZero : ControlReduces types [instr (.const (.i32 0)), instr (.brIf l)] []
  | brIfNonzero (h : c ≠ 0) : ControlReduces types
      [instr (.const (.i32 c)), instr (.brIf l)] [instr (.br l)]
  | brTableHit (h : targets[c.toNat]? = some l) : ControlReduces types
      [instr (.const (.i32 c)), instr (.brTable targets fallback)] [instr (.br l)]
  | brTableDefault (h : targets.length ≤ c.toNat) : ControlReduces types
      [instr (.const (.i32 c)), instr (.brTable targets fallback)] [instr (.br fallback)]
  | labelDone : ControlReduces types [.label n continuation (values vs)] (values vs)
  | labelTrap : ControlReduces types [.label n continuation [.trap]] [.trap]
  | returnLabel : ControlReduces types
      [.label n continuation (values vs ++ [.instr .return_] ++ tail)]
      (values vs ++ [.instr .return_])
  | brZero (h : results.length = n) : ControlReduces types
      [.label n continuation (values discarded ++ values results ++ [instr (.br 0)] ++ tail)]
      (values results ++ instructions continuation)
  | brSucc : ControlReduces types
      [.label n continuation (values vs ++ [instr (.br (l + 1))] ++ tail)]
      (values vs ++ [instr (.br l)])

/-- Nested evaluation contexts do not reduce a label's continuation before a branch. -/
inductive ExecStep : TypeContext → List AdminInstr → List AdminInstr → Prop where
  | primitive : Reduces es es' → ExecStep types es es'
  | integer : IntegerReduces es es' → ExecStep types es es'
  | activation : FrameReduces es es' → ExecStep types es es'
  | control : ControlReduces types es es' → ExecStep types es es'
  | context : ExecStep types es es' →
      ExecStep types (values vs ++ es ++ tail) (values vs ++ es' ++ tail)
  | label : ExecStep types body body' →
      ExecStep types [.label n continuation body] [.label n continuation body']
  | handler : ExecStep types body body' →
      ExecStep types [.handler catches body] [.handler catches body']
  | frame : ExecStep state.module.types body body' →
      ExecStep types [.frame n state body] [.frame n state body']
  | localFrame : LocalStep state body state' body' →
      ExecStep types [.frame n state body] [.frame n state' body']
  | trap (h : values vs ++ [.trap] ++ tail ≠ [.trap]) :
      ExecStep types (values vs ++ [.trap] ++ tail) [.trap]

inductive ExecSteps (types : TypeContext) : List AdminInstr → List AdminInstr → Prop where
  | refl : ExecSteps types es es
  | cons : ExecStep types es middle → ExecSteps types middle result → ExecSteps types es result

/-- Existing flat reductions remain valid in the extended semantics. -/
theorem Step.toExecStep (h : Step es es') : ExecStep types es es' := by
  cases h with
  | context h => exact .context (.primitive h)
  | trap h => exact .trap h

theorem Steps.toExecSteps (h : Steps es es') : ExecSteps types es es' := by
  induction h with
  | refl => exact .refl
  | cons h _ ih => exact .cons h.toExecStep ih

theorem ExecSteps.trans (h₁ : ExecSteps types a b) (h₂ : ExecSteps types b c) :
    ExecSteps types a c := by
  induction h₁ with
  | refl => exact h₂
  | cons h _ ih => exact .cons h (ih h₂)

theorem ExecSteps.inLabel (h : ExecSteps types body body') :
    ExecSteps types [.label n continuation body] [.label n continuation body'] := by
  induction h with
  | refl => exact .refl
  | cons h _ ih => exact .cons (.label h) ih

theorem ExecSteps.inContext (h : ExecSteps types es es') :
    ExecSteps types (values vs ++ es ++ tail) (values vs ++ es' ++ tail) := by
  induction h with
  | refl => exact .refl
  | cons h _ ih => exact .cons (.context h) ih

end Wasm
