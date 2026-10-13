import Wasm.VectorWidths

open Lean Elab Tactic

private partial def stringTests (expression : Expr) : List Expr :=
  let here := if expression.isAppOf ``String.startsWith || expression.isAppOf ``String.endsWith || expression.isAppOf ``BEq.beq then
    if expression.hasFVar || expression.hasMVar || expression.hasLooseBVars then [] else [expression]
    else []
  here ++ match expression with
    | .app f a => stringTests f ++ stringTests a
    | .lam _ t b _ | .forallE _ t b _ => stringTests t ++ stringTests b
    | .letE _ t v b _ => stringTests t ++ stringTests v ++ stringTests b
    | .mdata _ e | .proj _ _ e => stringTests e
    | _ => []

elab "closed_string_tests" : tactic => withMainContext do
  let mut expressions := stringTests (← getMainTarget)
  for declaration in ← getLCtx do
    expressions := expressions ++ stringTests declaration.type
  for expression in expressions.eraseDups do
    if !(← Meta.isDefEq (← Meta.inferType expression) (mkConst ``Bool)) then continue
    let term ← PrettyPrinter.delab expression
    evalTactic (← `(tactic| first
      | have : $term = true := by decide +kernel
      | have : $term = false := by decide +kernel))

namespace Wasm.VectorProofs

def memoryOpcode (opcode : VectorOpcode) : Bool :=
  opcode.name.startsWith "v128.load" || opcode.name.startsWith "v128.store"

/-- The finite opcode classification is checked by Lean's kernel. -/
theorem isMemory_eq (opcode : VectorOpcode) : opcode.isMemory = memoryOpcode opcode := rfl

end Wasm.VectorProofs
