import Wasm.Runtime

namespace Wasm

/-! Definite initialization effects from Wasm 3.0 validation. Structured instructions
check their bodies but do not export local initialization effects to the enclosing sequence.
https://webassembly.github.io/spec/core/valid/instructions.html -/

mutual
  def Instr.initializeLocals? (initialized : List Nat) : Instr → Option (List Nat)
    | .localGet x => if x ∈ initialized then some initialized else none
    | .localSet x | .localTee x => some (x :: initialized)
    | .block _ body | .loop _ body | .tryTable _ _ body =>
      (initializeSequence? initialized body).map fun _ => initialized
    | .if_ _ yes no => do
      let _ ← initializeSequence? initialized yes
      let _ ← initializeSequence? initialized no
      return initialized
    | _ => some initialized
  def initializeSequence? (initialized : List Nat) : List Instr → Option (List Nat)
    | [] => some initialized
    | instr :: rest => do
      let next ← instr.initializeLocals? initialized
      initializeSequence? next rest
end

def initiallyInitialized (params locals : List ValType) : List Nat :=
  List.range params.length ++
    (locals.zipIdx.filterMap fun (type, i) =>
      if type.defaultable then some (params.length + i) else none)

def Func.Initialized (function : Func) (type : FuncType) : Prop :=
  (initializeSequence? (initiallyInitialized type.params function.locals)
    function.body).isSome = true

instance (function : Func) (type : FuncType) : Decidable (function.Initialized type) := by
  unfold Func.Initialized
  infer_instance

end Wasm
