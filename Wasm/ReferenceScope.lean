import Wasm.Runtime

namespace Wasm

def heapInScope (typeCount : Nat) (heap : Types.HeapType) : Bool :=
  heap.isSource && match heap with
    | .typeIdx x => x < typeCount
    | _ => true

def ValType.referencesInScope (typeCount : Nat) : ValType → Bool
  | .i32 | .i64 | .f32 | .f64 => true
  | .ref heap | .refNonNull heap => heapInScope typeCount heap

def BlockType.referencesInScope (typeCount : Nat) : BlockType → Bool
  | .val result => result.all (ValType.referencesInScope typeCount)
  | .typeIdx _ => true

mutual
  /-- Runtime reference constants are administrative values, not source constants. -/
  def Instr.referencesInScope (typeCount : Nat) : Instr → Bool
    | .const (.ref _) => false
    | .refNull heap => heapInScope typeCount heap
    | .select types => types.all (fun ts => ts.all (ValType.referencesInScope typeCount))
    | .block type body | .loop type body =>
      type.referencesInScope typeCount && instructionsInScope typeCount body
    | .if_ type yes no => type.referencesInScope typeCount &&
      instructionsInScope typeCount yes && instructionsInScope typeCount no
    | _ => true
  def instructionsInScope (typeCount : Nat) : List Instr → Bool
    | [] => true
    | instr :: rest => instr.referencesInScope typeCount && instructionsInScope typeCount rest
end

end Wasm
