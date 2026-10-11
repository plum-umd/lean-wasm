import Wasm.Runtime

namespace Wasm

def heapInScope (typeCount : Nat) (heap : Types.HeapType) : Bool :=
  heap.isSource && match heap with
    | .typeIdx x => x < typeCount
    | _ => true

def ValType.referencesInScope (typeCount : Nat) : ValType → Bool
  | .i32 | .i64 | .f32 | .f64 | .v128 => true
  | .ref heap | .refNonNull heap => heapInScope typeCount heap

def BlockType.referencesInScope (typeCount : Nat) : BlockType → Bool
  | .val result => result.all (ValType.referencesInScope typeCount)
  | .typeIdx _ => true

mutual
  /-- Runtime reference constants are administrative values, not source constants. -/
  def Instr.referencesInScope (typeCount : Nat) : Instr → Bool
    | .arrayOp op =>
      let indices := match op with
        | .len => []
        | .copy x y => [x, y]
        | .new_ x _ | .newFixed x _ | .newData x _ | .newElem x _ | .get x _ |
            .set x | .fill x | .initData x _ | .initElem x _ => [x]
      indices.all (fun x => x < typeCount)
    | .const (.ref _) => false
    | .structNew x _ | .structGet x _ _ | .structSet x _ |
        .callRef x | .returnCallRef x => x < typeCount
    | .refNull heap | .refTest _ heap | .refCast _ heap => heapInScope typeCount heap
    | .brOnCast _ _ source target =>
      heapInScope typeCount source.heap && heapInScope typeCount target.heap
    | .select types => types.all (fun ts => ts.all (ValType.referencesInScope typeCount))
    | .block type body | .loop type body | .tryTable type _ body =>
      type.referencesInScope typeCount && instructionsInScope typeCount body
    | .if_ type yes no => type.referencesInScope typeCount &&
      instructionsInScope typeCount yes && instructionsInScope typeCount no
    | _ => true
  def instructionsInScope (typeCount : Nat) : List Instr → Bool
    | [] => true
    | instr :: rest => instr.referencesInScope typeCount && instructionsInScope typeCount rest
end

end Wasm
