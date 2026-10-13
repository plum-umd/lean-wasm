import Wasm.NativeExecution
import Wasm.ExecutionCompletenessAudit

namespace Wasm.Tests
open Types

private def recursiveStruct : HeapType :=
  .defined [.struct_ true [] [⟨.val (.ref true (.recIdx 0)), false⟩]] 0

private def structHierarchy : RecType :=
  [.struct_ false [] [], .struct_ false [.recIdx 0] [], .struct_ true [.recIdx 1] []]

example : (checkHeapValid 32 {} recursiveStruct).isSome = true := by decide +kernel
example : (checkHeapValid 32 {} (.defined structHierarchy 2)).isSome = true := by
  decide +kernel
example : (checkHeapValid 32 {} (.defined structHierarchy 3)).isSome = false := by
  decide +kernel
example : (checkHeapValid 32 {} (.defined [] 0)).isSome = false := by decide +kernel
example : (checkHeapValid 32 {} (.defined [.struct_ false [.recIdx 0] []] 0)).isSome =
    false := by decide +kernel
example : (checkHeapValid 32 {} (.defined
    [.struct_ true [] [], .struct_ true [.recIdx 0] []] 1)).isSome = false := by
  decide +kernel
example : (checkHeapValid 32 {} (.defined
    [.struct_ false [] [], .func true [.recIdx 0] [] []] 1)).isSome = false := by
  decide +kernel
example : (checkHeapValid 32 {} (.defined [.struct_ true []
    [⟨.val (.ref true (.recIdx 1)), false⟩]] 0)).isSome = false := by decide +kernel
example : (checkHeapValid 32 {} (.defined [.struct_ true [.any, .eq] []] 0)).isSome =
    false := by decide +kernel
example : Algorithm.heapMatches 32 {recs := structHierarchy} (.recIdx 2) (.recIdx 0) =
    true := by decide +kernel
example : (checkHeapValid 0 {} recursiveStruct).isSome = false := by decide +kernel

private def arrayFrame : Frame :=
  {module := {
    types := [.array (.mk (.val .i32) true)]
    definedTypes := [⟨[.array true [] (.mk (.val .i32) true)], 0⟩]}}

private def arrayCode (count : Nat) : List AdminInstr :=
  values [.i32 0, .i32 (BitVec.ofNat 32 count)] ++ [.instr (.arrayOp (.new_ 0 false))]

private def overLimit : RunStatus := .resourceLimit (.arrayElements 1048577 1048576)

example : arrayResourceLimit? {} arrayFrame (arrayCode 1048575) = none := by decide +kernel
example : arrayResourceLimit? {} arrayFrame (arrayCode 1048576) = none := by decide +kernel
example : arrayResourceLimit? {} arrayFrame (arrayCode 1048577) =
    some (.arrayElements 1048577 1048576) := by decide +kernel
example : (runConfiguration 1 ⟨{}, arrayFrame, arrayCode 2⟩).status = .finished
    [.ref (.array ⟨0⟩)] := by decide +kernel
example : (runConfiguration 1 ⟨{}, arrayFrame,
    values [.i32 42] ++ [.label 0 [] [.handler []
      [.frame 0 arrayFrame (arrayCode 1048577)]]] ++ [.instr .nop]⟩).status =
    overLimit := by decide +kernel
example : (runConfiguration 0 ⟨{}, arrayFrame, arrayCode 1048577⟩).status = overLimit := by
  decide +kernel
#eval (do
  unless (Native.run 1 ⟨{}, arrayFrame, arrayCode 1048577⟩).status == overLimit do
    throw (IO.userError "native runner lost the array resource-limit outcome") : IO Unit)
example : (runConfiguration 1 ⟨{}, arrayFrame,
    [.instr (.const (.i32 1048577)), .instr (.arrayOp (.new_ 0 false))]⟩).status =
    .stuck := by decide +kernel
example : arrayResourceLimit? {} arrayFrame
    ([.instr .nop] ++ arrayCode 1048577) = none := by decide +kernel
example : arrayResourceLimit? {} arrayFrame
    (values [.i32 0] ++ [.label 0 []
      [ .instr (.const (.i32 1048577)), .instr (.arrayOp (.new_ 0 false))]]) = none := by
  decide +kernel

-- Out-of-bounds data allocation traps before the resource guard; missing segments are stuck.
private def dataStore : Store := {datas := [⟨#[]⟩]}
private def dataFrame : Frame := {arrayFrame with module.datas := [⟨0⟩]}
private def dataCode : List AdminInstr :=
  values [.i32 0, .i32 1048577] ++ [.instr (.arrayOp (.newData 0 0))]
example : (runConfiguration 1 ⟨dataStore, dataFrame, dataCode⟩).status = .trapped := by
  decide +kernel
example : (runConfiguration 1 ⟨{}, arrayFrame, dataCode⟩).status = .stuck := by decide +kernel
example : (runConfiguration 1 ⟨{}, arrayFrame, arrayCode 1048577⟩).state =
    ⟨{}, arrayFrame, arrayCode 1048577⟩ := by
  have stopped : stepConfiguration ⟨{}, arrayFrame, arrayCode 1048577⟩ = none := by
    decide +kernel
  exact runConfiguration_stopped_state stopped

#print axioms checkHeapValid_sound
#print axioms runConfiguration_sound
#print axioms runConfiguration_finished
#print axioms runConfiguration_trapped
end Wasm.Tests
