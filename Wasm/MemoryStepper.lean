import Wasm.Memory

namespace Wasm

abbrev CheckedMemoryStep (store : Store) (state : Frame) (es : List AdminInstr) :=
  Option { next : Store × List AdminInstr // MemoryStep store state es next.1 next.2 }

private def withMemory (store : Store) (state : Frame) (x : Nat) (es : List AdminInstr)
    (f : (address : MemAddr) → (memory : MemoryInst) →
      state.module.memAddr? x = some address → store.mem? address = some memory →
      CheckedMemoryStep store state es) : CheckedMemoryStep store state es :=
  match ha : state.module.memAddr? x with
  | none => none
  | some address => match hm : store.mem? address with
    | none => none
    | some memory => f address memory ha hm

private def memoryResult (ha : state.module.memAddr? x = some address)
    (hm : store.mem? address = some memory) (hi : memoryIndex? es = some x)
    (hr : MemoryReduces memory es change es') : CheckedMemoryStep store state es :=
  some ⟨(store.applyMemory address change, es'), .access ha hm hi hr⟩

private def checkedMemoryRedex (store : Store) (state : Frame) (es : List AdminInstr) :
    CheckedMemoryStep store state es := by
  match es with
  | [.instr (.const a), .instr (.load op x arg)] =>
    exact withMemory store state x _ fun address memory ha hm => by
      match hn : Value.address? memory.type.addrType a with
      | none => exact none
      | some n =>
        if hb : n + arg.offset + op.bytes ≤ memory.bytes.size then
          exact memoryResult ha hm rfl (.load hn hb)
        else exact memoryResult ha hm rfl (.loadTrap hn (by omega))
  | [.instr (.const a), .instr (.const v), .instr (.store op x arg)] =>
    exact withMemory store state x _ fun address memory ha hm => by
      match hn : Value.address? memory.type.addrType a with
      | none => exact none
      | some n =>
        if ht : v.type = op.type then
          if hb : n + arg.offset + op.bytes ≤ memory.bytes.size then
            exact memoryResult ha hm rfl (.store hn ht hb)
          else exact memoryResult ha hm rfl (.storeTrap hn ht (by omega))
        else exact none
  | [.instr (.memorySize x)] =>
    exact withMemory store state x _ fun _ _ ha hm => memoryResult ha hm rfl .size
  | [.instr (.const v), .instr (.memoryGrow x)] =>
    exact withMemory store state x _ fun address memory ha hm => by
      match hn : Value.address? memory.type.addrType v with
      | none => exact none
      | some delta =>
        match hg : memory.grow? delta with
        | none => exact memoryResult ha hm rfl (.growFail hn)
        | some next =>
          obtain ⟨hcan, he⟩ := MemoryInst.grow?_sound hg
          subst next
          exact memoryResult ha hm rfl (.grow hn hcan)
  | _ => exact none

private def memoryContext (vs : List Value) (tail : List AdminInstr)
    (s : CheckedMemoryStep store state es) :
    CheckedMemoryStep store state (values vs ++ es ++ tail) :=
  s.map fun next => ⟨(next.val.1, values vs ++ next.val.2 ++ tail), .context next.property⟩

def checkedMemoryStep (store : Store) (state : Frame) (es : List AdminInstr) :
    CheckedMemoryStep store state es := by
  match es with
  | .instr (.const a) :: .instr (.const v) :: .instr (.store op x arg) :: tail =>
    simpa [values] using memoryContext [] tail
      (checkedMemoryRedex store state [.instr (.const a), .instr (.const v), .instr (.store op x arg)])
  | .instr (.const a) :: .instr (.load op x arg) :: tail =>
    simpa [values] using memoryContext [] tail
      (checkedMemoryRedex store state [.instr (.const a), .instr (.load op x arg)])
  | .instr (.const v) :: .instr (.memoryGrow x) :: tail =>
    simpa [values] using memoryContext [] tail
      (checkedMemoryRedex store state [.instr (.const v), .instr (.memoryGrow x)])
  | .instr (.memorySize x) :: tail =>
    simpa [values] using memoryContext [] tail
      (checkedMemoryRedex store state [.instr (.memorySize x)])
  | .instr (.const v) :: tail =>
    simpa [values] using memoryContext [v] [] (checkedMemoryStep store state tail)
  | .label n continuation body :: tail =>
    let inner : CheckedMemoryStep store state [.label n continuation body] :=
      (checkedMemoryStep store state body).map fun next =>
        ⟨(next.val.1, [.label n continuation next.val.2]), .label next.property⟩
    simpa [values] using memoryContext [] tail inner
  | .handler catches body :: tail =>
    let inner : CheckedMemoryStep store state [.handler catches body] :=
      (checkedMemoryStep store state body).map fun next =>
        ⟨(next.val.1, [.handler catches next.val.2]), .handler next.property⟩
    simpa [values] using memoryContext [] tail inner
  | .frame n frame body :: tail =>
    let inner : CheckedMemoryStep store state [.frame n frame body] :=
      (checkedMemoryStep store frame body).map fun next =>
        ⟨(next.val.1, [.frame n frame next.val.2]), .frame next.property⟩
    simpa [values] using memoryContext [] tail inner
  | _ => exact none
termination_by sizeOf es
decreasing_by all_goals simp_wf; omega

def stepMemory (store : Store) (state : Frame) (es : List AdminInstr) :
    Option (Store × List AdminInstr) :=
  (checkedMemoryStep store state es).map Subtype.val

theorem stepMemory_sound (h : stepMemory store state es = some next) :
    MemoryStep store state es next.1 next.2 := by
  unfold stepMemory at h
  cases hs : checkedMemoryStep store state es with
  | none => simp [hs] at h
  | some s => simp [hs] at h; subst next; exact s.property

end Wasm
