import Wasm.Fast.Runtime
import Wasm.Fast.BulkMemory

namespace Wasm.Fast


abbrev CheckedBulkStep (store : Store) (state : Frame) (es : List AdminInstr) :=
  Option { next : Store × List AdminInstr // BulkStep store state es next.1 next.2 }

private def bulkResult (h : BulkReduces store state es store' es') :
    CheckedBulkStep store state es := some ⟨(store', es'), .redex h⟩

private def checkedBulkRedex (store : Store) (state : Frame) (es : List AdminInstr) :
    CheckedBulkStep store state es := by
  match es with
  | [.instr (.const a), .instr (.const v), .instr (.const len), .instr (.memoryFill x)] =>
    match hm : store.resolveMem? state.module x with
    | none => exact none
    | some memory =>
      match hi : Value.address? memory.type.addrType a,
          hn : Value.address? memory.type.addrType len with
      | some i, some n =>
        if hv : v.type = .i32 then
          if hb : i + n ≤ memory.bytes.size then
            exact bulkResult (.fill hm hi hv hn hb)
          else exact bulkResult (.fillTrap hm hi hv hn (by omega))
        else exact none
      | _, _ => exact none
  | [.instr (.const a), .instr (.const b), .instr (.const len), .instr (.memoryCopy x y)] =>
    match hd : store.resolveMem? state.module x, hs : store.resolveMem? state.module y with
    | some dst, some src =>
      match hi : Value.address? dst.type.addrType a, hj : Value.address? src.type.addrType b,
          hn : Value.address? (dst.type.addrType.minAddress src.type.addrType) len with
      | some i, some j, some n =>
        if hb : i + n ≤ dst.bytes.size ∧ j + n ≤ src.bytes.size then
          exact bulkResult (.copy hd hs hi hj hn hb)
        else exact bulkResult (.copyTrap hd hs hi hj hn (by omega))
      | _, _, _ => exact none
    | _, _ => exact none
  | [.instr (.const a), .instr (.const b), .instr (.const len), .instr (.memoryInit x y)] =>
    match hm : store.resolveMem? state.module x, hd : store.resolveData? state.module y with
    | some memory, some data =>
      match hi : Value.address? memory.type.addrType a, hj : Value.address? .i32 b,
          hn : Value.address? .i32 len with
      | some i, some j, some n =>
        if hb : i + n ≤ memory.bytes.size ∧ j + n ≤ data.bytes.size then
          exact bulkResult (.init hm hd hi hj hn hb)
        else exact bulkResult (.initTrap hm hd hi hj hn (by omega))
      | _, _, _ => exact none
    | _, _ => exact none
  | [.instr (.dataDrop y)] =>
    match ha : state.module.dataAddr? y with
    | none => exact none
    | some address =>
      match hd : store.data? address with
      | none => exact none
      | some data => exact bulkResult (.drop ha hd)
  | _ => exact none

private def bulkContext (vs : List Value) (tail : List AdminInstr)
    (s : CheckedBulkStep store state es) :
    CheckedBulkStep store state (values vs ++ es ++ tail) :=
  s.map fun next => ⟨(next.val.1, values vs ++ next.val.2 ++ tail), .context next.property⟩

def checkedBulkStep (store : Store) (state : Frame) (es : List AdminInstr) :
    CheckedBulkStep store state es := by
  match es with
  | .instr (.const a) :: .instr (.const b) :: .instr (.const c) :: .instr op :: tail =>
    match checkedBulkRedex store state (values [a, b, c] ++ [.instr op]) with
    | some next =>
      simpa [values] using bulkContext [] tail (some next)
    | none =>
      simpa [values] using bulkContext [a] []
        (checkedBulkStep store state (.instr (.const b) :: .instr (.const c) :: .instr op :: tail))
  | .instr (.dataDrop y) :: tail =>
    simpa [values] using bulkContext [] tail (checkedBulkRedex store state [.instr (.dataDrop y)])
  | .instr (.const v) :: tail =>
    simpa [values] using bulkContext [v] [] (checkedBulkStep store state tail)
  | .label n continuation body :: tail =>
    let inner : CheckedBulkStep store state [.label n continuation body] :=
      (checkedBulkStep store state body).map fun next =>
        ⟨(next.val.1, [.label n continuation next.val.2]), .label next.property⟩
    simpa [values] using bulkContext [] tail inner
  | .handler catches body :: tail =>
    let inner : CheckedBulkStep store state [.handler catches body] :=
      (checkedBulkStep store state body).map fun next =>
        ⟨(next.val.1, [.handler catches next.val.2]), .handler next.property⟩
    simpa [values] using bulkContext [] tail inner
  | .frame n frame body :: tail =>
    let inner : CheckedBulkStep store state [.frame n frame body] :=
      (checkedBulkStep store frame body).map fun next =>
        ⟨(next.val.1, [.frame n frame next.val.2]), .frame next.property⟩
    simpa [values] using bulkContext [] tail inner
  | _ => exact none
termination_by sizeOf es
decreasing_by all_goals simp_wf; omega

def stepBulkMemory (store : Store) (state : Frame) (es : List AdminInstr) :
    Option (Store × List AdminInstr) := (checkedBulkStep store state es).map Subtype.val

theorem stepBulkMemory_sound (h : stepBulkMemory store state es = some next) :
    BulkStep store state es next.1 next.2 := by
  unfold stepBulkMemory at h
  cases hs : checkedBulkStep store state es with
  | none => simp [hs] at h
  | some s => simp [hs] at h; subst next; exact s.property

end Wasm.Fast
