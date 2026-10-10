import Wasm.Tables

namespace Wasm

abbrev CheckedTableStep (store : Store) (state : Frame) (es : List AdminInstr) :=
  Option { next : Store × List AdminInstr // TableStep store state es next.1 next.2 }

private def tableResult (h : TableReduces store state es store' es') :
    CheckedTableStep store state es := some ⟨(store', es'), .redex h⟩

private def checkedTableRedex (store : Store) (state : Frame) (es : List AdminInstr) :
    CheckedTableStep store state es := by
  match es with
  | [.instr (.const a), .instr (.tableGet x)] =>
    match ht : store.resolveTable? state.module x with
    | none => exact none
    | some table =>
      match hi : Value.address? table.type.addrType a with
      | none => exact none
      | some i =>
        if hb : i < table.refs.size then exact tableResult (.get ht hi hb)
        else exact tableResult (.getTrap ht hi (by omega))
  | [.instr (.const a), .instr (.const (.ref reference)), .instr (.tableSet x)] =>
    match ha : state.module.tableAddr? x with
    | none => exact none
    | some address =>
      match ht : store.table? address with
      | none => exact none
      | some table =>
        match hi : Value.address? table.type.addrType a with
        | none => exact none
        | some i =>
          if hv : (checkValue store (.ref reference) table.type.refType).isSome = true then
            if hb : i < table.refs.size then exact tableResult (.set ha ht hi (checkValue_sound hv) hb)
            else
              exact tableResult (.setTrap (by simp [Store.resolveTable?, ha, ht]) hi (checkValue_sound hv) (by omega))
          else exact none
  | [.instr (.tableSize x)] =>
    match ht : store.resolveTable? state.module x with
    | none => exact none
    | some table => exact tableResult (.size ht)
  | [.instr (.const (.ref reference)), .instr (.const len), .instr (.tableGrow x)] =>
    match ha : state.module.tableAddr? x with
    | none => exact none
    | some address =>
      match ht : store.table? address with
      | none => exact none
      | some table =>
        match hn : Value.address? table.type.addrType len with
        | none => exact none
        | some n =>
          if hv : (checkValue store (.ref reference) table.type.refType).isSome = true then
            if hg : table.CanGrow n then
              if table.refs.size + n ≤ tableGrowthBudget then
                exact tableResult (.grow ha ht hn (checkValue_sound hv) hg)
              else exact tableResult (.growFailure (by simp [Store.resolveTable?, ha, ht]) hn (checkValue_sound hv))
            else exact tableResult (.growFailure (by simp [Store.resolveTable?, ha, ht]) hn (checkValue_sound hv))
          else exact none
  | [.instr (.const a), .instr (.const v), .instr (.const len), .instr (.tableFill x)] =>
    match hm : store.resolveTable? state.module x with
    | none => exact none
    | some table =>
      match hi : Value.address? table.type.addrType a,
          hn : Value.address? table.type.addrType len with
      | some i, some n =>
        if hv : (checkValue store v table.type.refType).isSome = true then
          if hb : i + n ≤ table.refs.size then
            exact tableResult (.fill hm hi (checkValue_sound hv) hn hb)
          else exact tableResult (.fillTrap hm hi (checkValue_sound hv) hn (by omega))
        else exact none
      | _, _ => exact none
  | [.instr (.const a), .instr (.const b), .instr (.const len), .instr (.tableCopy x y)] =>
    match hd : store.resolveTable? state.module x, hs : store.resolveTable? state.module y with
    | some dst, some src =>
      match hi : Value.address? dst.type.addrType a, hj : Value.address? src.type.addrType b,
          hn : Value.address? (dst.type.addrType.minAddress src.type.addrType) len with
      | some i, some j, some n =>
        if hb : i + n ≤ dst.refs.size ∧ j + n ≤ src.refs.size then
          exact tableResult (.copy hd hs hi hj hn hb)
        else exact tableResult (.copyTrap hd hs hi hj hn (by omega))
      | _, _, _ => exact none
    | _, _ => exact none
  | [.instr (.const a), .instr (.const b), .instr (.const len), .instr (.tableInit x y)] =>
    match hm : store.resolveTable? state.module x, hd : store.resolveElem? state.module y with
    | some table, some element =>
      match hi : Value.address? table.type.addrType a, hj : Value.address? .i32 b,
          hn : Value.address? .i32 len with
      | some i, some j, some n =>
        if hb : i + n ≤ table.refs.size ∧ j + n ≤ element.refs.size then
          exact tableResult (.init hm hd hi hj hn hb)
        else exact tableResult (.initTrap hm hd hi hj hn (by omega))
      | _, _, _ => exact none
    | _, _ => exact none
  | [.instr (.elemDrop y)] =>
    match ha : state.module.elemAddr? y with
    | none => exact none
    | some address =>
      match hd : store.elem? address with
      | none => exact none
      | some element => exact tableResult (.drop ha hd)
  | _ => exact none

private def tableContext (vs : List Value) (tail : List AdminInstr)
    (s : CheckedTableStep store state es) :
    CheckedTableStep store state (values vs ++ es ++ tail) :=
  s.map fun next => ⟨(next.val.1, values vs ++ next.val.2 ++ tail), .context next.property⟩

def checkedTableStep (store : Store) (state : Frame) (es : List AdminInstr) :
    CheckedTableStep store state es := by
  match es with
  | .instr (.const a) :: .instr (.const b) :: .instr (.const c) :: .instr op :: tail =>
    match checkedTableRedex store state (values [a, b, c] ++ [.instr op]) with
    | some next =>
      simpa [values] using tableContext [] tail (some next)
    | none =>
      simpa [values] using tableContext [a] []
        (checkedTableStep store state (.instr (.const b) :: .instr (.const c) :: .instr op :: tail))
  | .instr (.const a) :: .instr (.const b) :: .instr op :: tail =>
    match checkedTableRedex store state (values [a, b] ++ [.instr op]) with
    | some next => simpa [values] using tableContext [] tail (some next)
    | none =>
      simpa [values] using tableContext [a] []
        (checkedTableStep store state (.instr (.const b) :: .instr op :: tail))
  | .instr (.const a) :: .instr op :: tail =>
    match checkedTableRedex store state (values [a] ++ [.instr op]) with
    | some next => simpa [values] using tableContext [] tail (some next)
    | none =>
      simpa [values] using tableContext [a] []
        (checkedTableStep store state (.instr op :: tail))
  | .instr (.tableSize x) :: tail =>
    simpa [values] using tableContext [] tail
      (checkedTableRedex store state [.instr (.tableSize x)])
  | .instr (.elemDrop y) :: tail =>
    simpa [values] using tableContext [] tail
      (checkedTableRedex store state [.instr (.elemDrop y)])
  | .instr (.const v) :: tail =>
    simpa [values] using tableContext [v] [] (checkedTableStep store state tail)
  | .label n continuation body :: tail =>
    let inner : CheckedTableStep store state [.label n continuation body] :=
      (checkedTableStep store state body).map fun next =>
        ⟨(next.val.1, [.label n continuation next.val.2]), .label next.property⟩
    simpa [values] using tableContext [] tail inner
  | .frame n frame body :: tail =>
    let inner : CheckedTableStep store state [.frame n frame body] :=
      (checkedTableStep store frame body).map fun next =>
        ⟨(next.val.1, [.frame n frame next.val.2]), .frame next.property⟩
    simpa [values] using tableContext [] tail inner
  | _ => exact none
termination_by sizeOf es
decreasing_by all_goals simp_wf; omega

def stepTables (store : Store) (state : Frame) (es : List AdminInstr) :
    Option (Store × List AdminInstr) := (checkedTableStep store state es).map Subtype.val

theorem stepTables_sound (h : stepTables store state es = some next) :
    TableStep store state es next.1 next.2 := by
  unfold stepTables at h
  cases hs : checkedTableStep store state es with
  | none => simp [hs] at h
  | some s => simp [hs] at h; subst next; exact s.property

end Wasm
