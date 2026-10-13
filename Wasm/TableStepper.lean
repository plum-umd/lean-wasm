import Wasm.Tables
import Wasm.FamilyScanner
import Wasm.RuntimeMatchingCompleteness

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

private def tableOperands : Frame → AdminInstr → Option Nat
  | _, .instr (.tableGet _) => some 1
  | _, .instr (.tableSet _) | _, .instr (.tableGrow _) => some 2
  | _, .instr (.tableFill _) | _, .instr (.tableCopy _ _) | _, .instr (.tableInit _ _) => some 3
  | _, .instr (.tableSize _) | _, .instr (.elemDrop _) => some 0
  | _, _ => none

private def tableScanner : FamilyScanner :=
  ⟨tableOperands, fun store state op args =>
    (checkedTableRedex store state (values args ++ [op])).map Subtype.val⟩

private theorem table_family (step : FamilyStep
    (fun store state op args next code => TableStep store state (values args ++ [op]) next code)
    store state code next code') : TableStep store state code next code' := by
  induction step with
  | redex reduced => exact reduced
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

private theorem tableScanner_sound (success : tableScanner.scan store state code [] = some next) :
    TableStep store state code next.1 next.2 := by
  apply table_family
  have localSound : ∀ store state op args next,
      tableScanner.reduce store state op args = some next →
      TableStep store state (values args ++ [op]) next.1 next.2 := by
    intro store state op args next found
    obtain ⟨checked, lookup, same⟩ := Option.map_eq_some_iff.mp found
    cases same
    exact checked.property
  simpa [values] using tableScanner.scan_sound localSound success

def checkedTableStep (store : Store) (state : Frame) (code : List AdminInstr) :
    CheckedTableStep store state code :=
  match found : tableScanner.scan store state code [] with
  | none => none
  | some next => some ⟨next, tableScanner_sound found⟩

def stepTables (store : Store) (state : Frame) (es : List AdminInstr) :
    Option (Store × List AdminInstr) := (checkedTableStep store state es).map Subtype.val

theorem stepTables_sound (h : stepTables store state es = some next) :
    TableStep store state es next.1 next.2 := by
  unfold stepTables at h
  cases hs : checkedTableStep store state es with
  | none => simp [hs] at h
  | some s => simp [hs] at h; subst next; exact s.property

/-- Table reference types are valid independently of the elements currently stored in the table. -/
def Store.TableTypesValid (store : Store) : Prop :=
  ∀ table ∈ store.tables, Types.RuntimeValValid {} (Types.embedVal table.type.refType)

private theorem resolved_table_mem {store : Store} {module : ModuleInst} {x : Nat}
    {table : TableInst} (lookup : store.resolveTable? module x = some table) :
    table ∈ store.tables := by
  obtain ⟨address, found, lookup⟩ := Option.bind_eq_some_iff.mp lookup
  exact List.mem_of_getElem? lookup

private theorem table_redex_complete (reduced : TableReduces store state code next code')
    (valid : store.RuntimeTypesValid) (tables : store.TableTypesValid) :
    (checkedTableRedex store state code).isSome = true := by
  have directChecks {table : TableInst} {value : Value} {address : TableAddr}
      (lookup : store.table? address = some table) (typed : Typed store value table.type.refType) :=
    checkValue_complete valid (tables table (List.mem_of_getElem? lookup)) typed
  have resolvedChecks {table : TableInst} {value : Value} {x : Nat}
      (lookup : store.resolveTable? state.module x = some table)
      (typed : Typed store value table.type.refType) :=
    checkValue_complete valid (tables table (resolved_table_mem lookup)) typed
  cases reduced
  case' set ha ht hi hv hb => have valueSuccess := directChecks ht hv
  case' setTrap ht hi hv hb => have valueSuccess := resolvedChecks ht hv
  case' grow ha ht hn hv hg => have valueSuccess := directChecks ht hv
  case' growFailure ht hn hv => have valueSuccess := resolvedChecks ht hv
  case' fill hm hi hv hn hb => have valueSuccess := resolvedChecks hm hv
  case' fillTrap hm hi hv hn hb => have valueSuccess := resolvedChecks hm hv
  all_goals simp only [values, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, checkedTableRedex]
  all_goals repeat first
    | simp_all [tableResult, Store.resolveTable?]
    | split
  all_goals subst_vars
  all_goals simp_all

private def TableLocal (store : Store) (state : Frame) (op : AdminInstr) (args : List Value)
    (next : Store) (code : List AdminInstr) : Prop :=
  op.ScannerAtom ∧ tableOperands state op = some args.length ∧
    TableReduces store state (values args ++ [op]) next code

private theorem TableStep.toFamily (step : TableStep store state code next code') :
    FamilyStep TableLocal store state code next code' := by
  induction step with
  | redex reduced =>
    cases reduced
    all_goals first
      | refine FamilyStep.redex (args := [_, _, _]) (op := .instr _) ?_
      | refine FamilyStep.redex (args := [_, _]) (op := .instr _) ?_
      | refine FamilyStep.redex (args := [_]) (op := .instr _) ?_
      | refine FamilyStep.redex (args := []) (op := .instr _) ?_
    all_goals refine ⟨by trivial, rfl, ?_⟩
    all_goals constructor <;> assumption
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

/-- Table progress is complete on valid runtime types, allowing either growth outcome. -/
theorem stepTables_complete (reduced : TableStep store state code next code')
    (valid : store.RuntimeTypesValid) (tables : store.TableTypesValid) :
    (stepTables store state code).isSome = true := by
  have localComplete : ∀ state op args next code, TableLocal store state op args next code →
      op.ScannerAtom ∧ tableScanner.operands state op = some args.length ∧
        (tableScanner.reduce store state op args).isSome = true := by
    intro state op args next code reduced
    obtain ⟨atom, arity, hr⟩ := reduced
    exact ⟨atom, arity, by simpa [tableScanner] using table_redex_complete hr valid tables⟩
  have success := tableScanner.step_complete localComplete reduced.toFamily
  unfold FamilyScanner.step at success
  unfold stepTables checkedTableStep
  split <;> rename_i found
  · simp [found] at success
  · simp

#print axioms stepTables_complete

end Wasm
