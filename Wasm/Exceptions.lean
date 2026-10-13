import Wasm.RuntimeExpectedTypesInvariant
import Wasm.RuntimeMatchingCompleteness
import Wasm.ContextualScanner

namespace Wasm

/-! Exception allocation, ordered catch selection, and unwinding from Wasm 3.0.
https://webassembly.github.io/spec/core/exec/instructions.html#exception-handling -/

inductive CatchOutcome (state : Frame) (address : ExnAddr) (exception : ExnInst) :
    List Catch → List AdminInstr → Prop where
  | empty : CatchOutcome state address exception [] [.throwing address]
  | hit (ht : state.module.tags[x]? = some exception.tag) :
      CatchOutcome state address exception (.tag x d reference :: rest)
        (values (exception.fields ++ if reference then [.ref (.exn address)] else []) ++
          [.instr (.br d)])
  | miss (ht : state.module.tags[x]? = some tag) (hne : tag ≠ exception.tag)
      (next : CatchOutcome state address exception rest code) :
      CatchOutcome state address exception (.tag x d reference :: rest) code
  | all : CatchOutcome state address exception (.all d reference :: rest)
      (values (if reference then [.ref (.exn address)] else []) ++ [.instr (.br d)])

private def selectCatch (state : Frame) (address : ExnAddr) (exception : ExnInst) :
    (catches : List Catch) →
      Option { code : List AdminInstr // CatchOutcome state address exception catches code }
  | [] => some ⟨_, .empty⟩
  | .tag x d reference :: rest => by
    match ht : state.module.tags[x]? with
    | none => exact none
    | some tag =>
      if he : tag = exception.tag then
        exact some ⟨_, .hit (he ▸ ht)⟩
      else exact (selectCatch state address exception rest).map fun next =>
        ⟨next.val, .miss ht he next.property⟩
  | .all _ _ :: _ => some ⟨_, .all⟩

inductive ExceptionStep : Store → Frame → List AdminInstr → Store → List AdminInstr → Prop where
  | enter (ht : bt.resolve state.module.types = some ft) (ha : args.length = ft.params.length) :
      ExceptionStep store state (values args ++ [.instr (.tryTable bt catches body)]) store
        [.handler catches [.label ft.results.length [] (values args ++ instructions body)]]
  | throw_ (ht : state.module.tags[x]? = some address)
      (hs : store.tags[address.index]? = some tag) (ha : ArgsTyped store args tag.type.params) :
      ExceptionStep store state (values args ++ [.instr (.throw_ x)])
        {store with exns := store.exns ++ [⟨address, args⟩]}
        [.throwing ⟨store.exns.length⟩]
  | throwRef (he : store.exns[address.index]? = some exception) :
      ExceptionStep store state [.instr (.const (.ref (.exn address))), .instr .throwRef] store
        [.throwing address]
  | throwNull : ExceptionStep store state
      [.instr (.const (.ref (.null heap))), .instr .throwRef] store [.trap]
  | discard (nonempty : (discarded.isEmpty && tail.isEmpty) ≠ true) :
      ExceptionStep store state (values discarded ++ [.throwing address] ++ tail)
      store [.throwing address]
  | labelThrow : ExceptionStep store state [.label n continuation [.throwing address]]
      store [.throwing address]
  | frameThrow : ExceptionStep store state [.frame n inner [.throwing address]]
      store [.throwing address]
  | caught (he : store.exns[address.index]? = some exception)
      (hc : CatchOutcome state address exception catches code) :
      ExceptionStep store state [.handler catches [.throwing address]] store code
  | done : ExceptionStep store state [.handler catches (values vs)] store (values vs)
  | trap : ExceptionStep store state [.handler catches [.trap]] store [.trap]
  | return_ : ExceptionStep store state
      [.handler catches (values vs ++ [.instr .return_] ++ tail)] store
      (values vs ++ [.instr .return_])
  | branch : ExceptionStep store state
      [.handler catches (values vs ++ [.instr (.br d)] ++ tail)] store
      (values vs ++ [.instr (.br d)])
  | context : ExceptionStep store state code store' code' →
      ExceptionStep store state (values vs ++ code ++ tail) store' (values vs ++ code' ++ tail)
  | label : ExceptionStep store state body store' body' →
      ExceptionStep store state [.label n continuation body] store' [.label n continuation body']
  | handler : ExceptionStep store state body store' body' →
      ExceptionStep store state [.handler catches body] store' [.handler catches body']
  | frame : ExceptionStep store inner body store' body' →
      ExceptionStep store state [.frame n inner body] store' [.frame n inner body']

private inductive ExceptionRedex : Store → Frame → List AdminInstr → Store → List AdminInstr → Prop where
  | enter (ht : bt.resolve state.module.types = some ft) (ha : args.length = ft.params.length) :
      ExceptionRedex store state (values args ++ [.instr (.tryTable bt catches body)]) store
        [.handler catches [.label ft.results.length [] (values args ++ instructions body)]]
  | throw_ (ht : state.module.tags[x]? = some address)
      (hs : store.tags[address.index]? = some tag) (ha : ArgsTyped store args tag.type.params) :
      ExceptionRedex store state (values args ++ [.instr (.throw_ x)])
        {store with exns := store.exns ++ [⟨address, args⟩]}
        [.throwing ⟨store.exns.length⟩]
  | throwRef (he : store.exns[address.index]? = some exception) :
      ExceptionRedex store state [.instr (.const (.ref (.exn address))), .instr .throwRef] store
        [.throwing address]
  | throwNull : ExceptionRedex store state
      [.instr (.const (.ref (.null heap))), .instr .throwRef] store [.trap]
  | discard (nonempty : (discarded.isEmpty && tail.isEmpty) ≠ true) :
      ExceptionRedex store state (values discarded ++ [.throwing address] ++ tail)
      store [.throwing address]
  | labelThrow : ExceptionRedex store state [.label n continuation [.throwing address]]
      store [.throwing address]
  | frameThrow : ExceptionRedex store state [.frame n inner [.throwing address]]
      store [.throwing address]
  | caught (he : store.exns[address.index]? = some exception)
      (hc : CatchOutcome state address exception catches code) :
      ExceptionRedex store state [.handler catches [.throwing address]] store code
  | done : ExceptionRedex store state [.handler catches (values vs)] store (values vs)
  | trap : ExceptionRedex store state [.handler catches [.trap]] store [.trap]
  | return_ : ExceptionRedex store state
      [.handler catches (values vs ++ [.instr .return_] ++ tail)] store
      (values vs ++ [.instr .return_])
  | branch : ExceptionRedex store state
      [.handler catches (values vs ++ [.instr (.br d)] ++ tail)] store
      (values vs ++ [.instr (.br d)])

private theorem ExceptionStep.contextual (h : ExceptionStep store state code next code') :
    ContextualStep ExceptionRedex store state code next code' := by
  induction h with
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih
  | enter ht ha => exact .redex (.enter ht ha)
  | throw_ ht hs ha => exact .redex (.throw_ ht hs ha)
  | throwRef he => exact .redex (.throwRef he)
  | throwNull => exact .redex .throwNull
  | discard hn => exact .redex (.discard hn)
  | labelThrow => exact .redex .labelThrow
  | frameThrow => exact .redex .frameThrow
  | caught he hc => exact .redex (.caught he hc)
  | done => exact .redex .done
  | trap => exact .redex .trap
  | @return_ _ _ catches vs suffix => exact .redex .return_
  | @branch _ _ catches vs suffix d => exact .redex .branch

private abbrev CheckedExceptionStep (store : Store) (state : Frame) (code : List AdminInstr) :=
  Option { next : Store × List AdminInstr // ExceptionStep store state code next.1 next.2 }

private def exceptionContext (vs : List Value) (tail : List AdminInstr)
    (next : CheckedExceptionStep store state code) :
    CheckedExceptionStep store state (values vs ++ code ++ tail) :=
  next.map fun next =>
    ⟨(next.val.1, values vs ++ next.val.2 ++ tail), .context next.property⟩

private structure Prefix (code : List AdminInstr) where
  values : List Value
  rest : List AdminInstr
  reconstruct : code = Wasm.values values ++ rest

private def splitPrefix : (code : List AdminInstr) → Prefix code
  | .instr (.const v) :: tail =>
    let p := splitPrefix tail
    ⟨v :: p.values, p.rest, by simp [values, p.reconstruct]⟩
  | code => ⟨[], code, rfl⟩

private def checkedExceptionLeaf (store : Store) (state : Frame) (op : AdminInstr)
    (stack : List Value) (tail : List AdminInstr) :
    CheckedExceptionStep store state (values stack ++ op :: tail) := by
  match op with
  | .instr (.tryTable bt catches body) =>
    match ht : bt.resolve state.module.types with
    | none => exact none
    | some ft =>
      let n := ft.params.length
      if hn : n ≤ stack.length then
        let below := stack.take (stack.length - n)
        let args := stack.drop (stack.length - n)
        have split : stack = below ++ args := (List.take_append_drop _ _).symm
        have arity : args.length = ft.params.length := by simp [args, n] at *; omega
        exact some ⟨(store, values below ++ [.handler catches
          [.label ft.results.length [] (values args ++ instructions body)]] ++ tail), by
          simpa [split, values, List.map_append, List.append_assoc] using
            ExceptionStep.context (vs := below) (tail := tail) (ExceptionStep.enter ht arity)⟩
      else exact none
  | .instr (.throw_ x) =>
    match ht : state.module.tags[x]? with
    | none => exact none
    | some address =>
      match hs : store.tags[address.index]? with
      | none => exact none
      | some tag =>
        let n := tag.type.params.length
        if hn : n ≤ stack.length then
          let below := stack.take (stack.length - n)
          let args := stack.drop (stack.length - n)
          match checkArgs store args tag.type.params with
          | none => exact none
          | some typed =>
            have split : stack = below ++ args := (List.take_append_drop _ _).symm
            exact some ⟨({store with exns := store.exns ++ [⟨address, args⟩]},
              values below ++ [.throwing ⟨store.exns.length⟩] ++ tail), by
              simpa [split, values, List.map_append, List.append_assoc] using
                ExceptionStep.context (vs := below) (tail := tail)
                  (ExceptionStep.throw_ ht hs typed.down)⟩
        else exact none
  | .instr .throwRef =>
    match hs : stack.reverse with
    | .ref (.null heap) :: rest =>
      have split : stack = rest.reverse ++ [.ref (.null heap)] := by
        simpa using congrArg List.reverse hs
      exact some ⟨(store, values rest.reverse ++ [.trap] ++ tail), by
        simpa [split, values, List.map_append, List.append_assoc] using
          ExceptionStep.context (vs := rest.reverse) (tail := tail) ExceptionStep.throwNull⟩
    | .ref (.exn address) :: rest =>
      match he : store.exns[address.index]? with
      | none => exact none
      | some exception =>
        have split : stack = rest.reverse ++ [.ref (.exn address)] := by
          simpa using congrArg List.reverse hs
        exact some ⟨(store, values rest.reverse ++ [.throwing address] ++ tail), by
          simpa [split, values, List.map_append, List.append_assoc] using
            ExceptionStep.context (vs := rest.reverse) (tail := tail) (ExceptionStep.throwRef he)⟩
    | _ => exact none
  | .throwing address =>
    if h : stack.isEmpty && tail.isEmpty then exact none
    else exact some ⟨(store, [.throwing address]), by
      simpa using (ExceptionStep.discard (store := store) (state := state)
        (discarded := stack) (tail := tail) (address := address) h)⟩
  | _ => exact none

private def checkedExceptionBoundary (store : Store) (state : Frame) (op : AdminInstr) :
    CheckedExceptionStep store state [op] := by
  match op with
  | .label n continuation body =>
    let inner : CheckedExceptionStep store state [.label n continuation body] :=
      match he : body with
      | [.throwing address] => some ⟨(store, [.throwing address]), .labelThrow⟩
      | _ => none
    exact inner
  | .frame n inner body =>
    let next : CheckedExceptionStep store state [.frame n inner body] :=
      match he : body with
      | [.throwing address] => some ⟨(store, [.throwing address]), .frameThrow⟩
      | _ => none
    exact next
  | .handler catches body =>
    let p := splitPrefix body
    let next : CheckedExceptionStep store state [.handler catches body] := by
      match hr : p.rest with
      | [] => exact some ⟨(store, values p.values), by
          simpa [p.reconstruct, hr] using (ExceptionStep.done (catches := catches))⟩
      | .instr .return_ :: rest => exact some ⟨(store, values p.values ++ [.instr .return_]), by
          simpa [p.reconstruct, hr] using
            (ExceptionStep.return_ (catches := catches) (tail := rest))⟩
      | .instr (.br d) :: rest => exact some ⟨(store, values p.values ++ [.instr (.br d)]), by
          simpa [p.reconstruct, hr] using
            (ExceptionStep.branch (catches := catches) (tail := rest))⟩
      | _ =>
        match he : body with
        | [.trap] => exact some ⟨(store, [.trap]), .trap⟩
        | [.throwing address] =>
          match hx : store.exns[address.index]? with
          | none => exact none
          | some exception => exact (selectCatch state address exception catches).map fun next =>
              ⟨(store, next.val), .caught hx next.property⟩
        | _ => exact none
    exact next
  | _ => exact none

private def exceptionScanner : ContextualScanner where
  leaf store state op stack tail :=
    (checkedExceptionLeaf store state op stack tail).map Subtype.val
  boundary store state op := (checkedExceptionBoundary store state op).map Subtype.val

private theorem ContextualStep.exception (h : ContextualStep ExceptionStep store state code next code') :
    ExceptionStep store state code next code' := by
  induction h with
  | redex h => exact h
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

def stepExceptions (store : Store) (state : Frame) (code : List AdminInstr) :
    Option (Store × List AdminInstr) := exceptionScanner.step store state code

theorem stepExceptions_sound (h : stepExceptions store state code = some next) :
    ExceptionStep store state code next.1 next.2 := by
  have lifted := ContextualScanner.scan_sound (redex := ExceptionStep)
    (scanner := exceptionScanner)
    (by
      intro store state op stack tail next found
      obtain ⟨checked, _, same⟩ := Option.map_eq_some_iff.mp found
      cases same
      exact .redex checked.property)
    (by
      intro store state op next found
      obtain ⟨checked, _, same⟩ := Option.map_eq_some_iff.mp found
      cases same
      exact .redex checked.property) h
  simpa [values] using lifted.exception

/-- The parameter types of stored tags are independently valid runtime value types. -/
def Store.TagParametersValid (store : Store) : Prop :=
  ∀ tag ∈ store.tags, ∀ type ∈ tag.type.params, Types.RuntimeValValid {} (Types.embedVal type)

private theorem selectCatch_complete (h : CatchOutcome state address exception catches code) :
    (selectCatch state address exception catches).isSome = true := by
  induction h with
  | empty | all => rfl
  | hit ht =>
    simp only [selectCatch]
    split <;> simp_all
  | miss ht hne next ih =>
    simp only [selectCatch]
    split <;> simp_all

private theorem splitPrefix_values_rest (vs : List Value) (rest : List AdminInstr)
    (notConst : ∀ value tail, rest ≠ .instr (.const value) :: tail) :
    (splitPrefix (values vs ++ rest)).values = vs ∧
      (splitPrefix (values vs ++ rest)).rest = rest := by
  induction vs with
  | nil =>
    cases rest with
    | nil => exact ⟨rfl, rfl⟩
    | cons op tail =>
      cases op with
      | instr instr =>
        cases instr with
        | const value => exact False.elim (notConst value tail rfl)
        | _ => exact ⟨rfl, rfl⟩
      | _ => exact ⟨rfl, rfl⟩
  | cons value vs ih => simpa [values, splitPrefix] using ih

private theorem drop_typed_args (h : ArgsTyped store args types) (stack : List Value) :
    (stack ++ args).drop ((stack ++ args).length - types.length) = args := by
  rw [List.length_append, h.length, Nat.add_sub_cancel]
  simp

private theorem exception_local_complete
    (storeValid : store.RuntimeTypesValid) (tagsValid : store.TagParametersValid)
    (reduced : ExceptionRedex store state code next code') (stack : List Value)
    (tail : List AdminInstr) :
    (exceptionScanner.scan store state (code ++ tail) stack).isSome = true := by
  cases reduced with
  | enter ht ha =>
    simp only [List.append_assoc, ContextualScanner.scan_values]
    simp [ContextualScanner.scan, exceptionScanner, checkedExceptionLeaf, ht,
      ha, List.length_append, List.take_append, List.drop_append, exceptionContext]
    split <;> simp_all [List.length_append, List.take_append, List.drop_append]
  | throw_ ht hs ha =>
    have length := ha.length
    have dropped := drop_typed_args ha stack
    have checked := checkArgs_complete storeValid
      (tagsValid _ (List.mem_of_getElem? hs)) ha
    obtain ⟨proof, found⟩ := Option.isSome_iff_exists.mp checked
    simp only [List.append_assoc, ContextualScanner.scan_values]
    simp [ContextualScanner.scan, exceptionScanner, checkedExceptionLeaf, ht, hs,
      length, List.length_append, List.take_append, List.drop_append, found, exceptionContext]
    split <;> simp_all
    subst_vars
    split <;> simp_all [List.length_append, List.take_append, List.drop_append, found]
    subst_vars
    have droppedAgain := drop_typed_args ha stack
    split <;> simp_all [droppedAgain, found]
    rename_i checked missing
    rw [drop_typed_args ha stack] at missing
    simp [found] at missing
  | throwRef he =>
    simp [ContextualScanner.scan, exceptionScanner, checkedExceptionLeaf, List.reverse_append,
      he, exceptionContext]
    split <;> try simp_all [List.reverse_append]
    subst_vars
    split <;> simp_all
  | throwNull =>
    rename_i heap
    simp [ContextualScanner.scan, exceptionScanner, checkedExceptionLeaf, List.reverse_append,
      exceptionContext]
    split <;> try (simp_all only [List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, List.cons.injEq, Value.ref.injEq,
      RefValue.noConfusion, Option.isSome_some])
    · rename_i address rest same
      have first := congrArg List.head? same
      simp [List.reverse_append] at first
    · rename_i missNull missExn
      exact False.elim (missNull heap stack.reverse ⟨rfl, rfl⟩)
  | @discard _ _ discarded suffix address nonempty =>
    simp only [List.append_assoc, ContextualScanner.scan_values]
    have remains : ((stack ++ discarded).isEmpty && (suffix ++ tail).isEmpty) ≠ true := by
      cases discarded <;> cases suffix <;> simp_all
    simp [ContextualScanner.scan, exceptionScanner, checkedExceptionLeaf, remains]
    simp_all
  | labelThrow | frameThrow | trap =>
    simp [ContextualScanner.scan, exceptionScanner, checkedExceptionBoundary, splitPrefix]
  | caught he hc =>
    have success := selectCatch_complete hc
    simp [ContextualScanner.scan, exceptionScanner, checkedExceptionBoundary, splitPrefix, he,
      success]
    obtain ⟨proof, found⟩ := Option.isSome_iff_exists.mp success
    split <;> simp_all
    split at * <;> simp_all [found]
    subst_vars
    try simp_all [found]
  | @done _ _ catches vs =>
    obtain ⟨front, rest⟩ := splitPrefix_values_rest (rest := []) vs (by simp)
    have emptyRest : (splitPrefix (values vs)).rest = [] := by
      have same : values vs ++ [] = values vs := List.append_nil _
      exact same ▸ rest
    simp [ContextualScanner.scan, exceptionScanner, checkedExceptionBoundary, emptyRest]
    split <;> simp_all
    split at * <;> simp_all
  | @return_ _ _ catches vs suffix =>
    obtain ⟨front, rest⟩ := splitPrefix_values_rest (rest := .instr .return_ :: suffix) vs (by simp)
    simp [ContextualScanner.scan, exceptionScanner, checkedExceptionBoundary, rest,
      List.append_assoc]
    split <;> simp_all
    split at * <;> simp_all
  | @branch _ _ catches vs suffix d =>
    obtain ⟨front, rest⟩ := splitPrefix_values_rest (rest := .instr (.br d) :: suffix) vs (by simp)
    simp [ContextualScanner.scan, exceptionScanner, checkedExceptionBoundary, rest,
      List.append_assoc]
    split <;> simp_all
    split at * <;> simp_all

/-- Exception allocation, catch selection, and unwinding always find a permitted successor. -/
theorem stepExceptions_complete (reduced : ExceptionStep store state code next code')
    (storeValid : store.RuntimeTypesValid) (tagsValid : store.TagParametersValid) :
    (stepExceptions store state code).isSome = true := by
  exact ContextualScanner.step_complete
    (domain := fun _ _ => True)
    (by intro state code next code' h _ stack tail
        exact exception_local_complete storeValid tagsValid h stack tail)
    reduced.contextual (codeScopedValid_true state code)

#print axioms stepExceptions_complete

theorem ExceptionStep.resources_preserved (h : ExceptionStep store state code next code') :
    next.funcs = store.funcs ∧ next.globals = store.globals ∧ next.mems = store.mems ∧
      next.datas = store.datas ∧ next.tables = store.tables ∧ next.elems = store.elems := by
  induction h with
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Wasm
