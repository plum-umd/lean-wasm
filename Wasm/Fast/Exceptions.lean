import Wasm.Fast.Runtime

namespace Wasm.Fast


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

private def scanExceptions (store : Store) (state : Frame) (code : List AdminInstr)
    (stack : List Value) : CheckedExceptionStep store state (values stack ++ code) := by
  match code with
  | .instr (.const v) :: tail =>
    simpa [values, List.map_append, List.append_assoc] using
      scanExceptions store state tail (stack ++ [v])
  | .instr (.tryTable bt catches body) :: tail =>
    match ht : bt.resolve state.module.types with
    | none => exact none
    | some ft =>
      let n := ft.params.length
      if hn : n ≤ stack.length then
        let below := stack.take (stack.length - n)
        let args := stack.drop (stack.length - n)
        have split : stack = below ++ args := (List.take_append_drop _ _).symm
        have arity : args.length = ft.params.length := by simp [args, n] at *; omega
        simpa [split, values, List.map_append, List.append_assoc] using
          exceptionContext below tail (some ⟨(store, [.handler catches
            [.label ft.results.length [] (values args ++ instructions body)]]),
            ExceptionStep.enter ht arity⟩)
      else exact none
  | .instr (.throw_ x) :: tail =>
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
            simpa [split, values, List.map_append, List.append_assoc] using
              exceptionContext below tail (some
                ⟨({store with exns := store.exns ++ [⟨address, args⟩]},
                [.throwing ⟨store.exns.length⟩]), ExceptionStep.throw_ ht hs typed.down⟩)
        else exact none
  | .instr .throwRef :: tail =>
    match hs : stack.reverse with
    | .ref (.null heap) :: rest =>
      have split : stack = rest.reverse ++ [.ref (.null heap)] := by
        simpa using congrArg List.reverse hs
      simpa [split, values, List.map_append, List.append_assoc] using
        exceptionContext rest.reverse tail (some ⟨(store, [.trap]), ExceptionStep.throwNull⟩)
    | .ref (.exn address) :: rest =>
      match he : store.exns[address.index]? with
      | none => exact none
      | some exception =>
        have split : stack = rest.reverse ++ [.ref (.exn address)] := by
          simpa using congrArg List.reverse hs
        simpa [split, values, List.map_append, List.append_assoc] using
          exceptionContext rest.reverse tail (some
            ⟨(store, [.throwing address]), ExceptionStep.throwRef he⟩)
    | _ => exact none
  | .throwing address :: tail =>
    if h : stack.isEmpty && tail.isEmpty then exact none
    else exact some ⟨(store, [.throwing address]), by
      simpa using (ExceptionStep.discard (store := store) (state := state)
        (discarded := stack) (tail := tail) (address := address) h)⟩
  | .label n continuation body :: tail =>
    let inner : CheckedExceptionStep store state [.label n continuation body] :=
      match he : body with
      | [.throwing address] => some ⟨(store, [.throwing address]), .labelThrow⟩
      | _ => (scanExceptions store state body []).map fun next =>
          ⟨(next.val.1, [.label n continuation next.val.2]),
            .label (by simpa [values, he] using next.property)⟩
    simpa using exceptionContext stack tail inner
  | .frame n inner body :: tail =>
    let next : CheckedExceptionStep store state [.frame n inner body] :=
      match he : body with
      | [.throwing address] => some ⟨(store, [.throwing address]), .frameThrow⟩
      | _ => (scanExceptions store inner body []).map fun next =>
          ⟨(next.val.1, [.frame n inner next.val.2]),
            .frame (by simpa [values, he] using next.property)⟩
    simpa using exceptionContext stack tail next
  | .handler catches body :: tail =>
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
        | _ => exact (scanExceptions store state body []).map fun next =>
            ⟨(next.val.1, [.handler catches next.val.2]),
              .handler (by simpa [values, he] using next.property)⟩
    simpa using exceptionContext stack tail next
  | _ => exact none
termination_by sizeOf code
decreasing_by
  all_goals simp_wf
  all_goals try simp_all
  all_goals omega

def stepExceptions (store : Store) (state : Frame) (code : List AdminInstr) :
    Option (Store × List AdminInstr) :=
  (scanExceptions store state code []).map Subtype.val

theorem stepExceptions_sound (h : stepExceptions store state code = some next) :
    ExceptionStep store state code next.1 next.2 := by
  unfold stepExceptions at h
  cases hs : scanExceptions store state code [] with
  | none => simp [hs] at h
  | some s => simp [hs] at h; subst next; simpa [values] using s.property

theorem ExceptionStep.resources_preserved (h : ExceptionStep store state code next code') :
    next.funcs = store.funcs ∧ next.globals = store.globals ∧ next.mems = store.mems ∧
      next.datas = store.datas ∧ next.tables = store.tables ∧ next.elems = store.elems := by
  induction h with
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih
  | _ => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Wasm.Fast
