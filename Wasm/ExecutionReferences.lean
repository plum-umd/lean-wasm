import Wasm.ExecutionRuntime

namespace Wasm.Execution
inductive ReferenceReduces (store : Store) (state : Frame) :
    List AdminInstr → List AdminInstr → Prop where
  | testYes (closedType : heap.close? state.module.definedTypes = some closed)
      (matched : Typed store (.ref reference)
        (if nullable then .ref closed else .refNonNull closed)) :
      ReferenceReduces store state
        [ .instr (.const (.ref reference)), .instr (.refTest nullable heap) ] (values [.i32 1])
  | testNo (closedType : heap.close? state.module.definedTypes = some closed)
      (rejected : (searchValue store (.ref reference)
        (if nullable then .ref closed else .refNonNull closed)).isRejected = true) :
      ReferenceReduces store state
        [ .instr (.const (.ref reference)), .instr (.refTest nullable heap) ] (values [.i32 0])
  | castSource (closedType : heap.close? state.module.definedTypes = some closed)
      (matched : Typed store (.ref reference)
        (if nullable then .ref closed else .refNonNull closed)) :
      ReferenceReduces store state
        [ .instr (.const (.ref reference)), .instr (.refCast nullable heap) ]
        (values [.ref reference])
  | castSourceTrap (closedType : heap.close? state.module.definedTypes = some closed)
      (rejected : (searchValue store (.ref reference)
        (if nullable then .ref closed else .refNonNull closed)).isRejected = true) :
      ReferenceReduces store state
        [ .instr (.const (.ref reference)), .instr (.refCast nullable heap) ] [.trap]
  | brCastYes (closedType : target.heap.close? state.module.definedTypes = some closed)
      (matched : Typed store (.ref reference)
        (if target.nullable then .ref closed else .refNonNull closed)) :
      ReferenceReduces store state
        [.instr (.const (.ref reference)), .instr (.brOnCast fail x source target)]
        (if fail then values [.ref reference] else values [.ref reference] ++ [.instr (.br x)])
  | brCastNo (closedType : target.heap.close? state.module.definedTypes = some closed)
      (rejected : (searchValue store (.ref reference)
        (if target.nullable then .ref closed else .refNonNull closed)).isRejected = true) :
      ReferenceReduces store state
        [.instr (.const (.ref reference)), .instr (.brOnCast fail x source target)]
        (if fail then values [.ref reference] ++ [.instr (.br x)] else values [.ref reference])
  | gc (evaluated : evalGCReference op args = some code) :
      ReferenceReduces store state (values args ++ [.instr (.gcReference op)]) code
  | null (ht : kind.close? state.module.definedTypes = some closed) :
      ReferenceReduces store state [.instr (.refNull kind)] (values [.ref (.null closed)])
  | func (ha : state.module.funcAddr? x = some address) :
      ReferenceReduces store state [.instr (.refFunc x)] (values [.ref (.func address)])
  | isNull : ReferenceReduces store state [ .instr (.const (.ref r)), .instr .refIsNull ]
      (values [.i32 (if r.isNull then 1 else 0)])
  | asNonNullTrap : ReferenceReduces store state
      [.instr (.const (.ref (.null heap))), .instr .refAsNonNull] [.trap]
  | asNonNull (hn : reference.isNull = false) : ReferenceReduces store state
      [.instr (.const (.ref reference)), .instr .refAsNonNull] (values [.ref reference])
  | brOnNull : ReferenceReduces store state
      [.instr (.const (.ref (.null heap))), .instr (.brOnNull x)] [.instr (.br x)]
  | brOnNullFallthrough (hn : reference.isNull = false) : ReferenceReduces store state
      [.instr (.const (.ref reference)), .instr (.brOnNull x)] (values [.ref reference])
  | brOnNonNullFallthrough : ReferenceReduces store state
      [.instr (.const (.ref (.null heap))), .instr (.brOnNonNull x)] []
  | brOnNonNull (hn : reference.isNull = false) : ReferenceReduces store state
      [.instr (.const (.ref reference)), .instr (.brOnNonNull x)]
        (values [.ref reference] ++ [.instr (.br x)])
  | castLegacy (ht : Typed store (.ref reference) (.ref ft.definedType.heap)) :
      ReferenceReduces store state [.instr (.const (.ref reference)), .castFunc ft]
        (values [.ref reference])
  | castLegacyTrap
      (ht : (searchValue store (.ref reference) (.ref ft.definedType.heap)).isRejected = true) :
      ReferenceReduces store state [.instr (.const (.ref reference)), .castFunc ft] [.trap]
  | castDefined (ht : Typed store (.ref reference) (.ref type.heap)) :
      ReferenceReduces store state [.instr (.const (.ref reference)), .castDefined type]
        (values [.ref reference])
  | castDefinedTrap
      (ht : (searchValue store (.ref reference) (.ref type.heap)).isRejected = true) :
      ReferenceReduces store state [.instr (.const (.ref reference)), .castDefined type] [.trap]

inductive ReferenceStep (store : Store) :
    Frame → List AdminInstr → List AdminInstr → Prop where
  | redex : ReferenceReduces store state es es' → ReferenceStep store state es es'
  | context : ReferenceStep store state es es' →
      ReferenceStep store state (values vs ++ es ++ tail) (values vs ++ es' ++ tail)
  | label : ReferenceStep store state body body' →
      ReferenceStep store state [.label n continuation body] [.label n continuation body']
  | handler : ReferenceStep store state body body' →
      ReferenceStep store state [.handler catches body] [.handler catches body']
  | frame : ReferenceStep store inner body body' →
      ReferenceStep store state [.frame n inner body] [.frame n inner body']

abbrev CheckedReferenceStep (store : Store) (state : Frame) (es : List AdminInstr) :=
  Option { next : List AdminInstr // ReferenceStep store state es next }

private def referenceRedex (store : Store) (state : Frame) (es : List AdminInstr) :
    CheckedReferenceStep store state es := by
  match es with
  | [.instr (.const (.ref reference)), .instr (.refTest nullable heap)] =>
    match closedType : heap.close? state.module.definedTypes with
    | none => exact none
    | some closed =>
      match checked : searchValue store (.ref reference)
          (if nullable then .ref closed else .refNonNull closed) with
      | .found proof => exact some ⟨_, .redex (.testYes closedType proof.down)⟩
      | .rejected => exact some ⟨_, .redex (.testNo closedType
          (by simp [checked, Types.Search.isRejected]))⟩
      | .inconclusive => exact none
  | [.instr (.const (.ref reference)), .instr (.refCast nullable heap)] =>
    match closedType : heap.close? state.module.definedTypes with
    | none => exact none
    | some closed =>
      match checked : searchValue store (.ref reference)
          (if nullable then .ref closed else .refNonNull closed) with
      | .found proof => exact some ⟨_, .redex (.castSource closedType proof.down)⟩
      | .rejected => exact some ⟨_, .redex (.castSourceTrap closedType
          (by simp [checked, Types.Search.isRejected]))⟩
      | .inconclusive => exact none
  | [.instr (.const (.ref reference)), .instr (.brOnCast fail x source target)] =>
    match closedType : target.heap.close? state.module.definedTypes with
    | none => exact none
    | some closed =>
      match checked : searchValue store (.ref reference)
          (if target.nullable then .ref closed else .refNonNull closed) with
      | .found proof => exact some ⟨_, .redex (.brCastYes closedType proof.down)⟩
      | .rejected => exact some ⟨_, .redex (.brCastNo closedType
          (by simp [checked, Types.Search.isRejected]))⟩
      | .inconclusive => exact none
  | [.instr (.const a), .instr (.const b), .instr (.gcReference op)] =>
    match evaluated : evalGCReference op [a, b] with
    | none => exact none
    | some code => exact some ⟨code, .redex (.gc evaluated)⟩
  | [.instr (.const a), .instr (.gcReference op)] =>
    match evaluated : evalGCReference op [a] with
    | none => exact none
    | some code => exact some ⟨code, .redex (.gc evaluated)⟩
  | [.instr (.refNull kind)] =>
    match ht : kind.close? state.module.definedTypes with
    | none => exact none
    | some closed => exact some ⟨_, .redex (.null ht)⟩
  | [.instr (.refFunc x)] =>
    match ha : state.module.funcAddr? x with
    | none => exact none
    | some address => exact some ⟨_, .redex (.func ha)⟩
  | [.instr (.const (.ref r)), .instr .refIsNull] => exact some ⟨_, .redex .isNull⟩
  | [.instr (.const (.ref reference)), .instr .refAsNonNull] =>
    match reference with
    | .null _ => exact some ⟨_, .redex .asNonNullTrap⟩
    | .func _ => exact some ⟨_, .redex (.asNonNull rfl)⟩
    | .extern _ => exact some ⟨_, .redex (.asNonNull rfl)⟩
    | .exn _ => exact some ⟨_, .redex (.asNonNull rfl)⟩
    | .struct_ _ | .array _ | .i31 _ | .host _ | .external _ =>
      exact some ⟨_, .redex (.asNonNull rfl)⟩
  | [.instr (.const (.ref reference)), .instr (.brOnNull x)] =>
    match reference with
    | .null _ => exact some ⟨_, .redex .brOnNull⟩
    | .func _ => exact some ⟨_, .redex (.brOnNullFallthrough rfl)⟩
    | .extern _ => exact some ⟨_, .redex (.brOnNullFallthrough rfl)⟩
    | .exn _ => exact some ⟨_, .redex (.brOnNullFallthrough rfl)⟩
    | .struct_ _ | .array _ | .i31 _ | .host _ | .external _ =>
      exact some ⟨_, .redex (.brOnNullFallthrough rfl)⟩
  | [.instr (.const (.ref reference)), .instr (.brOnNonNull x)] =>
    match reference with
    | .null _ => exact some ⟨_, .redex .brOnNonNullFallthrough⟩
    | .func _ => exact some ⟨_, .redex (.brOnNonNull rfl)⟩
    | .extern _ => exact some ⟨_, .redex (.brOnNonNull rfl)⟩
    | .exn _ => exact some ⟨_, .redex (.brOnNonNull rfl)⟩
    | .struct_ _ | .array _ | .i31 _ | .host _ | .external _ =>
      exact some ⟨_, .redex (.brOnNonNull rfl)⟩
  | [.instr (.const (.ref reference)), .castFunc ft] =>
    match checked : searchValue store (.ref reference) (.ref ft.definedType.heap) with
    | .found proof => exact some ⟨_, .redex (.castLegacy proof.down)⟩
    | .rejected =>
      exact some ⟨_, .redex (.castLegacyTrap (by simp [checked, Types.Search.isRejected]))⟩
    | .inconclusive => exact none
  | [.instr (.const (.ref reference)), .castDefined type] =>
    match checked : searchValue store (.ref reference) (.ref type.heap) with
    | .found proof => exact some ⟨_, .redex (.castDefined proof.down)⟩
    | .rejected =>
      exact some ⟨_, .redex (.castDefinedTrap (by simp [checked, Types.Search.isRejected]))⟩
    | .inconclusive => exact none
  | _ => exact none

private def referenceContext (vs : List Value) (tail : List AdminInstr)
    (s : CheckedReferenceStep store state es) :
    CheckedReferenceStep store state (values vs ++ es ++ tail) :=
  s.map fun next => ⟨values vs ++ next.val ++ tail, .context next.property⟩

def checkedReferenceStep (store : Store) (state : Frame) (es : List AdminInstr) :
    CheckedReferenceStep store state es := by
  match es with
  | .instr (.const (.ref reference)) :: .instr (.refTest nullable heap) :: tail =>
    simpa [values] using referenceContext [] tail
      (referenceRedex store state
        [.instr (.const (.ref reference)), .instr (.refTest nullable heap)])
  | .instr (.const (.ref reference)) :: .instr (.refCast nullable heap) :: tail =>
    simpa [values] using referenceContext [] tail
      (referenceRedex store state
        [.instr (.const (.ref reference)), .instr (.refCast nullable heap)])
  | .instr (.const (.ref reference)) :: .instr (.brOnCast fail x source target) :: tail =>
    simpa [values] using referenceContext [] tail
      (referenceRedex store state
        [.instr (.const (.ref reference)), .instr (.brOnCast fail x source target)])
  | .instr (.const a) :: .instr (.const b) :: .instr (.gcReference .eq) :: tail =>
    simpa [values] using referenceContext [] tail
      (referenceRedex store state
        [.instr (.const a), .instr (.const b), .instr (.gcReference .eq)])
  | .instr (.const a) :: .instr (.gcReference op) :: tail =>
    simpa [values] using referenceContext [] tail
      (referenceRedex store state [.instr (.const a), .instr (.gcReference op)])
  | .instr (.const (.ref r)) :: .instr .refIsNull :: tail =>
    simpa [values] using referenceContext [] tail
      (referenceRedex store state [.instr (.const (.ref r)), .instr .refIsNull])
  | .instr (.const (.ref r)) :: .instr .refAsNonNull :: tail =>
    simpa [values] using referenceContext [] tail
      (referenceRedex store state [.instr (.const (.ref r)), .instr .refAsNonNull])
  | .instr (.const (.ref r)) :: .instr (.brOnNull x) :: tail =>
    simpa [values] using referenceContext [] tail
      (referenceRedex store state [.instr (.const (.ref r)), .instr (.brOnNull x)])
  | .instr (.const (.ref r)) :: .instr (.brOnNonNull x) :: tail =>
    simpa [values] using referenceContext [] tail
      (referenceRedex store state [.instr (.const (.ref r)), .instr (.brOnNonNull x)])
  | .instr (.const (.ref r)) :: .castFunc ft :: tail =>
    simpa [values] using referenceContext [] tail
      (referenceRedex store state [.instr (.const (.ref r)), .castFunc ft])
  | .instr (.const (.ref r)) :: .castDefined type :: tail =>
    simpa [values] using referenceContext [] tail
      (referenceRedex store state [.instr (.const (.ref r)), .castDefined type])
  | .instr (.refNull kind) :: tail =>
    simpa [values] using referenceContext [] tail
      (referenceRedex store state [.instr (.refNull kind)])
  | .instr (.refFunc x) :: tail =>
    simpa [values] using referenceContext [] tail (referenceRedex store state [.instr (.refFunc x)])
  | .instr (.const v) :: tail =>
    simpa [values] using referenceContext [v] [] (checkedReferenceStep store state tail)
  | .label n continuation body :: tail =>
    let inner : CheckedReferenceStep store state [.label n continuation body] :=
      (checkedReferenceStep store state body).map fun next =>
        ⟨[.label n continuation next.val], .label next.property⟩
    simpa [values] using referenceContext [] tail inner
  | .handler catches body :: tail =>
    let inner : CheckedReferenceStep store state [.handler catches body] :=
      (checkedReferenceStep store state body).map fun next =>
        ⟨[.handler catches next.val], .handler next.property⟩
    simpa [values] using referenceContext [] tail inner
  | .frame n frame body :: tail =>
    let inner : CheckedReferenceStep store state [.frame n frame body] :=
      (checkedReferenceStep store frame body).map fun next =>
        ⟨[.frame n frame next.val], .frame next.property⟩
    simpa [values] using referenceContext [] tail inner
  | _ => exact none
termination_by sizeOf es
decreasing_by all_goals simp_wf; omega

def stepReferences (store : Store) (state : Frame) (es : List AdminInstr) :
    Option (List AdminInstr) := (checkedReferenceStep store state es).map Subtype.val

theorem stepReferences_sound (h : stepReferences store state es = some next) :
    ReferenceStep store state es next := by
  unfold stepReferences at h
  cases hs : checkedReferenceStep store state es with
  | none => simp [hs] at h
  | some s => simp [hs] at h; subst next; exact s.property

end Wasm.Execution
