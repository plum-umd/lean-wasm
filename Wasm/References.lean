import Wasm.FamilyScanner
import Wasm.RuntimeMatchingCompleteness

namespace Wasm

def RefValue.isNull : RefValue → Bool
  | .null _ => true
  | _ => false

def RefValue.internalize : RefValue → RefValue
  | .null _ => .null .any
  | .extern id => .host id
  | .external reference => reference
  | reference => reference

def RefValue.externalize : RefValue → RefValue
  | .null _ => .null .extern
  | .host id => .extern id
  | reference => .external reference

def RefValue.equal (a b : RefValue) : Bool :=
  match a, b with
  | .null _, .null _ => true
  | _, _ => decide (a = b)

/-- Equations for the GC operations that neither allocate nor inspect heap objects. -/
def evalGCReference : GCReferenceOp → List Value → Option (List AdminInstr)
  | .i31New, [.i32 bits] => some (values [.ref (.i31 (bits.truncate 31))])
  | .i31GetS, [.ref (.i31 bits)] => some (values [.i32 (bits.signExtend 32)])
  | .i31GetU, [.ref (.i31 bits)] => some (values [.i32 (bits.zeroExtend 32)])
  | .i31GetS, [.ref (.null _)] | .i31GetU, [.ref (.null _)] => some [.trap]
  | .eq, [.ref a, .ref b] => some (values [.i32 (if a.equal b then 1 else 0)])
  | .anyConvertExtern, [.ref reference] => some (values [.ref reference.internalize])
  | .externConvertAny, [.ref reference] => some (values [.ref reference.externalize])
  | _, _ => none

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

private def referenceOperands : AdminInstr → Option Nat
  | .instr (.refNull _) | .instr (.refFunc _) => some 0
  | .instr (.gcReference op) => some op.signature.params.length
  | .instr (.refTest _ _) | .instr (.refCast _ _) | .instr (.brOnCast _ _ _ _)
  | .instr .refIsNull | .instr .refAsNonNull | .instr (.brOnNull _)
  | .instr (.brOnNonNull _) | .castFunc _ | .castDefined _ => some 1
  | _ => none

private def referenceScanner : FamilyScanner where
  operands := fun _ => referenceOperands
  reduce := fun store state op args =>
    (referenceRedex store state (values args ++ [op])).map fun checked => (store, checked.val)

private theorem reference_family (step : FamilyStep
    (fun store state op args next code => next = store ∧
      ReferenceStep store state (values args ++ [op]) code) store state code next code') :
    next = store ∧ ReferenceStep store state code code' := by
  induction step with
  | redex h => exact h
  | context _ ih => exact ⟨ih.1, .context ih.2⟩
  | label _ ih => exact ⟨ih.1, .label ih.2⟩
  | handler _ ih => exact ⟨ih.1, .handler ih.2⟩
  | frame _ ih => exact ⟨ih.1, .frame ih.2⟩

private theorem referenceScanner_sound
    (found : referenceScanner.scan store state code stack = some next) :
    next.1 = store ∧ ReferenceStep store state (values stack ++ code) next.2 := by
  apply reference_family
  apply referenceScanner.scan_sound (redex := fun store state op args next code =>
    next = store ∧ ReferenceStep store state (values args ++ [op]) code) ?_ found
  intro store state op args result success
  rcases result with ⟨next, code⟩
  change (referenceRedex store state (values args ++ [op])).map
    (fun checked => (store, checked.val)) = some (next, code) at success
  cases checked : referenceRedex store state (values args ++ [op]) with
  | none => simp [checked] at success
  | some proof =>
    simp only [checked, Option.map_some, Option.some.injEq, Prod.mk.injEq] at success
    exact ⟨success.1.symm, success.2 ▸ proof.property⟩

def checkedReferenceStep (store : Store) (state : Frame) (code : List AdminInstr) :
    CheckedReferenceStep store state code :=
  match found : referenceScanner.scan store state code [] with
  | none => none
  | some next => some ⟨next.2, by simpa [values] using (referenceScanner_sound found).2⟩

def stepReferences (store : Store) (state : Frame) (es : List AdminInstr) :
    Option (List AdminInstr) := (checkedReferenceStep store state es).map Subtype.val

theorem stepReferences_sound (h : stepReferences store state es = some next) :
    ReferenceStep store state es next := by
  unfold stepReferences at h
  cases hs : checkedReferenceStep store state es with
  | none => simp [hs] at h
  | some s => simp [hs] at h; subst next; exact s.property

/-- Validity of a cast/test target is independent of the search performed on its operand. -/
def ReferenceExpectedTypesValid (state : Frame) : AdminInstr → Prop
  | .instr (.refTest _ heap) | .instr (.refCast _ heap) =>
      ∀ closed, heap.close? state.module.definedTypes = some closed → Types.HeapValid {} closed
  | .instr (.brOnCast _ _ _ target) =>
      ∀ closed, target.heap.close? state.module.definedTypes = some closed → Types.HeapValid {} closed
  | .castFunc type => Types.HeapValid {} type.definedType.heap
  | .castDefined type => Types.HeapValid {} type.heap
  | _ => True

private theorem reference_target_valid (valid : Types.HeapValid {} heap) (nullable : Bool) :
    Types.RuntimeValValid {} (Types.embedVal (if nullable then .ref heap else .refNonNull heap)) := by
  cases nullable <;> exact .ref valid

private theorem reference_raw_complete (reduced : ReferenceReduces store state code code')
    (valid : store.RuntimeTypesValid)
    (targets : CodeScopedValid ReferenceExpectedTypesValid state code) :
    (referenceRedex store state code).isSome = true := by
  cases reduced
  all_goals simp [CodeScopedValid, AdminInstr.ScopedValid, ReferenceExpectedTypesValid,
    values] at targets
  case' testYes closedType matched =>
    obtain ⟨proof, found⟩ := searchValue_complete valid
      (reference_target_valid (targets _ closedType) _) matched
  case' castSource closedType matched =>
    obtain ⟨proof, found⟩ := searchValue_complete valid
      (reference_target_valid (targets _ closedType) _) matched
  case' brCastYes closedType matched =>
    obtain ⟨proof, found⟩ := searchValue_complete valid
      (reference_target_valid (targets _ closedType) _) matched
  case' castLegacy matched =>
    obtain ⟨proof, found⟩ := searchValue_complete (type := .ref _) valid (.ref targets) matched
  case' castDefined matched =>
    obtain ⟨proof, found⟩ := searchValue_complete (type := .ref _) valid (.ref targets) matched
  case gc evaluated =>
    unfold evalGCReference at evaluated
    split at evaluated <;> simp_all [referenceRedex, values, evalGCReference]
  all_goals simp only [referenceRedex]
  all_goals repeat first | simp_all [Types.Search.isRejected] | split
  all_goals subst_vars
  all_goals repeat first | simp_all | split

private theorem gc_reference_arity (evaluated : evalGCReference op args = some code) :
    args.length = op.signature.params.length := by
  unfold evalGCReference at evaluated
  split at evaluated <;> simp_all [GCReferenceOp.signature]

private def ReferenceLocal (store : Store) (state : Frame) (op : AdminInstr)
    (args : List Value) (next : Store) (code : List AdminInstr) : Prop :=
  op.ScannerAtom ∧ referenceOperands op = some args.length ∧ next = store ∧
    ReferenceReduces store state (values args ++ [op]) code

private theorem ReferenceStep.toFamily (reduced : ReferenceStep store state code code') :
    FamilyStep ReferenceLocal store state code store code' := by
  induction reduced with
  | redex reduced =>
    cases reduced
    case gc evaluated =>
      refine FamilyStep.redex ⟨by trivial, ?_, rfl, .gc evaluated⟩
      simp [referenceOperands, gc_reference_arity evaluated]
    all_goals first
      | refine FamilyStep.redex (op := .instr _) (args := []) ?_
      | refine FamilyStep.redex (op := .instr _) (args := [_]) ?_
      | refine FamilyStep.redex (op := .instr _) ?_
      | refine FamilyStep.redex (op := .castFunc _) (args := [_]) ?_
      | refine FamilyStep.redex (op := .castDefined _) (args := [_]) ?_
    all_goals refine ⟨by trivial, ?_, rfl, ?_⟩
    all_goals first | rfl | (constructor <;> assumption)
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

/-- Reference scanning is complete when its written target types are valid in their frames. -/
theorem stepReferences_complete (reduced : ReferenceStep store state code code')
    (valid : store.RuntimeTypesValid)
    (targets : CodeScopedValid ReferenceExpectedTypesValid state code) :
    (stepReferences store state code).isSome = true := by
  have success := referenceScanner.step_complete_scoped (redex := ReferenceLocal)
    (domain := ReferenceExpectedTypesValid) ?_ (fun _ _ _ _ _ h => h.1)
    reduced.toFamily targets
  · unfold stepReferences checkedReferenceStep
    change (referenceScanner.scan store state code []).isSome = true at success
    split <;> simp_all
  · intro state op args next code ready localStep
    refine ⟨localStep.1, localStep.2.1, ?_⟩
    have targetValid : CodeScopedValid ReferenceExpectedTypesValid state (values args ++ [op]) := by
      simp only [codeScopedValid_append, codeScopedValid_singleton]
      refine ⟨?_, ?_⟩
      · simp [CodeScopedValid, values, AdminInstr.ScopedValid, ReferenceExpectedTypesValid]
      · rw [localStep.1.scopedValid_eq]
        exact ready
    have found := reference_raw_complete localStep.2.2.2 valid targetValid
    simpa [referenceScanner] using found

#print axioms stepReferences_complete

end Wasm
