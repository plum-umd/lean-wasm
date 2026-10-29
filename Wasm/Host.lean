import Wasm.Configuration

namespace Wasm

/-! A pure, unchanged-store host boundary layered over ordinary certified execution. -/

/-- Saved evaluation context, including the frames that own suspended locals. -/
inductive HostContext where
  | hole
  | sequence (before : List Value) (suffix : List AdminInstr) (inner : HostContext)
  | label (arity : Nat) (continuation : List Instr) (inner : HostContext)
  | handler (catches : List Catch) (inner : HostContext)
  | frame (arity : Nat) (state : Frame) (inner : HostContext)
  deriving BEq, Repr

def HostContext.fill : HostContext → List AdminInstr → List AdminInstr
  | .hole, code => code
  | .sequence before suffix inner, code => values before ++ inner.fill code ++ suffix
  | .label arity continuation inner, code => [.label arity continuation (inner.fill code)]
  | .handler catches inner, code => [.handler catches (inner.fill code)]
  | .frame arity state inner, code => [.frame arity state (inner.fill code)]

inductive HostCallForm where
  | direct
  | reference (type : FuncType)
  | defined (type : Types.DefinedType)
  deriving BEq, Repr

/-- Host identity is resolved in the saved store; `caller` exposes the calling instance. -/
structure HostRequest where
  address : FuncAddr
  identifier : Nat
  type : FuncType
  arguments : List Value
  caller : Frame
  tailCall : Bool
  form : HostCallForm := .direct
  deriving BEq, Repr

def FuncCode.hostIdentifier? : FuncCode → Option Nat
  | .host identifier | .hostTyped identifier _ => some identifier
  | .wasm _ => none

/-- The first boundary supports scalar signatures and never changes the store. -/
def hostScalarType : ValType → Bool
  | .i32 | .i64 | .f32 | .f64 => true
  | _ => false

def HostRequest.scalar (request : HostRequest) : Bool :=
  request.type.params.all hostScalarType && request.type.results.all hostScalarType

def HostRequest.invocation (request : HostRequest) : List AdminInstr :=
  match request.form with
  | .direct =>
    [if request.tailCall then .returnInvoke request.address request.type
      else .invoke request.address request.type]
  | .reference type =>
    values [.ref (.func request.address)] ++
      [if request.tailCall then .returnInvokeRef type else .invokeRef type]
  | .defined type =>
    values [.ref (.func request.address)] ++
      [if request.tailCall then .returnInvokeDefined type else .invokeDefined type]

/-- Reference calls retain the runtime matching evidence used by ordinary call resolution. -/
inductive HostTarget (function : FuncInst) : HostCallForm → Prop where
  | direct : HostTarget function .direct
  | reference (matched : Types.HeapMatches {} function.runtimeType.heap type.definedType.heap) :
      HostTarget function (.reference type)
  | defined (expanded : type.expand? = some signature)
      (matched : Types.HeapMatches {} function.runtimeType.heap type.heap) :
      HostTarget function (.defined type)

/-- Independent source evidence for a pending call, lifted through evaluation contexts. -/
inductive HostSite (store : Store) :
    Frame → List AdminInstr → HostRequest → HostContext → Prop where
  | invoke (found : store.func? request.address = some function)
      (identity : function.code.hostIdentifier? = some request.identifier)
      (signature : function.type = request.type)
      (target : HostTarget function request.form)
      (arguments : ArgsTyped store request.arguments request.type.params) :
      HostSite store request.caller
        (values request.arguments ++ request.invocation) request .hole
  | sequence : HostSite store state code request context →
      HostSite store state (values before ++ code ++ suffix) request
        (.sequence before suffix context)
  | label : HostSite store state body request context →
      HostSite store state [.label arity continuation body] request
        (.label arity continuation context)
  | handler : HostSite store state body request context →
      HostSite store state [.handler catches body] request (.handler catches context)
  | frame : HostSite store inner body request context →
      HostSite store state [.frame arity inner body] request (.frame arity inner context)

theorem HostSite.decompose (site : HostSite store state code request context) :
    code = context.fill (values request.arguments ++ request.invocation) := by
  induction site with
  | invoke => rfl
  | sequence _ ih => simp [HostContext.fill, ih]
  | label _ ih => simp [HostContext.fill, ih]
  | handler _ ih => simp [HostContext.fill, ih]
  | frame _ ih => simp [HostContext.fill, ih]

theorem HostSite.arguments_typed (site : HostSite store state code request context) :
    ArgsTyped store request.arguments request.type.params := by
  induction site with
  | invoke _ _ _ _ typed => exact typed
  | sequence _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

private abbrev CheckedHostSite (store : Store) (state : Frame) (code : List AdminInstr) :=
  Option { p : HostRequest × HostContext // HostSite store state code p.1 p.2 }

private def hostSequence (before : List Value) (suffix : List AdminInstr)
    (site : CheckedHostSite store state code) :
    CheckedHostSite store state (values before ++ code ++ suffix) :=
  site.map fun site => ⟨(site.val.1, .sequence before suffix site.val.2),
    .sequence site.property⟩

private def detectHostTarget (store : Store) (state : Frame) (stack : List Value)
    (address : FuncAddr) (type : FuncType) (tailCall : Bool) (form : HostCallForm)
    (function : FuncInst) (found : store.func? address = some function)
    (signature : function.type = type) (target : HostTarget function form) :
    CheckedHostSite store state
      (values stack ++ (HostRequest.mk address 0 type [] state tailCall form).invocation) := by
  match identity : function.code.hostIdentifier? with
  | none => exact none
  | some identifier =>
    if enough : type.params.length ≤ stack.length then
      let below := stack.take (stack.length - type.params.length)
      let args := stack.drop (stack.length - type.params.length)
      match checkArgs store args type.params with
      | none => exact none
      | some typed =>
        let request : HostRequest := ⟨address, identifier, type, args, state, tailCall, form⟩
        have splitStack : stack = below ++ args := (List.take_append_drop _ _).symm
        simpa [request, HostRequest.invocation, splitStack, values, List.map_append,
          List.append_assoc] using hostSequence below []
            (some ⟨(request, .hole), .invoke found identity signature target typed.down⟩)
    else exact none

private def detectHostInvoke (store : Store) (state : Frame) (stack : List Value)
    (address : FuncAddr) (type : FuncType) (tailCall : Bool) :
    CheckedHostSite store state
      (values stack ++
        [if tailCall then .returnInvoke address type else .invoke address type]) := by
  match found : store.func? address with
  | none => exact none
  | some function =>
    if signature : function.type = type then
      exact detectHostTarget store state stack address type tailCall .direct
        function found signature .direct
    else exact none

private def detectHostReference (store : Store) (state : Frame) (stack : List Value)
    (form : HostCallForm) (tailCall : Bool) (instruction : AdminInstr)
    (instructionEq : ∀ address type,
      (HostRequest.mk address 0 type [] state tailCall form).invocation =
        values [.ref (.func address)] ++ [instruction])
    (checkTarget : (function : FuncInst) → Option (PLift (HostTarget function form))) :
    CheckedHostSite store state (values stack ++ [instruction]) := by
  match reversed : stack.reverse with
  | .ref (.func address) :: rest =>
    match found : store.func? address with
    | none => exact none
    | some function =>
      match checkTarget function with
      | none => exact none
      | some target =>
        have stackEq : stack = rest.reverse ++ [.ref (.func address)] := by
          have equality := congrArg List.reverse reversed
          simpa using equality
        simpa [instructionEq, stackEq, values, List.map_append, List.append_assoc] using
          detectHostTarget store state rest.reverse address function.type tailCall form
            function found rfl target.down
  | _ => exact none

private def detectHostRef (store : Store) (state : Frame) (stack : List Value)
    (type : FuncType) (tailCall : Bool) :
    CheckedHostSite store state
      (values stack ++ [if tailCall then .returnInvokeRef type else .invokeRef type]) :=
  detectHostReference store state stack (.reference type) tailCall _ (by intros; rfl)
    fun function => (checkRuntimeHeap function.runtimeType.heap type.definedType.heap).map
      fun matched => ⟨.reference matched.down⟩

private def detectHostDefined (store : Store) (state : Frame) (stack : List Value)
    (type : Types.DefinedType) (tailCall : Bool) :
    CheckedHostSite store state
      (values stack ++ [if tailCall then .returnInvokeDefined type else .invokeDefined type]) :=
  detectHostReference store state stack (.defined type) tailCall _ (by intros; rfl)
    fun function => do
      match expanded : type.expand? with
      | none => none
      | some _ =>
        (checkRuntimeHeap function.runtimeType.heap type.heap).map
          fun matched => ⟨.defined expanded matched.down⟩

private def scanHost (store : Store) (state : Frame) (code : List AdminInstr)
    (stack : List Value) : CheckedHostSite store state (values stack ++ code) := by
  match code with
  | .instr (.const value) :: rest =>
    simpa [values, List.map_append, List.append_assoc] using
      scanHost store state rest (stack ++ [value])
  | .invoke address type :: rest =>
    exact (detectHostInvoke store state stack address type false).map fun site =>
      ⟨(site.val.1, .sequence [] rest site.val.2), by
        simpa [values, List.append_assoc] using
          (HostSite.sequence (before := []) (suffix := rest) site.property)⟩
  | .returnInvoke address type :: rest =>
    exact (detectHostInvoke store state stack address type true).map fun site =>
      ⟨(site.val.1, .sequence [] rest site.val.2), by
        simpa [values, List.append_assoc] using
          (HostSite.sequence (before := []) (suffix := rest) site.property)⟩
  | .invokeRef type :: rest =>
    exact (detectHostRef store state stack type false).map fun site =>
      ⟨(site.val.1, .sequence [] rest site.val.2), by
        simpa [values, List.append_assoc] using
          (HostSite.sequence (before := []) (suffix := rest) site.property)⟩
  | .returnInvokeRef type :: rest =>
    exact (detectHostRef store state stack type true).map fun site =>
      ⟨(site.val.1, .sequence [] rest site.val.2), by
        simpa [values, List.append_assoc] using
          (HostSite.sequence (before := []) (suffix := rest) site.property)⟩
  | .invokeDefined type :: rest =>
    exact (detectHostDefined store state stack type false).map fun site =>
      ⟨(site.val.1, .sequence [] rest site.val.2), by
        simpa [values, List.append_assoc] using
          (HostSite.sequence (before := []) (suffix := rest) site.property)⟩
  | .returnInvokeDefined type :: rest =>
    exact (detectHostDefined store state stack type true).map fun site =>
      ⟨(site.val.1, .sequence [] rest site.val.2), by
        simpa [values, List.append_assoc] using
          (HostSite.sequence (before := []) (suffix := rest) site.property)⟩
  | .label arity continuation body :: rest =>
    let site : CheckedHostSite store state [.label arity continuation body] :=
      (scanHost store state body []).map fun site =>
      ⟨(site.val.1, HostContext.label arity continuation site.val.2),
        HostSite.label (by simpa [values] using site.property)⟩
    simpa using hostSequence stack rest site
  | .handler catches body :: rest =>
    let site : CheckedHostSite store state [.handler catches body] :=
      (scanHost store state body []).map fun site =>
      ⟨(site.val.1, HostContext.handler catches site.val.2),
        HostSite.handler (by simpa [values] using site.property)⟩
    simpa using hostSequence stack rest site
  | .frame arity inner body :: rest =>
    let site : CheckedHostSite store state [.frame arity inner body] :=
      (scanHost store inner body []).map fun site =>
      ⟨(site.val.1, HostContext.frame arity inner site.val.2),
        HostSite.frame (state := state) (by simpa [values] using site.property)⟩
    simpa using hostSequence stack rest site
  | _ => exact none
termination_by sizeOf code
decreasing_by all_goals simp_wf; omega

/-- Immutable suspension. The embedder owns servicing and prevents unwanted reuse. -/
structure PendingHostCall where
  source : Configuration
  request : HostRequest
  context : HostContext
  evidence : HostSite source.store source.frame source.code request context

/-- Observation is pure and does not execute any ordinary step or host effect. -/
def observeHostCall (config : Configuration) : Option PendingHostCall :=
  (scanHost config.store config.frame config.code []).map fun site =>
    ⟨config, site.val.1, site.val.2, by simpa [values] using site.property⟩

theorem observeHostCall_sound (h : observeHostCall config = some pending) :
    pending.source = config ∧
      HostSite config.store config.frame config.code pending.request pending.context := by
  unfold observeHostCall at h
  cases hs : scanHost config.store config.frame config.code [] with
  | none => simp [hs] at h
  | some site =>
    simp [hs] at h
    subst pending
    exact ⟨rfl, by simpa [values] using site.property⟩

/-- A host error terminates this invocation as a Wasm trap; it is not a guest exception. -/
inductive HostReply where
  | values (results : List Value)
  | trap
  deriving BEq, Repr

inductive HostReplyError where
  | unsupportedSignature
  | invalidResults
  deriving BEq, Repr

def PendingHostCall.resultCode (pending : PendingHostCall) (results : List Value) :
    List AdminInstr :=
  if pending.request.tailCall then [.tailActivation (values results)] else values results

/-- Explicit boundary semantics, separate from ordinary `ConfigStep`. -/
inductive HostBoundaryStep : Configuration → HostReply → Configuration → Prop where
  | returned (site : HostSite store frame code request context)
      (scalar : request.scalar = true)
      (typed : ArgsTyped store results request.type.results) :
      HostBoundaryStep ⟨store, frame, code⟩ (.values results)
        ⟨store, frame, context.fill
          (if request.tailCall then [.tailActivation (values results)] else values results)⟩
  | trapped (site : HostSite store frame code request context)
      (scalar : request.scalar = true) :
      HostBoundaryStep ⟨store, frame, code⟩ .trap ⟨store, frame, context.fill [.trap]⟩

/-- Validate before inserting results. Errors leave the immutable pending call available. -/
def resumeHostCall (pending : PendingHostCall) (reply : HostReply) :
    Except HostReplyError Configuration :=
  if pending.request.scalar then
    match reply with
    | .trap => .ok { pending.source with code := pending.context.fill [.trap] }
    | .values results =>
      match checkArgs pending.source.store results pending.request.type.results with
      | none => .error .invalidResults
      | some _ => .ok { pending.source with
          code := pending.context.fill (pending.resultCode results) }
  else .error .unsupportedSignature

theorem resumeHostCall_sound (h : resumeHostCall pending reply = .ok next) :
    HostBoundaryStep pending.source reply next := by
  unfold resumeHostCall at h
  split at h
  · rename_i scalar
    cases reply with
    | trap =>
      cases h
      exact .trapped pending.evidence scalar
    | values results =>
      cases checked : checkArgs pending.source.store results pending.request.type.results with
      | none => simp [checked] at h
      | some typed =>
        simp [checked] at h
        subst next
        exact .returned pending.evidence scalar typed.down
  · cases h

theorem HostBoundaryStep.store_preserved (h : HostBoundaryStep config reply next) :
    next.store = config.store := by cases h <;> rfl

theorem resumeHostCall_store_preserved (h : resumeHostCall pending reply = .ok next) :
    next.store = pending.source.store :=
  (resumeHostCall_sound h).store_preserved

/-- Mixed traces expose each host reply explicitly; no callback correctness axiom is needed. -/
inductive HostExecutionStep : Configuration → Configuration → Prop where
  | ordinary : ConfigStep config next → HostExecutionStep config next
  | host : HostBoundaryStep config reply next → HostExecutionStep config next

inductive HostExecutionSteps : Configuration → Configuration → Prop where
  | refl : HostExecutionSteps config config
  | cons : HostExecutionStep config middle → HostExecutionSteps middle final →
      HostExecutionSteps config final

theorem ConfigSteps.toHostExecutionSteps (steps : ConfigSteps config final) :
    HostExecutionSteps config final := by
  induction steps with
  | refl => exact .refl
  | cons step _ ih => exact .cons (.ordinary step) ih

theorem HostExecutionSteps.trans (first : HostExecutionSteps config middle)
    (second : HostExecutionSteps middle final) : HostExecutionSteps config final := by
  induction first with
  | refl => exact second
  | cons step _ ih => exact .cons step (ih second)

inductive HostRunStatus where
  | ordinary (status : RunStatus)
  | pending (call : PendingHostCall)
  | unsupportedHost (call : PendingHostCall)

structure HostRunResult (initial : Configuration) where
  state : Configuration
  status : HostRunStatus
  trace : ConfigSteps initial state

/-- Run ordinary certified steps until a host boundary, terminal state, or fuel exhaustion.
Host observation and servicing consume no ordinary execution fuel. -/
def runUntilHost (fuel : Nat) (initial : Configuration) : HostRunResult initial :=
  let result := runConfiguration fuel initial
  match observeHostCall result.state with
  | some pending =>
    ⟨result.state, if pending.request.scalar then .pending pending else .unsupportedHost pending,
      runConfiguration_sound⟩
  | none => ⟨result.state, .ordinary result.status, runConfiguration_sound⟩

theorem runUntilHost_sound : ConfigSteps initial (runUntilHost fuel initial).state :=
  (runUntilHost fuel initial).trace

theorem runUntilHost_pending_source
    (h : (runUntilHost fuel initial).status = .pending pending) :
    pending.source = (runUntilHost fuel initial).state := by
  unfold runUntilHost at h ⊢
  cases observed : observeHostCall (runConfiguration fuel initial).state with
  | none => simp [observed] at h
  | some call =>
    simp only [observed] at h ⊢
    split at h
    · cases h
      exact (observeHostCall_sound observed).1
    · cases h

theorem runUntilHost_resume_sound
    (suspended : (runUntilHost fuel initial).status = .pending pending)
    (resumed : resumeHostCall pending reply = .ok next) :
    HostExecutionSteps initial next := by
  have boundary := resumeHostCall_sound resumed
  rw [runUntilHost_pending_source suspended] at boundary
  exact runUntilHost_sound.toHostExecutionSteps.trans (.cons (.host boundary) .refl)

end Wasm
