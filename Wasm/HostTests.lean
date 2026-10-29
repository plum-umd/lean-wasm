import Wasm.Host

namespace Wasm.Tests

private def sameHost {α : Type} [BEq α] (actual expected : α) : Bool := actual == expected
local infix:50 " ≟ " => sameHost

private def checkHost (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"host regression failed: {name}")

private def pendingHost (fuel : Nat) (config : Configuration) : IO PendingHostCall := do
  match (runUntilHost fuel config).status with
  | .pending pending => return pending
  | _ => throw (IO.userError "expected pending host call")

private def replyHost (pending : PendingHostCall) (reply : HostReply) : IO Configuration := do
  match resumeHostCall pending reply with
  | .ok config => return config
  | .error error => throw (IO.userError s!"unexpected reply error: {repr error}")

private def hostFinished (config : Configuration) (expected : List Value) : IO Unit := do
  match (runUntilHost 100 config).status with
  | .ordinary (.finished actual) => checkHost "finished values" (actual ≟ expected)
  | _ => throw (IO.userError "expected normal completion")

private def rejectedReply (pending : PendingHostCall) (results : List Value) : Bool :=
  match resumeHostCall pending (.values results) with
  | .error .invalidResults => true
  | _ => false

#eval do
  let type : FuncType := ⟨[.i64], [.i64]⟩
  let owner : ModuleInst := { types := [type], funcs := [⟨0⟩, ⟨1⟩] }
  let host : FuncInst := ⟨type, {}, .host 73⟩
  let nested : FuncInst := ⟨type, owner, .wasm ⟨0, [.i64],
    [.localGet 0, .localSet 1, .localGet 1, .call 0,
      .const (.i64 1), .binop .i64 .add]⟩⟩
  let store : Store := { funcs := [host, nested] }
  let frame : Frame := { module := { funcs := [⟨1⟩] }, locals := [some (.i32 99)] }
  let initial : Configuration := ⟨store, frame,
    instructions [.const (.i32 17), .const (.i64 5), .call 0]⟩
  let pending ← pendingHost 100 initial
  checkHost "resolved host identity" (pending.request.identifier ≟ 73)
  checkHost "resolved host address" (pending.request.address ≟ ⟨0⟩)
  checkHost "arguments" (pending.request.arguments ≟ [.i64 5])
  checkHost "expected signature" (pending.request.type ≟ type)
  checkHost "callee module" (pending.request.caller.module ≟ owner)
  checkHost "callee locals" (pending.request.caller.locals ≟ [some (.i64 5), some (.i64 5)])
  checkHost "outer locals" (pending.source.frame.locals ≟ frame.locals)
  checkHost "wrong arity" (rejectedReply pending [])
  checkHost "extra result" (rejectedReply pending [.i64 42, .i64 43])
  checkHost "wrong type" (rejectedReply pending [.i32 42])
  checkHost "dangling reference" (rejectedReply pending [.ref (.func ⟨999⟩)])
  let observed := (observeHostCall pending.source).map fun (call : PendingHostCall) =>
    (call.request, call.context, call.source)
  checkHost "repeat observation"
    (observed ≟ some (pending.request, pending.context, pending.source))
  -- A separate computation can finish while the immutable request is retained.
  hostFinished ⟨{}, {}, values [.i32 8]⟩ [.i32 8]
  let resumed ← replyHost pending (.values [.i64 42])
  checkHost "unchanged store" (resumed.store ≟ pending.source.store)
  hostFinished resumed [.i32 17, .i64 43]
  let failed ← replyHost pending .trap
  match (runUntilHost 100 failed).status with
  | .ordinary .trapped => pure ()
  | _ => throw (IO.userError "host failure did not trap")
  -- Zero fuel can observe an already pending invocation without advancing it.
  let zero ← pendingHost 0 pending.source
  checkHost "zero fuel observation" (zero.source ≟ pending.source)
  -- Saved labels and handlers retain both their continuations and their surrounding operands.
  let wrapped : Configuration := ⟨store, frame,
    values [.i32 9] ++ [AdminInstr.frame 1 frame [.label 1 [] [.handler []
      (values [.i64 5] ++ [AdminInstr.invoke ⟨0⟩ type])]]]⟩
  let inside ← pendingHost 0 wrapped
  let unwrapped ← replyHost inside (.values [.i64 42])
  hostFinished unwrapped [.i32 9, .i64 42]
  -- Tail replies must discard labels, handlers, and the callee continuation.
  let tail : Configuration := ⟨store, frame,
    values [.i32 9] ++ [AdminInstr.frame 1 frame [.label 1 [] [.handler []
      (values [.i64 5] ++ [AdminInstr.returnInvoke ⟨0⟩ type, .instr .unreachable])]]]⟩
  let tailPending ← pendingHost 0 tail
  checkHost "tail identity" tailPending.request.tailCall
  let tailResumed ← replyHost tailPending (.values [.i64 42])
  hostFinished tailResumed [.i32 9, .i64 42]
  -- Both structural and nominal reference invocations share the boundary.
  for tailCall in [false, true] do
    let invocation := if tailCall then AdminInstr.returnInvokeRef type else .invokeRef type
    let refCode := values [.i64 5, .ref (.func ⟨0⟩)] ++ [invocation]
    let refConfig : Configuration := ⟨store, frame,
      [.frame 1 frame [.label 1 [] refCode]]⟩
    let reference ← pendingHost 50 refConfig
    checkHost "reference argument suffix" (reference.request.arguments ≟ [.i64 5])
    let referenceResumed ← replyHost reference (.values [.i64 42])
    hostFinished referenceResumed [.i64 42]
  let indirectOwner : ModuleInst :=
    { owner with tables := [⟨0⟩], definedTypes := [type.definedType] }
  let indirectFrame : Frame := { frame with module := indirectOwner }
  let table : TableInst := ⟨⟨.i32, 1, some 1, .func, true⟩, #[.func ⟨0⟩]⟩
  let indirectStore := { store with tables := [table] }
  for call in [Instr.callRef 0, .returnCallRef 0, .callIndirect 0 0,
      .returnCallIndirect 0 0, .returnCall 0] do
    let operand : List Instr := match call with
      | .callRef _ | .returnCallRef _ => [.refFunc 0]
      | .callIndirect _ _ | .returnCallIndirect _ _ => [.const (.i32 0)]
      | _ => []
    let sourceCode := instructions ([Instr.const (.i64 5)] ++ operand ++ [call])
    let sourceConfig : Configuration := ⟨indirectStore, indirectFrame,
      [.frame 1 indirectFrame [.label 1 [] sourceCode]]⟩
    let indirect ← pendingHost 100 sourceConfig
    checkHost "lowered call identity" (indirect.request.identifier ≟ 73)
    let indirectResumed ← replyHost indirect (.values [.i64 42])
    hostFinished indirectResumed [.i64 42]
  let nullCall : Configuration := ⟨store, frame,
    values [.i64 5, .ref (.null .func)] ++ [AdminInstr.invokeRef type]⟩
  match (runUntilHost 10 nullCall).status with
  | .ordinary .trapped => pure ()
  | _ => throw (IO.userError "null reference call should trap")
  for code in [
      [AdminInstr.invoke ⟨0⟩ type],
      values [.i32 5] ++ [AdminInstr.invoke ⟨0⟩ type],
      values [.i64 5] ++ [AdminInstr.invoke ⟨0⟩ ⟨[.i64], [.i32]⟩],
      values [.i64 5, .ref (.func ⟨0⟩)] ++ [AdminInstr.invokeRef ⟨[.i32], [.i32]⟩]] do
    match (runUntilHost 10 ⟨store, frame, code⟩).status with
    | .ordinary .stuck => pure ()
    | _ => throw (IO.userError "malformed host invocation should remain stuck")
  let inactive : Configuration := ⟨store, frame,
    [AdminInstr.instr .unreachable] ++ values [.i64 5] ++ [AdminInstr.invoke ⟨0⟩ type]⟩
  checkHost "observation cannot skip active instructions" (observeHostCall inactive).isNone
  let multiType : FuncType := ⟨[], [.i32, .i64]⟩
  let multiStore : Store := { funcs := [⟨multiType, {}, .hostTyped 81 multiType.definedType⟩] }
  let multi ← pendingHost 0 ⟨multiStore, {}, [.invoke ⟨0⟩ multiType]⟩
  checkHost "typed host identity" (multi.request.identifier ≟ 81)
  let multiResumed ← replyHost multi (.values [.i32 3, .i64 4])
  hostFinished multiResumed [.i32 3, .i64 4]
  let refType : FuncType := ⟨[], [.ref .func]⟩
  let refStore : Store := { funcs := [⟨refType, {}, .host 82⟩] }
  match (runUntilHost 0 ⟨refStore, {}, [.invoke ⟨0⟩ refType]⟩).status with
  | .unsupportedHost call =>
    match resumeHostCall call (.values [.ref (.null .func)]) with
    | .error .unsupportedSignature => pure ()
    | _ => throw (IO.userError "reference signature unexpectedly supported")
  | _ => throw (IO.userError "expected unsupported host diagnostic")
  match (runUntilHost 10 ⟨store, frame, [.invoke ⟨999⟩ type]⟩).status with
  | .ordinary .stuck => pure ()
  | _ => throw (IO.userError "unknown address should be stuck")
  let looping : Configuration := ⟨{}, {}, instructions [.loop (.val none) [.br 0]]⟩
  let first := runUntilHost 3 looping
  let second := runUntilHost 3 first.state
  match first.status, second.status with
  | .ordinary .exhausted, .ordinary .exhausted =>
    checkHost "retained loop state" (!(first.state ≟ looping))
  | _, _ => throw (IO.userError "loop should exhaust and resume")
  -- Guest traps and uncaught exceptions remain ordinary outcomes after reply insertion.
  let trapping : Configuration := ⟨store, frame,
    values [.i64 5] ++ [AdminInstr.invoke ⟨0⟩ type, .instr .unreachable]⟩
  let trapPending ← pendingHost 10 trapping
  let trapResumed ← replyHost trapPending (.values [.i64 42])
  match (runUntilHost 10 trapResumed).status with
  | .ordinary .trapped => pure ()
  | _ => throw (IO.userError "guest trap lost after resumption")
  let throwing : Configuration := ⟨store, frame,
    values [.i64 5] ++ [AdminInstr.invoke ⟨0⟩ type, .throwing ⟨0⟩]⟩
  let exceptionPending ← pendingHost 10 throwing
  let exceptionResumed ← replyHost exceptionPending (.values [.i64 42])
  match (runUntilHost 10 exceptionResumed).status with
  | .ordinary (.exception address) => checkHost "exception address" (address ≟ ⟨0⟩)
  | _ => throw (IO.userError "guest exception lost after resumption")

#print axioms HostSite.decompose
#print axioms HostSite.arguments_typed
#print axioms observeHostCall_sound
#print axioms resumeHostCall_sound
#print axioms HostBoundaryStep.store_preserved
#print axioms resumeHostCall_store_preserved
#print axioms ConfigSteps.toHostExecutionSteps
#print axioms HostExecutionSteps.trans
#print axioms runUntilHost_sound
#print axioms runUntilHost_pending_source
#print axioms runUntilHost_resume_sound

end Wasm.Tests
