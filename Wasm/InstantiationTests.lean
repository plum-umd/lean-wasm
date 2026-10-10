import Wasm.Instantiation

namespace Wasm.Tests

private def checkInstantiation (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"instantiation regression failed: {name}")
private def sameInstantiation {α : Type} [BEq α] (actual expected : α) : Bool := actual == expected
local infix:50 " ≟ " => sameInstantiation

private def fixture : Module :=
  { types := [⟨[], []⟩],
    imports := [⟨"env", "offset", .global ⟨.const, .i32⟩⟩,
      ⟨"env", "memory", .memory ⟨.i32, 1, some 2⟩⟩],
    globals := [⟨⟨.const, .i32⟩, [.globalGet 0, .const (.i32 1), .binop .i32 .add]⟩,
      ⟨⟨.var, .i32⟩, [.globalGet 1]⟩],
    funcs := [⟨0, [], [.globalGet 1, .load .i32_8U 0 {}, .globalSet 2]⟩],
    mems := [⟨.i64, 0, some 2⟩],
    datas := [⟨#[42, 43], .active 0 [.globalGet 1]⟩, ⟨#[99], .passive⟩],
    start := some 0,
    exports := [⟨"start", .func 0⟩, ⟨"memory", .memory 0⟩, ⟨"wide", .memory 1⟩,
      ⟨"result", .global 2⟩] }

private def fixtureContext : FunctionContext :=
  { types := [⟨[], []⟩], funcs := [⟨[], []⟩],
    globals := [⟨.const, .i32⟩, ⟨.const, .i32⟩, ⟨.var, .i32⟩],
    mems := [⟨.i32, 1, some 2⟩, ⟨.i64, 0, some 2⟩], dataCount := 2, declaredRefs := [0] }

private theorem fixtureValid : fixture.Valid := by
  refine ⟨fixtureContext, ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      by simp [fixture, Module.importedTables], by simp [fixture], by simp [fixture],
      by simp [fixture], by decide⟩⟩
  · intro memory hm
    simp [fixture, Module.importedMemories] at hm
    subst memory
    simp [MemoryType.Valid, MemoryType.pageLimit, ValType.bits, ValType.IsInteger]
  · intro memory hm
    simp [fixture] at hm
    subst memory
    simp [MemoryType.Valid, MemoryType.pageLimit, ValType.bits, ValType.IsInteger]
  · refine .cons (.cons (.global (.get (gt := ⟨.const, .i32⟩) rfl))
      (.cons (.weaken (ts₀ := [.i32]) (.plain (.plain (.plain .const))))
        (.cons (.plain (.plain (.plain .binop))) .empty))) ?_ ?_
    · intro i hi
      simp at hi
      rcases hi with rfl | rfl | rfl
      · exact .global (type := .i32) rfl
      · exact .const
      · exact .binop
    · refine .cons (.cons (.global (.get (gt := ⟨.const, .i32⟩) rfl)) .empty) ?_ .empty
      intro i hi
      simp at hi
      subst i
      exact .global (type := .i32) rfl
  · intro function hf
    simp [fixture] at hf
    subst function
    refine ⟨⟨[], []⟩, .wasm rfl (by decide) ?_⟩
    exact .cons (.global (.get (gt := ⟨.const, .i32⟩) rfl))
      (.cons (.memory (.load (memoryType := ⟨.i32, 1, some 2⟩) rfl (by decide)))
        (.cons (.global (.set rfl)) .empty))
  · intro segment hs
    simp [fixture] at hs
    rcases hs with rfl | rfl
    · refine .active (memory := ⟨.i32, 1, some 2⟩) rfl
        (.cons (.global (.get (gt := ⟨.const, .i32⟩) rfl)) .empty) ?_
      intro i hi
      simp at hi
      subst i
      exact .global (type := .i32) rfl
    · exact .passive
  · intro entry he
    simp [fixture] at he
    rcases he with rfl | rfl | rfl | rfl <;> decide
  · decide
  · intro x hx
    simp [fixture] at hx
    subst x
    rfl

private def singleFunctionModule (body : List Instr) : Module :=
  { types := [⟨[], []⟩], funcs := [⟨0, [], body⟩], start := some 0,
    exports := [⟨"run", .func 0⟩] }

private theorem singleFunctionValid
    (scope : instructionsInScope 0 body = true)
    (hi : (Func.mk 0 [] body).Initialized ⟨[], []⟩)
    (hb : RuntimeSeqTyping { types := [⟨[], []⟩], funcs := [⟨[], []⟩], returns := some [], declaredRefs := [0] }
      [[]] body [] []) : (singleFunctionModule body).Valid := by
  refine ⟨{ types := [⟨[], []⟩], funcs := [⟨[], []⟩], declaredRefs := [0] },
    ⟨rfl, by simp [singleFunctionModule, Module.importedMemories],
      by simp [singleFunctionModule], .empty, ?_,
      by simp [singleFunctionModule], ?_, by simp [singleFunctionModule], ?_,
      by simp [singleFunctionModule, Module.importedTables],
      by simp [singleFunctionModule], by simp [singleFunctionModule],
      by simp [singleFunctionModule],
      by simpa [Module.referencesInScope, singleFunctionModule] using scope⟩⟩
  · intro function hf
    simp [singleFunctionModule] at hf
    subst function
    exact ⟨⟨[], []⟩, .wasm rfl hi hb⟩
  · intro entry he
    simp [singleFunctionModule] at he
    subst entry
    decide
  · intro x hx
    simp [singleFunctionModule] at hx
    subst x
    rfl

private def dataModule (segments : List Data) : Module :=
  { imports := [⟨"env", "memory", .memory ⟨.i32, 1, none⟩⟩], datas := segments }

private theorem dataModuleValid
    (hs : ∀ segment ∈ segments,
      DataTyping { mems := [⟨.i32, 1, none⟩], dataCount := segments.length } segment) :
    (dataModule segments).Valid := by
  refine ⟨{ mems := [⟨.i32, 1, none⟩], dataCount := segments.length },
    ⟨rfl, ?_, by simp [dataModule], .empty, by simp [dataModule], hs,
      by simp [dataModule], by simp [dataModule], by simp [dataModule],
      by simp [dataModule, Module.importedTables], by simp [dataModule], by simp [dataModule],
      by simp [dataModule], by simp [dataModule, Module.referencesInScope]⟩⟩
  intro memory hm
  simp [dataModule, Module.importedMemories] at hm
  subst memory
  simp [MemoryType.Valid, MemoryType.pageLimit, ValType.bits, ValType.IsInteger]

private theorem constantDataTyping : DataTyping
    { mems := [⟨.i32, 1, none⟩], dataCount := count }
    ⟨bytes, .active 0 [.const (.i32 offset)]⟩ := by
  refine .active (memory := ⟨.i32, 1, none⟩) rfl
    (.cons (.plain (.plain (.plain .const))) .empty) ?_
  intro i hi
  simp at hi
  subst i
  exact .const

private def instantiationTests : IO Unit := do
  let memory : MemoryInst := ⟨⟨.i32, 1, some 2⟩, Array.replicate pageSize 0⟩
  let existing : FuncInst := ⟨⟨[], []⟩, {}, .host 7⟩
  let store : Store :=
    { funcs := [existing], globals := [⟨⟨.const, .i32⟩, .i32 3⟩],
      mems := [memory], datas := [⟨#[7]⟩] }
  let addresses := [ExternAddr.global ⟨0⟩, .memory ⟨0⟩]
  let validated : ValidatedModule := ⟨fixture, fixtureValid⟩
  let .ok result := instantiate 100 store validated addresses
    | throw (IO.userError "fixture preparation failed")
  let final := result.execution.state
  checkInstantiation "initializers and start finish" (result.execution.status ≟ .finished [])
  checkInstantiation "module published on success" (result.module? ≟ some final.frame.module)
  checkInstantiation "function addresses after existing functions"
    (final.frame.module.funcs ≟ [⟨1⟩])
  checkInstantiation "formal temporary and final globals" (final.store.globals.length ≟ 5)
  checkInstantiation "final global address map" (final.frame.module.globals ≟ [⟨0⟩, ⟨3⟩, ⟨4⟩])
  checkInstantiation "earlier global expression" (final.store.global? ⟨3⟩ ≟
    some ⟨⟨.const, .i32⟩, .i32 4⟩)
  checkInstantiation "start observes initialized data" (final.store.global? ⟨4⟩ ≟
    some ⟨⟨.var, .i32⟩, .i32 42⟩)
  checkInstantiation "temporary globals retain initializer values" (final.store.global? ⟨2⟩ ≟
    some ⟨⟨.var, .i32⟩, .i32 4⟩)
  checkInstantiation "imported memory is shared"
    ((final.store.mems[0]?.getD memory).read 4 2 ≟ #[42, 43])
  checkInstantiation "memory64 allocation" (final.store.mem? ⟨1⟩ ≟ some ⟨⟨.i64, 0, some 2⟩, #[]⟩)
  checkInstantiation "segments retain index order" (final.frame.module.datas ≟ [⟨1⟩, ⟨2⟩])
  checkInstantiation "active dropped passive retained" (final.store.datas ≟
    [⟨#[7]⟩, ⟨#[]⟩, ⟨#[99]⟩])
  checkInstantiation "exports use addresses" (final.frame.module.export? "result" ≟
    some (.global ⟨4⟩))
  checkInstantiation "imported export" (final.frame.module.export? "memory" ≟
    some (.memory ⟨0⟩))
  checkInstantiation "closure captures complete instance"
    ((final.store.func? ⟨1⟩).map FuncInst.module ≟ some final.frame.module)
  checkInstantiation "old function preserved" (final.store.func? ⟨0⟩ ≟ some existing)
  checkInstantiation "imported global preserved" (final.store.global? ⟨0⟩ ≟ store.global? ⟨0⟩)
  for wrong in [[], [ExternAddr.global ⟨0⟩], addresses ++ [.memory ⟨0⟩],
      [ExternAddr.memory ⟨0⟩, .global ⟨0⟩], [ExternAddr.global ⟨99⟩, .memory ⟨0⟩]] do
    match instantiate 10 store validated wrong with
    | .error .imports => pure ()
    | _ => throw (IO.userError "bad imports accepted")
  let wrongGlobal : Store := { store with globals := [⟨⟨.var, .i32⟩, .i32 3⟩] }
  checkInstantiation "global import mutability"
    (match instantiate 10 wrongGlobal validated addresses with
      | .error .imports => true
      | _ => false)
  let .ok suspended := instantiate 0 store validated addresses
    | throw (IO.userError "zero fuel preparation failed")
  checkInstantiation "zero fuel returns residual" (suspended.execution.status ≟ .exhausted)
  checkInstantiation "residual not published" (suspended.module? ≟ none)
  checkInstantiation "resume initialization" ((resumeInstantiation 100 suspended).execution ≟
    result.execution)
  let .ok again := instantiate 100 final.store validated addresses
    | throw (IO.userError "second instantiation failed")
  checkInstantiation "fresh function on repeated instantiation"
    (again.execution.state.frame.module.funcs ≟ [⟨2⟩])
  checkInstantiation "existing closure remains unchanged" (again.execution.state.store.func? ⟨1⟩ ≟
    final.store.func? ⟨1⟩)
  let trapModule : ValidatedModule := ⟨singleFunctionModule [.unreachable],
    singleFunctionValid (by decide) (by decide) (.cons (.plain (.plain (.plain .unreachable))) .empty)⟩
  let .ok trapped := instantiate 20 {} trapModule []
    | throw (IO.userError "trapping start preparation failed")
  checkInstantiation "start trap" (trapped.execution.status ≟ .trapped)
  checkInstantiation "trap retains allocated function"
    (trapped.execution.state.store.funcs.length ≟ 1)
  checkInstantiation "trapped module not published" (trapped.module? ≟ none)
  let recursive : ValidatedModule := ⟨singleFunctionModule [.call 0],
    singleFunctionValid (by decide) (by decide) (.cons (.call (ft := ⟨[], []⟩) rfl) .empty)⟩
  let .ok exhausted := instantiate 12 {} recursive []
    | throw (IO.userError "recursive start preparation failed")
  checkInstantiation "recursive start exhaustion" (exhausted.execution.status ≟ .exhausted)
  let empty : Module := {}
  let emptyValid : empty.Valid := ⟨{}, ⟨rfl, by simp [empty, Module.importedMemories],
    by simp [empty], .empty, by simp [empty], by simp [empty], by simp [empty],
    by simp [empty], by simp [empty], by simp [empty, Module.importedTables],
    by simp [empty], by simp [empty], by simp [empty], by decide⟩⟩
  let .ok noCode := instantiate 0 store ⟨empty, emptyValid⟩ []
    | throw (IO.userError "empty module failed")
  checkInstantiation "empty module zero fuel" (noCode.execution.status ≟ .finished [])
  checkInstantiation "empty module preserves store" (noCode.execution.state.store ≟ store)
  let failingStore : Store :=
    { store with globals := [⟨⟨.const, .i32⟩, Value.ofNat .i32 (pageSize - 2)⟩] }
  let .ok failedInit := instantiate 100 failingStore validated addresses
    | throw (IO.userError "active segment trap preparation failed")
  checkInstantiation "active segment bounds trap" (failedInit.execution.status ≟ .trapped)
  checkInstantiation "failed initializer does not write partial bytes"
    (failedInit.execution.state.store.mems[0]? ≟ some memory)
  checkInstantiation "failed initializer does not drop segment"
    (failedInit.execution.state.store.data? ⟨1⟩ ≟ some ⟨#[42, 43]⟩)
  checkInstantiation "failed initializer prevents start"
    (failedInit.execution.state.store.global? ⟨4⟩ ≟
      some ⟨⟨.var, .i32⟩, Value.ofNat .i32 (pageSize - 1)⟩)
  let sequential : List Data :=
    [⟨#[11], .active 0 [.const (.i32 4)]⟩,
      ⟨#[12], .active 0 [.const (.i32 65536)]⟩]
  let seqValid : (dataModule sequential).Valid := by
    apply dataModuleValid
    intro segment hs
    simp [sequential] at hs
    rcases hs with rfl | rfl <;> exact constantDataTyping
  let .ok seqResult := instantiate 100 store ⟨dataModule sequential, seqValid⟩ [.memory ⟨0⟩]
    | throw (IO.userError "sequential segments failed")
  checkInstantiation "later segment trap" (seqResult.execution.status ≟ .trapped)
  checkInstantiation "earlier imported memory writes retained"
    ((seqResult.execution.state.store.mems[0]?.getD memory).read 4 1 ≟ #[11])
  checkInstantiation "earlier drop retained later segment retained"
    (seqResult.execution.state.store.datas ≟ [⟨#[7]⟩, ⟨#[]⟩, ⟨#[12]⟩])
  let mixed : Module :=
    { types := [⟨[], []⟩], imports := [⟨"env", "f", .func 0⟩,
      ⟨"env", "m", .memory ⟨.i32, 1, none⟩⟩, ⟨"env", "g", .global ⟨.const, .i32⟩⟩,
      ⟨"env", "f2", .func 0⟩] }
  let .ok imported := checkedPrepareInstantiation store mixed
      [.func ⟨0⟩, .memory ⟨0⟩, .global ⟨0⟩, .func ⟨0⟩]
    | throw (IO.userError "mixed import preparation failed")
  checkInstantiation "mixed imports preserve per-kind order"
    (imported.val.frame.module.funcs ≟ [⟨0⟩, ⟨0⟩])
  checkInstantiation "mixed imports globals" (imported.val.frame.module.globals ≟ [⟨0⟩])
  checkInstantiation "mixed imports memory" (imported.val.frame.module.mems ≟ [⟨0⟩])
  let definedMemories : Module := { mems := [⟨.i32, 1, none⟩, ⟨.i64, 1, some 2⟩] }
  let .ok allocated := checkedPrepareInstantiation store definedMemories []
    | throw (IO.userError "memory allocation failed")
  checkInstantiation "defined memory maps" (allocated.val.frame.module.mems ≟ [⟨1⟩, ⟨2⟩])
  for index in [1, 2] do
    checkInstantiation "defined memory starts zero-filled"
      ((allocated.val.store.mems[index]?.getD memory).bytes ≟ Array.replicate pageSize 0)
  checkInstantiation "allocation resource limit"
    (match checkedPrepareInstantiation store { mems := [⟨.i64, growthBudgetPages + 1, none⟩] } [] with
      | .error .resourceLimit => true
      | _ => false)
  checkInstantiation "explicit smaller allocation budget"
    (match checkedPrepareInstantiation store definedMemories [] 0 with
      | .error .resourceLimit => true
      | _ => false)
  let forward : Module :=
    { types := [⟨[], []⟩], funcs := [⟨0, [], [.call 1]⟩, ⟨0, [], [.nop]⟩], start := some 0 }
  let .ok preparedForward := checkedPrepareInstantiation store forward []
    | throw (IO.userError "forward call allocation failed")
  checkInstantiation "forward function call"
    ((runConfiguration 30 preparedForward.val).status ≟ .finished [])
  let badFunc : Module := { imports := [⟨"env", "f", .func 0⟩] }
  checkInstantiation "invalid imported type index" (badFunc.context? ≟ none)
  checkInstantiation "missing function import address"
    (!(decide (ImportMatches store [⟨[], []⟩] (.func 0) (.func ⟨99⟩))))
  checkInstantiation "function import signature mismatch"
    (!(decide (ImportMatches store [⟨[.i32], []⟩] (.func 0) (.func ⟨0⟩))))
  checkInstantiation "memory import missing required maximum"
    (!(decide (ImportMatches { mems := [{ memory with type := ⟨.i32, 1, none⟩ }] } []
      (.memory ⟨.i32, 1, some 2⟩) (.memory ⟨0⟩))))
  let badConst := evalConst store {} [.unreachable]
  checkInstantiation "constant evaluator rejects nonconstant instructions" badConst.isNone
  checkInstantiation "constant evaluator operand order"
    ((evalConst {} {} [.const (.i64 8), .const (.i64 3), .binop .i64 .sub]).map Subtype.val ≟
      some (.i64 5))

#eval instantiationTests

example : MemoryType.Matches ⟨.i32, 2, some 3⟩ ⟨.i32, 1, some 4⟩ := by decide
example : ¬ MemoryType.Matches ⟨.i64, 2, some 3⟩ ⟨.i32, 1, some 4⟩ := by decide
example : ¬ MemoryType.Matches ⟨.i32, 2, none⟩ ⟨.i32, 1, some 4⟩ := by decide
example : ¬ MemoryType.Matches ⟨.i32, 0, some 3⟩ ⟨.i32, 1, some 4⟩ := by decide
example : ¬ MemoryType.Matches ⟨.i32, 2, some 5⟩ ⟨.i32, 1, some 4⟩ := by decide

#print axioms ConstEval.toConfigSteps
#print axioms instantiate_sound
#print axioms instantiate_finished
#print axioms allocatedStore_preserves_functions
#print axioms allocatedStore_preserves_memories

end Wasm.Tests
