import Wasm.Instantiation

namespace Wasm.Tests

private def checkElement (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"element instantiation regression failed: {name}")
private def sameElement {α : Type} [BEq α] (actual expected : α) : Bool := actual == expected
local infix:50 " ≟ " => sameElement

private def referenceModule : Module :=
  { types := [.func ⟨[.i32], [.i32]⟩, .func ⟨[], []⟩],
    funcs := [⟨0, [], [.localGet 0, .const (.i32 1), .binop .i32 .add]⟩,
      ⟨1, [], [.const (.i32 41), .const (.i32 0), .callIndirect 0 0, .globalSet 0]⟩],
    globals := [⟨⟨.var, .i32⟩, [.const (.i32 0)]⟩],
    tables := [⟨⟨.i32, 3, some 5, .func, true⟩, [.refNull .func]⟩],
    elems := [⟨.func, [[.refFunc 0]], .active 0 [.const (.i32 0)], true⟩,
      ⟨.func, [[.refFunc 0]], .passive, true⟩, ⟨.func, [[.refFunc 1]], .declarative, true⟩],
    start := some 1, exports := [⟨"table", .table 0⟩, ⟨"result", .global 0⟩] }

private def referenceContext : FunctionContext :=
  { types := [.func ⟨[.i32], [.i32]⟩, .func ⟨[], []⟩], funcs := [⟨[.i32], [.i32]⟩, ⟨[], []⟩],
    globals := [⟨.var, .i32⟩], tables := [⟨.i32, 3, some 5, .func, true⟩],
    elems := [.func, .func, .func], declaredRefs := [0, 0, 1] }

private theorem referenceModuleValid : referenceModule.Valid := by
  refine ⟨referenceContext, ⟨rfl, by simp [referenceModule, Module.importedMemories],
    by simp [referenceModule], ?_, ?_, by simp [referenceModule], ?_, by decide, ?_,
    by simp [referenceModule, Module.importedTables], ?_, ?_,
    by simp [referenceModule], by decide⟩⟩
  · refine .cons (.cons (.plain (.plain (.plain .const))) .empty) ?_ .empty
    intro i hi
    simp at hi
    subst i
    exact .const
  · intro function hf
    simp [referenceModule] at hf
    rcases hf with rfl | rfl
    · refine ⟨⟨[.i32], [.i32]⟩, .wasm rfl (by decide) ?_⟩
      exact .cons (.plain (.localGet rfl))
        (.cons (.weaken (ts₀ := [.i32]) (.plain (.plain (.plain .const))))
          (.cons (.plain (.plain (.plain .binop))) .empty))
    · refine ⟨⟨[], []⟩, .wasm rfl (by decide) ?_⟩
      exact .cons (.plain (.plain (.plain .const)))
        (.cons (.weaken (ts₀ := [.i32]) (.plain (.plain (.plain .const))))
          (.cons (.tables (.indirect (table := ⟨.i32, 3, some 5, .func, true⟩)
            (ft := ⟨[.i32], [.i32]⟩) rfl rfl rfl))
            (.cons (.global (.set rfl)) .empty)))
  · intro entry he
    simp [referenceModule] at he
    rcases he with rfl | rfl <;> decide
  · intro x hx
    simp [referenceModule] at hx
    subst x
    rfl
  · intro table ht
    simp [referenceModule] at ht
    subst table
    refine ⟨by decide, .cons (.references .null) .empty, ?_⟩
    intro i hi
    simp at hi
    subst i
    exact .refNull
  · intro elem he
    simp [referenceModule] at he
    rcases he with rfl | rfl | rfl
    · refine ⟨?_, ?_, .active (table := ⟨.i32, 3, some 5, .func, true⟩) rfl
        (Types.ValMatches.ref (a := ⟨true, .func⟩) (b := ⟨true, .func⟩) ⟨id, .refl⟩)
        (.cons (.plain (.plain (.plain .const))) .empty) ?_⟩
      · intro expression hx
        simp at hx
        subst expression
        exact .cons (.references (.func (ft := ⟨[.i32], [.i32]⟩) rfl (by decide))) .empty
      · intro expression hx i hi
        simp at hx
        subst expression
        simp at hi
        subst i
        exact .refFunc
      · intro i hi
        simp at hi
        subst i
        exact .const
    · refine ⟨?_, ?_, .passive⟩
      · intro expression hx
        simp at hx
        subst expression
        exact .cons (.references (.func (ft := ⟨[.i32], [.i32]⟩) rfl (by decide))) .empty
      · intro expression hx i hi
        simp at hx
        subst expression
        simp at hi
        subst i
        exact .refFunc
    · refine ⟨?_, ?_, .declarative⟩
      · intro expression hx
        simp at hx
        subst expression
        exact .cons (.references (.func (ft := ⟨[], []⟩) rfl (by decide))) .empty
      · intro expression hx i hi
        simp at hx
        subst expression
        simp at hi
        subst i
        exact .refFunc

private def elementInstantiationTests : IO Unit := do
  let validated : ValidatedModule := ⟨referenceModule, referenceModuleValid⟩
  let .ok result := instantiate 100 {} validated []
    | throw (IO.userError "reference module instantiation failed")
  let final := result.execution.state
  checkElement "start calls active element" (result.execution.status ≟ .finished [] &&
    (final.store.global? ⟨1⟩).map GlobalInst.value ≟ some (.i32 42))
  checkElement "active initialization" (final.store.tables ≟
    [⟨⟨.i32, 3, some 5, .func, true⟩, #[.func ⟨0⟩, .null .func, .null .func]⟩])
  checkElement "active and declarative dropped passive retained" (final.store.elems ≟
    [⟨.func, #[], true⟩, ⟨.func, #[.func ⟨0⟩], true⟩, ⟨.func, #[], true⟩])
  checkElement "table export" (final.frame.module.export? "table" ≟ some (.table ⟨0⟩))
  checkElement "closure captures table and element address maps"
    ((final.store.func? ⟨0⟩).map FuncInst.module ≟ some final.frame.module)
  let .ok suspended := instantiate 0 {} validated []
    | throw (IO.userError "reference module suspension failed")
  checkElement "initialization suspension" (suspended.execution.status ≟ .exhausted)
  checkElement "element expressions evaluated before allocation"
    (suspended.execution.state.store.elems ≟
    [⟨.func, #[.func ⟨0⟩], true⟩, ⟨.func, #[.func ⟨0⟩], true⟩, ⟨.func, #[.func ⟨1⟩], true⟩])
  checkElement "resume reference module"
    ((resumeInstantiation 100 suspended).execution ≟ result.execution)
  let .ok repeated := instantiate 100 final.store validated []
    | throw (IO.userError "reference module repeated instantiation failed")
  checkElement "fresh function references" (repeated.execution.state.store.tables[1]? ≟
    some ⟨⟨.i32, 3, some 5, .func, true⟩, #[.func ⟨2⟩, .null .func, .null .func]⟩)
  checkElement "preserves old table"
    (repeated.execution.state.store.tables[0]? ≟ final.store.tables[0]?)
  let initialized : Module :=
    { types := [.func ⟨[], []⟩], funcs := [⟨0, [], []⟩],
      globals := [⟨⟨.const, .ref .func⟩, [.refFunc 0]⟩],
      tables := [⟨⟨.i64, 2, some 3, .func, true⟩, [.refFunc 0]⟩] }
  let .ok nonnull := checkedPrepareInstantiation final.store initialized []
    | throw (IO.userError "nonnull initializer failed")
  checkElement "table initializer can reference defined functions" (nonnull.val.store.tables[1]? ≟
    some ⟨⟨.i64, 2, some 3, .func, true⟩, #[.func ⟨2⟩, .func ⟨2⟩]⟩)
  checkElement "global initializer can reference defined functions"
    ((nonnull.val.store.globals.getLast?).map GlobalInst.value ≟ some (.ref (.func ⟨2⟩)))
  let importedTable : TableInst := ⟨⟨.i32, 3, some 4, .func, true⟩,
    #[.null .func, .null .func, .null .func]⟩
  let imports : Store :=
    { funcs := [⟨⟨[], []⟩, {}, .wasm ⟨0, [], []⟩⟩],
      tables := [importedTable] }
  let source : Module :=
    { types := [.func ⟨[], []⟩], imports := [⟨"env", "t", .table ⟨.i32, 2, some 5, .func, true⟩⟩,
      ⟨"env", "f", .func 0⟩],
      elems := [⟨.func, [[.refFunc 0]], .active 0 [.const (.i32 0)], true⟩,
        ⟨.func, [[.refFunc 0]], .active 0 [.const (.i32 3)], true⟩],
      exports := [⟨"t", .table 0⟩] }
  let .ok shared := checkedPrepareInstantiation imports source [.table ⟨0⟩, .func ⟨0⟩]
    | throw (IO.userError "table import failed")
  let trapped := runConfiguration 100 shared.val
  checkElement "later active element traps" (trapped.status ≟ .trapped)
  checkElement "earlier imported table writes retained" (trapped.state.store.tables[0]? ≟
    some { importedTable with refs := #[.func ⟨0⟩, .null .func, .null .func] })
  checkElement "earlier drop retained failing element retained" (trapped.state.store.elems ≟
    [⟨.func, #[], true⟩, ⟨.func, #[.func ⟨0⟩], true⟩])
  checkElement "imported table export"
    (shared.val.frame.module.export? "t" ≟ some (.table ⟨0⟩))
  for expected in [TableType.mk .i64 2 (some 5) .func true,
      ⟨.i32, 2, some 5, .extern, true⟩, ⟨.i32, 4, some 5, .func, true⟩, ⟨.i32, 2, some 3, .func, true⟩] do
    checkElement "table import mismatch"
      (!(decide (ImportMatches imports [] (.table expected) (.table ⟨0⟩))))
  checkElement "missing table import" (!(decide (ImportMatches imports []
    (.table ⟨.i32, 0, none, .func, true⟩) (.table ⟨99⟩))))
  checkElement "table allocation budget" (match checkedPrepareInstantiation {}
      { tables := [⟨⟨.i32, tableGrowthBudget + 1, none, .func, true⟩, [.refNull .func]⟩] } [] with
    | .error .resourceLimit => true
    | _ => false)

#eval elementInstantiationTests

#print axioms referenceModuleValid
#print axioms ConstEval.toConfigSteps
#print axioms instantiate_sound
#print axioms RefsEvaluated.length_eq
#print axioms RefsEvaluated.length_eq
#print axioms allocatedStore_preserves_tables
#print axioms allocatedStore_preserves_elements

end Wasm.Tests
