import Wasm.Instantiation

namespace Wasm.Tests

private def checkTable (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"table regression failed: {name}")
private def sameTable {α : Type} [BEq α] (actual expected : α) : Bool := actual == expected
local infix:50 " ≟ " => sameTable

private def tableTests : IO Unit := do
  let null := RefValue.null .func
  let f0 := RefValue.func ⟨0⟩
  let f1 := RefValue.func ⟨1⟩
  let owner : ModuleInst :=
    { types := [⟨[.i32], [.i32]⟩], funcs := [⟨0⟩, ⟨1⟩],
      tables := [⟨0⟩, ⟨1⟩], elems := [⟨0⟩] }
  let function : FuncInst := ⟨⟨[.i32], [.i32]⟩, owner,
    .wasm ⟨0, [], [.localGet 0, .const (.i32 1), .binop .i32 .add]⟩⟩
  let wrong : FuncInst := ⟨⟨[], []⟩, owner, .wasm ⟨0, [], []⟩⟩
  let table : TableInst := ⟨⟨.i32, 4, some 6, .func, true⟩, #[f0, f1, null, f0]⟩
  let wide : TableInst := ⟨⟨.i64, 3, some 4, .func, true⟩, #[null, null, null]⟩
  let store : Store :=
    { funcs := [function, wrong], tables := [table, wide],
      elems := [⟨.func, #[f1, f0], true⟩] }
  let run := fun code => runConfiguration 150 ⟨store, { module := owner }, instructions code⟩
  checkTable "reference null" ((run [.refNull .extern, .refIsNull]).status ≟ .finished [.i32 1])
  checkTable "function reference address" ((run [.refFunc 1]).status ≟ .finished [.ref f1])
  checkTable "nonnull function reference"
    ((run [.refFunc 0, .refIsNull]).status ≟ .finished [.i32 0])
  checkTable "external reference" ((run [.const (.ref (.extern 17)), .refIsNull]).status ≟
    .finished [.i32 0])
  checkTable "table get" ((run [.const (.i32 1), .tableGet 0]).status ≟ .finished [.ref f1])
  checkTable "table get bounds" ((run [.const (.i32 4), .tableGet 0]).status ≟ .trapped)
  checkTable "table64 get width" ((run [.const (.i64 0), .tableGet 1]).status ≟
    .finished [.ref null])
  checkTable "wrong address width stuck" ((run [.const (.i32 0), .tableGet 1]).status ≟ .stuck)
  let set := run [.const (.i32 2), .refFunc 0, .tableSet 0, .const (.i32 2), .tableGet 0]
  checkTable "table set" (set.status ≟ .finished [.ref f0])
  checkTable "set updates only chosen table" (set.state.store.tables[1]? ≟ some wide)
  checkTable "table set bounds"
    ((run [.const (.i32 4), .refNull .func, .tableSet 0]).status ≟ .trapped)
  checkTable "table size widths" ((run [.tableSize 0, .tableSize 1]).status ≟
    .finished [.i32 4, .i64 3])
  let grow := run [.refFunc 0, .const (.i32 2), .tableGrow 0, .tableSize 0]
  checkTable "grow returns old length" (grow.status ≟ .finished [.i32 4, .i32 6])
  checkTable "grow fills new slots and updates minimum" (grow.state.store.tables[0]? ≟
    some ⟨⟨.i32, 6, some 6, .func, true⟩, #[f0, f1, null, f0, f0, f0]⟩)
  checkTable "grow maximum failure"
    ((run [.refNull .func, .const (.i32 3), .tableGrow 0]).status ≟
    .finished [.i32 4294967295])
  checkTable "table64 grow" ((run [.refNull .func, .const (.i64 1), .tableGrow 1]).status ≟
    .finished [.i64 3])
  checkTable "table64 grow failure"
    ((run [.refNull .func, .const (.i64 2), .tableGrow 1]).status ≟
    .finished [.i64 18446744073709551615])
  let fill := run [.const (.i32 1), .refFunc 0, .const (.i32 2), .tableFill 0]
  checkTable "fill" (fill.state.store.tables[0]? ≟
    some { table with refs := #[f0, f0, f0, f0] })
  let fillTrap := run [.const (.i32 3), .refNull .func, .const (.i32 2), .tableFill 0]
  checkTable "fill bounds before writes"
    (fillTrap.status ≟ .trapped && fillTrap.state.store ≟ store)
  checkTable "zero fill at endpoint" ((run [.const (.i32 4), .refNull .func,
    .const (.i32 0), .tableFill 0]).status ≟ .finished [])
  checkTable "zero fill beyond endpoint" ((run [.const (.i32 5), .refNull .func,
    .const (.i32 0), .tableFill 0]).status ≟ .trapped)
  let backward := run [.const (.i32 1), .const (.i32 0), .const (.i32 3), .tableCopy 0 0]
  checkTable "overlap backward" (backward.state.store.tables[0]? ≟
    some { table with refs := #[f0, f0, f1, null] })
  let forward := run [.const (.i32 0), .const (.i32 1), .const (.i32 3), .tableCopy 0 0]
  checkTable "overlap forward" (forward.state.store.tables[0]? ≟
    some { table with refs := #[f1, null, f0, f0] })
  let mixed := run [.const (.i64 0), .const (.i32 0), .const (.i32 3), .tableCopy 1 0]
  checkTable "copy mixed widths" (mixed.state.store.tables[1]? ≟
    some { wide with refs := #[f0, f1, null] })
  checkTable "copy validates source on zero length" ((run [.const (.i32 0), .const (.i64 4),
    .const (.i32 0), .tableCopy 0 1]).status ≟ .trapped)
  let init := run [.const (.i32 1), .const (.i32 0), .const (.i32 2), .tableInit 0 0]
  checkTable "element init" (init.state.store.tables[0]? ≟
    some { table with refs := #[f0, f1, f0, f0] })
  checkTable "table64 init uses i32 source and length" ((run [.const (.i64 0),
    .const (.i32 0), .const (.i32 2), .tableInit 1 0]).status ≟ .finished [])
  let drop := run [.elemDrop 0, .elemDrop 0, .const (.i32 0), .const (.i32 0),
    .const (.i32 0), .tableInit 0 0]
  checkTable "drop idempotent zero init" (drop.status ≟ .finished [])
  checkTable "drop retains kind" (drop.state.store.elems ≟ [⟨.func, #[], true⟩])
  checkTable "dropped element source bounds" ((run [.elemDrop 0, .const (.i32 0),
    .const (.i32 1), .const (.i32 0), .tableInit 0 0]).status ≟ .trapped)
  checkTable "indirect call"
    ((run [.const (.i32 41), .const (.i32 0), .callIndirect 0 0]).status ≟
    .finished [.i32 42])
  checkTable "indirect null trap"
    ((run [.const (.i32 41), .const (.i32 2), .callIndirect 0 0]).status ≟
    .trapped)
  checkTable "indirect signature trap" ((run [.const (.i32 41), .const (.i32 1),
    .callIndirect 0 0]).status ≟ .trapped)
  checkTable "indirect bounds trap" ((run [.const (.i32 41), .const (.i32 4),
    .callIndirect 0 0]).status ≟ .trapped)
  let lowered := runConfiguration 1 ⟨store, { module := owner },
    instructions [.const (.i32 41), .const (.i32 0), .callIndirect 0 0]⟩
  checkTable "indirect lowering step" (lowered.state.code ≟
    instructions [.const (.i32 41), .const (.i32 0), .tableGet 0] ++
      [.castFunc ⟨[.i32], [.i32]⟩, .invokeRef ⟨[.i32], [.i32]⟩])
  let lowFuel := runConfiguration 1 ⟨store, { module := owner },
    instructions [.const (.i32 1), .refFunc 0, .const (.i32 2), .tableFill 0]⟩
  checkTable "bulk operation resumable" (lowFuel.status ≟ .exhausted &&
    (runConfiguration 150 lowFuel.state).state ≟ fill.state)
  let external : Store := { tables := [⟨⟨.i32, 1, none, .extern, true⟩, #[.extern 8]⟩] }
  let extRun := runConfiguration 20 ⟨external, { module := { tables := [⟨0⟩] } },
    instructions [.refNull .extern, .const (.i32 1), .tableGrow 0,
      .const (.i32 1), .tableGet 0, .refIsNull]⟩
  checkTable "external table" (extRun.status ≟ .finished [.i32 1, .i32 1])
  let aliases := runConfiguration 150 ⟨store,
    { module := { owner with tables := [⟨0⟩, ⟨0⟩] } },
    instructions [.const (.i32 1), .const (.i32 0), .const (.i32 3), .tableCopy 1 0]⟩
  checkTable "overlap through aliased table indices"
    (aliases.state.store.tables[0]? ≟ backward.state.store.tables[0]?)
  let calleeOwner : ModuleInst := { types := [⟨[], [.ref .func]⟩], tables := [⟨1⟩] }
  let readTable : FuncInst := ⟨⟨[], [.ref .func]⟩, calleeOwner,
    .wasm ⟨0, [], [.const (.i64 0), .tableGet 0]⟩⟩
  let callStore := { store with funcs := [readTable, wrong] }
  let callOwner := { owner with types := [⟨[], [.ref .func]⟩] }
  let read := runConfiguration 30 ⟨callStore, { module := callOwner },
    instructions [.const (.i32 0), .callIndirect 0 0]⟩
  checkTable "indirect callee uses its defining table map" (read.status ≟ .finished [.ref null])
  let nested := runConfiguration 30 ⟨store, { module := owner },
    instructions [.block (.val (some (.ref .func))) [.const (.i32 0), .tableGet 0]]⟩
  checkTable "table access under a label" (nested.status ≟ .finished [.ref f0])
  let nullCast := runConfiguration 3 ⟨store, { module := owner },
    instructions [.const (.i32 41), .const (.i32 2), .callIndirect 0 0]⟩
  checkTable "nullable cast accepts null before invocation"
    (nullCast.state.code ≟ values [.i32 41, .ref null] ++ [.invokeRef ⟨[.i32], [.i32]⟩])
  let budgetStore : Store := { tables := [⟨⟨.i32, 0, none, .func, true⟩, #[]⟩] }
  let budget := runConfiguration 10 ⟨budgetStore, { module := { tables := [⟨0⟩] } },
    instructions [.refNull .func, .const (Value.ofNat .i32 (tableGrowthBudget + 1)),
      .tableGrow 0]⟩
  checkTable "growth resource budget chooses permitted failure"
    (budget.status ≟ .finished [.i32 4294967295] && budget.state.store ≟ budgetStore)

#eval tableTests

example : ReferenceInstrTyping [⟨[], []⟩] [0] (.refFunc 0) [] [.ref .func] :=
  .func rfl (by simp)
example : ¬ ReferenceInstrTyping [⟨[], []⟩] [] (.refFunc 0) [] [.ref .func] := by
  intro h
  cases h with
  | func _ hd => simp at hd
example : TableInstrTyping [⟨[.i32], [.i64]⟩] [⟨.i64, 1, none, .func, true⟩] []
    (.callIndirect 0 0) [.i32, .i64] [.i64] :=
  .indirect (table := ⟨.i64, 1, none, .func, true⟩) (ft := ⟨[.i32], [.i64]⟩) rfl rfl rfl
example : ¬ (ValType.ref .func).IsInteger := by decide
example : InstrTyping (.select (some [.ref .func]))
    [.ref .func, .ref .func, .i32] [.ref .func] := .selectTyped

example : ¬ ReferenceInstrTyping [] [0] (.refFunc 0) [] [.ref .func] := by
  intro h
  cases h with
  | func hf _ => simp at hf
example (input output : List ValType) :
    ¬ TableInstrTyping [⟨[], []⟩] [⟨.i32, 0, none, .extern, true⟩] []
      (.callIndirect 0 0) input output := by
  intro h
  cases h with
  | indirect ht hk _ =>
    simp at ht
    cases ht
    cases hk

example : ¬ TableType.Valid ⟨.ref .func, 0, none, .func, true⟩ := by decide
example : ¬ TableType.Valid ⟨.i32, 4294967296, none, .func, true⟩ := by decide
example : TableType.Valid ⟨.i64, 4294967296, none, .extern, true⟩ := by decide

#print axioms stepTables_sound
#print axioms stepReferences_sound
#print axioms TableStep.functions_preserved
#print axioms TableStep.table_count_preserved
#print axioms ConfigStep.elem_count_preserved
#print axioms Store.dropElem_lookup
#print axioms stepConfiguration_sound

end Wasm.Tests
