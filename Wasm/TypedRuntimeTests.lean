import Wasm.Instantiation

namespace Wasm.Tests.TypedReferences

private def signature : FuncType := ⟨[.i32], [.i32]⟩
private def parent : Types.DefinedType := ⟨[.func false [] [.i32] [.i32]], 0⟩
private def child : Types.DefinedType := ⟨[.func true [parent.heap] [.i32] [.i32]], 0⟩
private def unrelated : Types.DefinedType := ⟨[.func true [] [.i32] [.i32]], 0⟩

private theorem child_matches_parent (ctx : Types.Context) :
    Types.HeapMatches ctx child.heap parent.heap :=
  .defined (a := child) (b := parent)
    (.super rfl (by simp [child, parent, Types.SubType.supers, Types.SubType.mapHeap,
      Types.HeapType.substRecs, Types.DefinedType.heap]) .refl)

private def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"typed reference regression failed: {name}")

private def equal {α : Type} [BEq α] (actual expected : α) : Bool := actual == expected
local infix:50 " ≟ " => equal

#eval do
  let owner : ModuleInst := {
    types := [signature, signature, signature],
    definedTypes := [parent, child, unrelated], funcs := [⟨0⟩, ⟨1⟩] }
  let function : FuncInst := ⟨signature, owner,
    .wasm ⟨1, [], [.localGet 0, .const (.i32 1), .binop .i32 .add]⟩⟩
  let wrong : FuncInst := ⟨signature, owner, .wasm ⟨2, [], [.localGet 0]⟩⟩
  let tableType : TableType := {
    addrType := .i32, min := 2,
    kind := parent.heap, nullable := false }
  let globalType : GlobalType := ⟨.var, .refNonNull parent.heap⟩
  let store : Store := {
    funcs := [function, wrong],
    tables := [⟨tableType, #[.func ⟨0⟩, .func ⟨0⟩]⟩],
    globals := [⟨globalType, .ref (.func ⟨0⟩)⟩] }
  let caller : Frame := { module := { owner with tables := [⟨0⟩], globals := [⟨0⟩] } }
  check "store-dependent concrete type"
    ((RefValue.func ⟨0⟩).type? store ≟ some (.refNonNull child.heap))
  check "declared supertype"
    ((checkValue store (.ref (.func ⟨0⟩)) (.refNonNull parent.heap)).isSome)
  check "same signature does not declare a subtype"
    (!(checkValue store (.ref (.func ⟨1⟩)) (.refNonNull parent.heap)).isSome)
  check "dangling function reference"
    (!(checkValue store (.ref (.func ⟨99⟩)) (.ref .func)).isSome)
  check "typed nullable null"
    ((checkValue store (.ref (.null parent.heap)) (.ref parent.heap)).isSome)
  check "nonnull null rejection"
    (!(checkValue store (.ref (.null parent.heap)) (.refNonNull parent.heap)).isSome)
  check "external hierarchy stays separate"
    (!(checkValue store (.ref (.extern 0)) (.ref .func)).isSome)
  check "empty external heap null"
    ((checkValue store (.ref (.null .noextern)) (.ref .extern)).isSome)

  let invoke (ref : RefValue) : Configuration :=
    ⟨{ store with tables := [⟨{ tableType with nullable := true }, #[ref]⟩] }, caller,
      instructions [.const (.i32 41), .const (.i32 0), .callIndirect 0 0]⟩
  check "indirect declared subtype"
    ((runConfiguration 30 (invoke (.func ⟨0⟩))).status ≟ .finished [.i32 42])
  check "indirect unrelated signature trap"
    ((runConfiguration 30 (invoke (.func ⟨1⟩))).status ≟ .trapped)
  check "indirect typed null trap"
    ((runConfiguration 30 (invoke (.null parent.heap))).status ≟ .trapped)
  let legacyCaller : Frame := { module := { types := [signature], tables := [⟨0⟩] } }
  let legacy (ref : RefValue) : Configuration :=
    ⟨{ store with tables := [⟨{ tableType with kind := .func, nullable := true }, #[ref]⟩] },
      legacyCaller, instructions [.const (.i32 41), .const (.i32 0), .callIndirect 0 0]⟩
  check "legacy cast respects final type identity"
    ((runConfiguration 30 (legacy (.func ⟨0⟩))).status ≟ .trapped)
  check "legacy cast accepts identical final group"
    ((runConfiguration 30 (legacy (.func ⟨1⟩))).status ≟ .finished [.i32 41])
  let cast := stepReferences store caller
    (values [.ref (.func ⟨0⟩)] ++ [AdminInstr.castDefined parent])
  check "cast preserves address" (cast ≟ some (values [.ref (.func ⟨0⟩)]))

  let argsType : FuncType := ⟨[.refNonNull parent.heap], [.i32]⟩
  let argsOwner : ModuleInst := {
    types := [argsType], funcs := [⟨2⟩] }
  let takesRef : FuncInst := ⟨argsType, argsOwner,
    .wasm ⟨0, [.refNonNull parent.heap],
      [.localGet 0, .localSet 1, .localGet 1, .drop, .const (.i32 7)]⟩⟩
  let withCallee := { store with funcs := store.funcs ++ [takesRef] }
  check "subtype argument activation"
    (takesRef.activation? [.ref (.func ⟨0⟩)] withCallee).isSome
  check "null argument activation rejection"
    (!(takesRef.activation? [.ref (.null parent.heap)] withCallee).isSome)
  let frame := Frame.initialize argsOwner [.ref (.func ⟨0⟩)]
    [.refNonNull parent.heap, .ref parent.heap]
  check "nonnull locals begin unset"
    (frame.locals ≟ [some (.ref (.func ⟨0⟩)), none, some (.ref (.null parent.heap))])
  check "unset local get is stuck" (stepLocals frame (instructions [.localGet 1]) ≟ none)
  let direct : Configuration := ⟨withCallee, { module := argsOwner },
    instructions [.const (.ref (.func ⟨0⟩)), .call 0]⟩
  check "typed direct call and local initialization"
    ((runConfiguration 30 direct).status ≟ .finished [.i32 7])

  check "typed table set subtype" (stepTables store caller
    (instructions [.const (.i32 1), .const (.ref (.func ⟨0⟩)), .tableSet 0])).isSome
  check "nonnull table set rejects null" (!(stepTables store caller
    (instructions [.const (.i32 1), .const (.ref (.null parent.heap)), .tableSet 0])).isSome)
  check "typed table fill subtype" (stepTables store caller
    (instructions [.const (.i32 0), .const (.ref (.func ⟨0⟩)),
      .const (.i32 2), .tableFill 0])).isSome
  check "typed table grow subtype" (stepTables store caller
    (instructions [.const (.ref (.func ⟨0⟩)), .const (.i32 1), .tableGrow 0])).isSome
  check "typed global set subtype" (stepGlobals store caller
    (instructions [.const (.ref (.func ⟨0⟩)), .globalSet 0])).isSome
  check "typed global set rejects null" (!(stepGlobals store caller
    (instructions [.const (.ref (.null parent.heap)), .globalSet 0])).isSome)

  check "function import subtype"
    (decide (ImportMatches store [signature] (.func 0) (.func ⟨0⟩) [parent]))
  let immutable : Store := { store with globals :=
    [⟨⟨.const, .refNonNull child.heap⟩, .ref (.func ⟨0⟩)⟩] }
  check "immutable global import covariance" (decide (ImportMatches immutable []
    (.global ⟨.const, .ref parent.heap⟩) (.global ⟨0⟩)))
  let mutable := { immutable with globals :=
    [⟨⟨.var, .refNonNull child.heap⟩, .ref (.func ⟨0⟩)⟩] }
  check "mutable global import invariant" (!(decide (ImportMatches mutable []
    (.global ⟨.var, .ref parent.heap⟩) (.global ⟨0⟩))))
  check "table import reference type invariant" (!(decide (ImportMatches store []
    (.table { tableType with kind := child.heap }) (.table ⟨0⟩))))
  check "table import nullability invariant" (!(decide (ImportMatches store []
    (.table { tableType with nullable := true }) (.table ⟨0⟩))))

-- Initialization effects are sequential, and do not escape structured instructions.
example : ¬ (Func.mk 0 [.refNonNull .func] [.localGet 0]).Initialized ⟨[], []⟩ := by decide
example : (Func.mk 0 [.refNonNull .func]
    [.refFunc 0, .localTee 0, .drop, .localGet 0, .drop]).Initialized ⟨[], []⟩ := by decide
example : ¬ (Func.mk 0 [.refNonNull .func]
    [.block (.val none) [.refFunc 0, .localSet 0], .localGet 0]).Initialized ⟨[], []⟩ :=
  by decide
example : (Func.mk 0 [] [.localGet 0, .drop]).Initialized ⟨[.refNonNull .func], []⟩ := by decide

example : ¬ FuncTyping [.func ⟨[], []⟩] [] [] [] 0
    ⟨0, [.refNonNull .func], [.localGet 0, .drop]⟩ ⟨[], []⟩ := by
  intro h
  have initialized := h.initialized
  exact (by decide : ¬ (Func.mk 0 [.refNonNull .func]
    [.localGet 0, .drop]).Initialized ⟨[], []⟩) initialized

example : ReferenceInstrTyping [signature] [0] (.refFunc 0) [] [.refNonNull .func] :=
  .funcNonNull rfl (by decide)

example : (Types.searchHeap 0 {} child.heap parent.heap).isRejected = false := rfl

#eval do
  let typedHost : FuncInst := ⟨signature, {}, .hostTyped 10 child⟩
  let store : Store := { funcs := [typedHost] }
  check "typed host retains recursive identity" (typedHost.runtimeType ≟ child)
  check "typed host reference subtype"
    ((checkValue store (.ref (.func ⟨0⟩)) (.refNonNull parent.heap)).isSome)
  check "typed host invocation unavailable" (typedHost.activation? [.i32 0] store ≟ none)
  let recContext : Types.Context := { recs :=
    [.func false [] [] [], .func false [.recIdx 0] [] [], .func true [.recIdx 1] [] []] }
  check "transitive recursion-index supertypes"
    ((Types.checkHeap 20 recContext (.recIdx 2) (.recIdx 0)).isSome)

private def parentGroup : Types.RecType := [.func false [] [.i32] [.i32]]
private def childGroup : Types.RecType := [.func true [.typeIdx 0] [.i32] [.i32]]

private theorem parent_closed : parent.closed := by
  refine ⟨20, ?_⟩
  simp [parent, Types.DefinedType.heap,
    Types.HeapType.scopedFuel, Types.ValType.scopedFuel, Types.SubType.scopedFuel]

private theorem child_closed : child.closed := by
  refine ⟨20, ?_⟩
  simp [child, parent, Types.DefinedType.heap,
    Types.HeapType.scopedFuel, Types.ValType.scopedFuel, Types.SubType.scopedFuel]

private theorem groups_valid :
    Types.TypeSectionValid [] [parentGroup, childGroup] [parent, child] := by
  apply Types.TypeSectionValid.cons (resolved := [parent])
  · simp [parentGroup, parent, Types.RecType.resolve?, Types.RecType.roll,
      Types.SubType.substTypes, Types.ValType.substTypes, Types.SubType.close?,
      Types.ValType.close?, Types.RecType.projections]
  · intro type member
    simp at member
    subst type
    exact parent_closed
  · intro i sub lookup
    cases i with
    | zero =>
      simp [parentGroup] at lookup
      subst sub
      constructor
      · rfl
      · decide
      · simp [Types.SubType.body, Types.CompType.valTypes, Types.ValType.Valid]
      · simp [Types.SubType.supers]
    | succ i => simp [parentGroup] at lookup
  · apply Types.TypeSectionValid.cons (resolved := [child])
    · simp [childGroup, child, parent, Types.RecType.resolve?, Types.RecType.roll,
        Types.SubType.substTypes, Types.ValType.substTypes, Types.HeapType.substTypes,
        Types.rollIndex, Types.SubType.close?, Types.ValType.close?, Types.HeapType.close?,
        Types.DefinedType.heap, Types.RecType.projections]
    · intro type member
      simp at member
      subst type
      exact child_closed
    · intro i sub lookup
      cases i with
      | zero =>
        simp [childGroup] at lookup
        subst sub
        constructor
        · rfl
        · decide
        · simp [Types.SubType.body, Types.CompType.valTypes, Types.ValType.Valid]
        · intro super member
          simp [Types.SubType.supers] at member
          subst super
          exact ⟨0, parent, .func false [] [.i32] [.i32], rfl, by decide, rfl, rfl, rfl,
             .func ⟨.cons .i32 .nil, .cons .i32 .nil⟩⟩
      | succ i => simp [childGroup] at lookup
    · exact .nil

private def sourceModule : Module :=
  { types := [signature, signature], typeGroups := [parentGroup, childGroup],
    funcs := [⟨1, [], [.localGet 0, .const (.i32 1), .binop .i32 .add]⟩],
    globals := [⟨⟨.var, .refNonNull (.typeIdx 0)⟩, [.refFunc 0]⟩],
    tables := [⟨{ addrType := .i32, min := 1, kind := .typeIdx 0, nullable := false },
      [.refFunc 0]⟩],
    elems := [⟨.typeIdx 1, [[.refFunc 0]], .active 0 [.const (.i32 0)], false⟩],
    exports := [⟨"f", .func 0⟩] }

private def sourceContext : FunctionContext :=
  { types := [signature, signature], funcs := [signature],
    globals := [⟨.var, .refNonNull (.typeIdx 0)⟩],
    tables := [{ addrType := .i32, min := 1, kind := .typeIdx 0, nullable := false }],
    declaredRefs := [0, 0, 0, 0], definedTypes := [parent, child], funcTypeIndices := [1],
    elems := [.typeIdx 1], elemTypes := [.refNonNull (.typeIdx 1)] }

private theorem source_initializer (ctx : FunctionContext)
    (funcs : ctx.funcs[0]? = some signature) (indices : ctx.funcTypeIndices[0]? = some 1)
    (declared : 0 ∈ ctx.declaredRefs) (types : ctx.definedTypes = [parent, child]) :
    RuntimeSeqTyping ctx [] [.refFunc 0] [] [.refNonNull (.typeIdx 0)] := by
  apply RuntimeSeqTyping.subtype
    (.cons (.typedFunc funcs indices declared) .empty) Types.ResultMatches.nil
  refine .cons (.ref (a := ⟨false, .typeIdx 1⟩) (b := ⟨false, .typeIdx 0⟩)
    ⟨by simp, ?_⟩) .nil
  exact .indexLeft (by simp [types])
    (.indexRight (by simp [types]) (child_matches_parent _))

private theorem source_valid : sourceModule.Valid := by
  refine ⟨sourceContext, ?_⟩
  constructor
  · simp [sourceModule, sourceContext, Module.context?, TypeContext.func?, CompositeType.func?, Module.importedFuncIndices, Module.importedTagIndices,
      Module.importedGlobals, Module.importedMemories, Module.importedTables,
      Module.declaredRefs, expressionFuncIndices, Elem.refType, Types.resolveSection?,
      Types.RecType.resolve?, Types.RecType.roll, parentGroup, childGroup, parent, child,
      Types.SubType.substTypes, Types.ValType.substTypes, Types.HeapType.substTypes,
      Types.rollIndex, Types.SubType.close?, Types.ValType.close?, Types.HeapType.close?,
      Types.RecType.projections, Types.DefinedType.heap]
  · simp [sourceModule, Module.importedMemories]
  · simp [sourceModule]
  · refine .cons (source_initializer _ rfl rfl (by decide) rfl) ?_ .empty
    intro instr member
    simp at member
    subst instr
    exact .refFunc
  · intro function member
    simp [sourceModule] at member
    subst function
    refine ⟨signature, .wasm rfl (by decide) ?_⟩
    exact .cons (.plain (.localGet rfl))
      (.cons (.weaken (ts₀ := [.i32]) (.plain (.plain (.plain .const))))
        (.cons (.plain (.plain (.plain .binop))) .empty))
  · simp [sourceModule]
  · intro entry member
    simp [sourceModule] at member
    subst entry
    decide
  · simp [sourceModule]
  · simp [sourceModule]
  · simp [sourceModule, Module.importedTables]
  · intro table member
    simp [sourceModule] at member
    subst table
    refine ⟨by decide, source_initializer _ rfl rfl (by decide) rfl, ?_⟩
    intro instr member
    simp at member
    subst instr
    exact .refFunc
  · intro elem member
    simp [sourceModule] at member
    subst elem
    refine ⟨?_, ?_, .active (table :=
      { addrType := .i32, min := 1, kind := .typeIdx 0, nullable := false }) rfl ?_
      (.cons (.plain (.plain (.plain .const))) .empty) ?_⟩
    · intro expression member
      simp at member
      subst expression
      exact .cons (.typedFunc (ft := signature) rfl rfl (by decide)) .empty
    · intro expression member instr found
      simp at member
      subst expression
      simp at found
      subst instr
      exact .refFunc
    · refine .ref (a := ⟨false, .typeIdx 1⟩) (b := ⟨false, .typeIdx 0⟩) ⟨by simp, ?_⟩
      exact .indexLeft rfl (.indexRight rfl (child_matches_parent _))
    · intro instr member
      simp at member
      subst instr
      exact .const
  · intro _
    refine ⟨groups_valid, ?_⟩
    simp [sourceModule, parentGroup, childGroup, signature, Types.SubType.body,
      Types.embedComposite, Types.embedFunc, Types.embedVal]
  · decide

#eval do
  let .ok result := instantiate 20 {} ⟨sourceModule, source_valid⟩ []
    | throw (IO.userError "typed source module instantiation failed")
  check "typed source instantiation finished" (result.execution.status ≟ .finished [])
  let owner := result.execution.state.frame.module
  let store := result.execution.state.store
  check "closed recursive type identity" (owner.definedTypes ≟ [parent, child])
  check "forward typed global initializer" (match store.resolveGlobal? owner 0 with
    | some global => global.type.valType == ValType.refNonNull parent.heap &&
        (checkValue store global.value global.type.valType).isSome
    | none => false)
  check "forward nonnull table initializer" (match store.resolveTable? owner 0 with
    | some table => table.type.refType == ValType.refNonNull parent.heap &&
        table.refs == #[RefValue.func ⟨0⟩]
    | none => false)
  let indirect : Configuration := ⟨store, { module := owner },
    instructions [.const (.i32 9), .const (.i32 0), .callIndirect 0 0]⟩
  check "instantiated typed indirect call"
    ((runConfiguration 30 indirect).status ≟ .finished [.i32 10])
  let nullOwner := { owner with types := [.func ⟨[], []⟩] }
  let typedNull := stepReferences store { module := nullOwner }
    (instructions [.refNull (.typeIdx 0)])
  check "ref.null resolves source type index"
    (typedNull ≟ some (values [.ref (.null parent.heap)]))
  check "dropped nonnull element retains its type" (match store.resolveElem? owner 0 with
    | some elem => elem.refType == ValType.refNonNull child.heap && elem.refs.isEmpty
    | none => false)

#print axioms source_valid
#print axioms FuncInst.activation?_sound
#print axioms Typed.store_funcs

end Wasm.Tests.TypedReferences
