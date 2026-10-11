import Wasm.ConstantExpression
import Wasm.TypeClosure

namespace Wasm

def MemoryType.Matches (actual expected : MemoryType) : Prop :=
  actual.addrType = expected.addrType ∧ expected.min ≤ actual.min ∧
    match expected.max with
    | none => True
    | some bound => match actual.max with
      | none => False
      | some maximum => maximum ≤ bound

instance (actual expected : MemoryType) : Decidable (actual.Matches expected) := by
  unfold MemoryType.Matches
  cases expected.max <;> cases actual.max <;> infer_instance

def TableType.Matches (actual expected : TableType) : Prop :=
  actual.kind = expected.kind ∧ actual.nullable = expected.nullable ∧
    actual.addrType = expected.addrType ∧
    expected.min ≤ actual.min ∧
    match expected.max with
    | none => True
    | some bound => match actual.max with
      | none => False
      | some maximum => maximum ≤ bound
instance instDecidableTableMatches (actual expected : TableType) :
    Decidable (actual.Matches expected) := by
  unfold TableType.Matches
  cases expected.max <;> cases actual.max <;> infer_instance

def GlobalType.Matches (actual expected : GlobalType) : Prop :=
  actual.mutability = expected.mutability ∧
    if expected.mutability = .var then actual.valType = expected.valType
    else (checkRuntimeVal actual.valType expected.valType).isSome = true

instance (actual expected : GlobalType) : Decidable (actual.Matches expected) := by
  unfold GlobalType.Matches
  infer_instance

def ImportMatches (store : Store) (types : TypeContext) (desc : ImportDesc) (address : ExternAddr)
    (definedTypes : List Types.DefinedType := []) : Prop :=
  match desc, address with
  | .func x, .func address =>
    match store.func? address, types.func? (x) with
    | some function, some type =>
      (checkRuntimeHeap function.runtimeType.heap
        ((definedTypes[x]?).getD type.definedType).heap).isSome = true
    | _, _ => False
  | .tag x, .tag address => match store.tags[address.index]?, types.func? (x) with
    | some tag, some type =>
      let expected := ((definedTypes[x]?).getD type.definedType).heap
      (checkRuntimeHeap tag.definedType.heap expected).isSome = true ∧
        (checkRuntimeHeap expected tag.definedType.heap).isSome = true
    | _, _ => False
  | .global type, .global address => match store.global? address with
    | none => False
    | some global => global.type.Matches type ∧
        (checkValue store global.value global.type.valType).isSome = true
  | .memory type, .memory address => match store.mem? address with
    | none => False
    | some memory => memory.type.Matches type
  | .table type, .table address => match store.table? address with
    | none => False
    | some table => table.type.Matches type
  | _, _ => False

instance (store : Store) (types : TypeContext) (desc : ImportDesc) (address : ExternAddr)
    (definedTypes : List Types.DefinedType) :
    Decidable (ImportMatches store types desc address definedTypes) := by
  cases desc <;> cases address <;> simp only [ImportMatches]
  all_goals first | infer_instance | split <;> (try simp only [GlobalInst.Valid]) <;> infer_instance

def ImportsMatch (store : Store) (types : TypeContext) (entries : List Import)
    (addresses : List ExternAddr) (definedTypes : List Types.DefinedType := []) : Prop :=
  match entries, addresses with
  | [], [] => True
  | entry :: rest, address :: addresses =>
      ImportMatches store types entry.desc address definedTypes ∧
        ImportsMatch store types rest addresses definedTypes
  | _, _ => False

instance (store : Store) (types : TypeContext) (entries : List Import)
    (addresses : List ExternAddr) (definedTypes : List Types.DefinedType) :
    Decidable (ImportsMatch store types entries addresses definedTypes) := by
  cases entries with
  | nil => cases addresses <;> simp only [ImportsMatch] <;> infer_instance
  | cons entry rest =>
    cases addresses with
    | nil => simp only [ImportsMatch]; infer_instance
    | cons address tail =>
      haveI := instDecidableImportsMatch store types rest tail definedTypes
      simp only [ImportsMatch]
      infer_instance

def importedModule (types : TypeContext) (addresses : List ExternAddr)
    (definedTypes : List Types.DefinedType := []) : ModuleInst :=
  { types, definedTypes,
    funcs := addresses.filterMap fun address => match address with
      | .func a => some a
      | _ => none,
    globals := addresses.filterMap fun address => match address with
      | .global a => some a
      | _ => none,
    mems := addresses.filterMap fun address => match address with
      | .memory a => some a
      | _ => none,
    tags := addresses.filterMap fun address => match address with
      | .tag a => some a
      | _ => none,
    tables := addresses.filterMap fun address => match address with
      | .table a => some a
      | _ => none }

def linkedImports (module : Module) (addresses : List ExternAddr) : ModuleInst :=
  importedModule module.types addresses (module.resolvedTypes?.getD [])

/-- During constant evaluation, new addresses already have declared types, although
their final closures are allocated after the initializers. This typing view does not
mutate the execution store or make provisional closures callable. -/
def initializerTypingStore (store : Store) (module : ModuleInst) : Store :=
  { store with funcs := store.funcs ++
      (module.funcs.zip module.funcTypeIndices).filterMap fun (address, typeIdx) =>
        if address.index < store.funcs.length then none
        else (module.types.func? (typeIdx)).map fun type =>
          ⟨type, module, .wasm ⟨typeIdx, [], []⟩⟩ }

inductive GlobalsEvaluated : Store → ModuleInst → List Global →
    Store → ModuleInst → List Value → Prop where
  | allocating (he : ConstAllocated store module global.init allocated value)
      (ht : Typed (initializerTypingStore allocated module) value global.type.valType)
      (hr : GlobalsEvaluated
        (allocated.allocateGlobal ⟨global.type, value⟩).2
        {module with globals := module.globals ++
          [(allocated.allocateGlobal ⟨global.type, value⟩).1]}
        rest final finalModule vs) :
      GlobalsEvaluated store module (global :: rest) final finalModule (value :: vs)
  | empty : GlobalsEvaluated store module [] store module []
  | cons (he : ConstEval store module global.init [] [value])
      (ht : Typed (initializerTypingStore store module) value global.type.valType)
      (hr : GlobalsEvaluated
        (store.allocateGlobal ⟨global.type, value⟩).2
        { module with globals := module.globals ++
          [(store.allocateGlobal ⟨global.type, value⟩).1] }
        rest final finalModule vs) :
      GlobalsEvaluated store module (global :: rest) final finalModule (value :: vs)

private def evaluateGlobals (store : Store) (module : ModuleInst) : (globals : List Global) →
    Option { next : Store × ModuleInst × List Value //
      GlobalsEvaluated store module globals next.1 next.2.1 next.2.2 }
  | [] => some ⟨(store, module, []), .empty⟩
  | global :: rest => by
    match evalConst store module global.init with
    | none => exact none
    | some value =>
      match checkValue (initializerTypingStore store module) value.val global.type.valType with
      | some ht =>
        let allocated := store.allocateGlobal ⟨global.type, value.val⟩
        let nextModule := { module with globals := module.globals ++ [allocated.1] }
        exact (evaluateGlobals allocated.2 nextModule rest).map fun next =>
          ⟨(next.val.1, next.val.2.1, value.val :: next.val.2.2),
            .cons value.property ht.down next.property⟩
      | none => exact none

private def evaluateAllocatedGlobals (store : Store) (module : ModuleInst) :
    (globals : List Global) → Option {next : Store × ModuleInst × List Value //
      GlobalsEvaluated store module globals next.1 next.2.1 next.2.2}
  | [] => some ⟨(store, module, []), .empty⟩
  | global :: rest => by
    match evalAllocatedConst store module global.init with
    | none => exact none
    | some evaluated =>
      let allocatedStore := evaluated.val.1
      let value := evaluated.val.2
      match checkValue (initializerTypingStore allocatedStore module) value global.type.valType with
      | none => exact none
      | some typed =>
        let allocated := allocatedStore.allocateGlobal ⟨global.type, value⟩
        let nextModule := {module with globals := module.globals ++ [allocated.1]}
        exact (evaluateAllocatedGlobals allocated.2 nextModule rest).map fun next =>
          ⟨(next.val.1, next.val.2.1, value :: next.val.2.2),
            .allocating evaluated.property typed.down next.property⟩

def ExternIdx.resolve? (module : ModuleInst) : ExternIdx → Option ExternAddr
  | .func x => (module.funcAddr? x).map .func
  | .tag x => module.tags[x]?.map .tag
  | .global x => (module.globalAddr? x).map .global
  | .memory x => (module.memAddr? x).map .memory
  | .table x => (module.tableAddr? x).map .table

inductive ExportsAllocated (module : ModuleInst) : List Export → List ExportInst → Prop where
  | empty : ExportsAllocated module [] []
  | cons (ha : entry.desc.resolve? module = some address)
      (hr : ExportsAllocated module rest entries) :
      ExportsAllocated module (entry :: rest) (⟨entry.name, address⟩ :: entries)

private def allocateExports (module : ModuleInst) : (entries : List Export) →
    Option { result : List ExportInst // ExportsAllocated module entries result }
  | [] => some ⟨[], .empty⟩
  | entry :: rest => by
    match ha : entry.desc.resolve? module with
    | none => exact none
    | some address => exact (allocateExports module rest).map fun result =>
        ⟨⟨entry.name, address⟩ :: result.val, .cons ha result.property⟩

inductive FunctionSignatures (types : TypeContext) : List Func → List FuncType → Prop where
  | empty : FunctionSignatures types [] []
  | cons (ht : types.func? (function.typeIdx) = some ft)
      (hr : FunctionSignatures types rest signatures) :
      FunctionSignatures types (function :: rest) (ft :: signatures)

private def functionSignatures (types : TypeContext) : (functions : List Func) →
    Option { signatures : List FuncType // FunctionSignatures types functions signatures }
  | [] => some ⟨[], .empty⟩
  | function :: rest => by
    match ht : types.func? (function.typeIdx) with
    | none => exact none
    | some ft => exact (functionSignatures types rest).map fun result =>
        ⟨ft :: result.val, .cons ht result.property⟩

def freshAddresses (base count : Nat) : List Nat := (List.range count).map (base + ·)

/- Address maps are computed before allocating closures, unraveling allocmodule's
mutual dependency without replacing existing store entries.
-/
/-- Function addresses are available to ref.func before their closures are allocated. -/
def initializerModule (store : Store) (module : Module)
    (addresses : List ExternAddr) : ModuleInst :=
  let imports := linkedImports module addresses
  { imports with
    funcTypeIndices := module.importedFuncIndices ++ module.funcs.map Func.typeIdx,
    funcs := imports.funcs ++
    (freshAddresses store.funcs.length module.funcs.length).map FuncAddr.mk }

inductive RefsEvaluated (store : Store) (module : ModuleInst) :
    List (ValType × List Instr) → List RefValue → Prop where
  | empty : RefsEvaluated store module [] []
  | cons (he : ConstEval store module expression [] [.ref reference])
      (hk : Typed (initializerTypingStore store module) (.ref reference) type)
      (hr : RefsEvaluated store module rest references) :
      RefsEvaluated store module ((type, expression) :: rest) (reference :: references)

theorem RefsEvaluated.length_eq (h : RefsEvaluated store module expressions references) :
    references.length = expressions.length := by
  induction h with
  | empty => rfl
  | cons _ _ _ ih => simp [ih]

private def evaluateRefs (store : Store) (module : ModuleInst) :
    (expressions : List (ValType × List Instr)) →
    Option { references : List RefValue // RefsEvaluated store module expressions references }
  | [] => some ⟨[], .empty⟩
  | (type, expression) :: rest => by
    match evalConst store module expression with
    | none => exact none
    | some value =>
      match hv : value.val with
      | .ref reference =>
        match checkValue (initializerTypingStore store module) (.ref reference) type with
        | some hk =>
          exact (evaluateRefs store module rest).map fun result =>
            ⟨reference :: result.val, .cons (hv ▸ value.property) hk.down result.property⟩
        | none => exact none
      | _ => exact none

inductive AllocatedRefs (module : ModuleInst) : Store → List (ValType × List Instr) →
    Store → List RefValue → Prop where
  | empty : AllocatedRefs module store [] store []
  | cons (he : ConstAllocated store module expression allocated (.ref reference))
      (ht : Typed (initializerTypingStore allocated module) (.ref reference) type)
      (hr : AllocatedRefs module allocated rest next references) :
      AllocatedRefs module store ((type, expression) :: rest) next (reference :: references)

private def evaluateAllocatedRefs (store : Store) (module : ModuleInst) :
    (expressions : List (ValType × List Instr)) →
    Option {result : Store × List RefValue //
      AllocatedRefs module store expressions result.1 result.2}
  | [] => some ⟨(store, []), .empty⟩
  | (type, expression) :: rest => by
    match evalAllocatedConst store module expression with
    | none => exact none
    | some evaluated =>
      match hv : evaluated.val.2 with
      | .ref reference =>
        match checkValue (initializerTypingStore evaluated.val.1 module) (.ref reference) type with
        | none => exact none
        | some typed =>
          exact (evaluateAllocatedRefs evaluated.val.1 module rest).map fun next =>
            ⟨(next.val.1, reference :: next.val.2),
              .cons (hv ▸ evaluated.property) typed.down next.property⟩
      | _ => exact none

def Module.tableExpressions (module : Module) : List (ValType × List Instr) :=
  module.tables.map fun table => (table.type.refType, table.init)
def Module.elemExpressions (module : Module) : List (ValType × List Instr) :=
  module.elems.flatMap fun elem => elem.init.map fun expression => (elem.refType, expression)

def allocateElems : List Elem → List RefValue → List ElemInst
  | [], _ => []
  | elem :: rest, references =>
    ⟨elem.kind, (references.take elem.init.length).toArray, elem.nullable⟩ ::
      allocateElems rest (references.drop elem.init.length)

def allocatedModule (store : Store) (module : Module) (imports : ModuleInst) : ModuleInst :=
  { types := module.types, definedTypes := module.resolvedTypes?.getD [],
    funcTypeIndices := module.importedFuncIndices ++ module.funcs.map Func.typeIdx,
    funcs := imports.funcs ++
      (freshAddresses store.funcs.length module.funcs.length).map FuncAddr.mk,
    globals := imports.globals ++
      (freshAddresses store.globals.length module.globals.length).map GlobalAddr.mk,
    mems := imports.mems ++ (freshAddresses store.mems.length module.mems.length).map MemAddr.mk,
    datas := (freshAddresses store.datas.length module.datas.length).map DataAddr.mk,
    tables := imports.tables ++
      (freshAddresses store.tables.length module.tables.length).map TableAddr.mk,
    elems := (freshAddresses store.elems.length module.elems.length).map ElemAddr.mk,
    tags := imports.tags ++ (freshAddresses store.tags.length module.tags.length).map TagAddr.mk }

def allocatedStore (store : Store) (module : Module) (owner : ModuleInst)
    (globals : List Value) (signatures : List FuncType)
    (tableValues : List RefValue := []) (elemValues : List RefValue := []) : Store :=
  { funcs := store.funcs ++ (module.funcs.zip signatures).map fun (function, ft) =>
      ⟨ft, owner, .wasm function⟩,
    globals := store.globals ++ (module.globals.zip globals).map fun (global, value) =>
      ⟨global.type, value⟩,
    mems := store.mems ++ module.mems.map fun type =>
      ⟨type, Array.replicate (type.min * pageSize) 0⟩,
    datas := store.datas ++ module.datas.map fun segment => ⟨segment.bytes⟩,
    tables := store.tables ++ (module.tables.zip tableValues).map fun (table, reference) =>
      ⟨table.type, Array.replicate table.type.min reference⟩,
    elems := store.elems ++ allocateElems module.elems elemValues,
    tags := store.tags ++ module.tags.filterMap (fun x => do
      let ft ← module.types.func? (x)
      return ⟨ft, (owner.definedTypes[x]?).getD ft.definedType⟩),
    exns := store.exns, structs := store.structs, arrays := store.arrays }

def Module.initializationCode (module : Module) : List Instr :=
  ((module.elems.zipIdx).flatMap fun (segment, index) => segment.initializer index) ++
  ((module.datas.zipIdx).flatMap fun (segment, index) => segment.initializer index) ++
    (module.start.toList.map Instr.call)

/-- Preparation follows evalglobal then allocmodule, including the specification's
temporary global instances. Only the final instances occur in the resulting address map.
-/
def allocatedFunctions (store : Store) (module : Module) (owner : ModuleInst)
    (signatures : List FuncType) : Store :=
  {store with funcs := store.funcs ++ (module.funcs.zip signatures).map fun (function, type) =>
    ⟨type, owner, .wasm function⟩}

def Module.allocatingInitializers (module : Module) : Bool :=
  let allocating : List Instr → Bool := fun code => code.any fun
    | .structNew _ _ | .arrayOp (.new_ _ _) | .arrayOp (.newFixed _ _) => true
    | _ => false
  module.globals.any (fun global => allocating global.init) ||
    module.tables.any (fun table => allocating table.init) ||
    module.elems.any (fun elem => elem.init.any allocating)

inductive ClosedModulePrepared (store : Store) (module : Module) (addresses : List ExternAddr) :
    Configuration → Prop where
  | allocating (hi : ImportsMatch store module.types module.imports addresses
        (module.resolvedTypes?.getD []))
      (hf : FunctionSignatures module.types module.funcs signatures)
      (he : ExportsAllocated (allocatedModule store module (linkedImports module addresses))
        module.exports entries)
      (hg : GlobalsEvaluated
        (allocatedFunctions store module
          {allocatedModule store module (linkedImports module addresses) with exports := entries}
          signatures)
        (initializerModule store module addresses) module.globals temporary temporaryModule vs)
      (ht : AllocatedRefs temporaryModule temporary module.tableExpressions tablesStore tableValues)
      (hel : AllocatedRefs temporaryModule tablesStore module.elemExpressions final elemValues) :
      ClosedModulePrepared store module addresses
        ⟨allocatedStore final module
            {allocatedModule store module (linkedImports module addresses) with exports := entries}
            [] [] tableValues elemValues,
          {module :=
            {allocatedModule store module (linkedImports module addresses) with exports := entries}},
          instructions module.initializationCode⟩
  | prepare (hi : ImportsMatch store module.types module.imports addresses
        (module.resolvedTypes?.getD []))
      (hg : GlobalsEvaluated store (initializerModule store module addresses)
        module.globals temporary temporaryModule globalValues)
      (ht : RefsEvaluated temporary temporaryModule module.tableExpressions tableValues)
      (hel : RefsEvaluated temporary temporaryModule module.elemExpressions elemValues)
      (hf : FunctionSignatures module.types module.funcs signatures)
      (he : ExportsAllocated
        (allocatedModule temporary module (linkedImports module addresses))
        module.exports entries) :
      ClosedModulePrepared store module addresses
        ⟨allocatedStore temporary module
            { allocatedModule temporary module (linkedImports module addresses)
              with exports := entries } globalValues signatures tableValues elemValues,
          { module := { allocatedModule temporary module (linkedImports module addresses)
              with exports := entries } }, instructions module.initializationCode⟩

inductive InstantiationError where
  | imports
  | resourceLimit
  | initializer
  | allocation
  deriving DecidableEq, Repr

/-- Low-level preparation for a validated source module and a well-formed incoming store.
The result certifies the allocation rules; source validity is required by `instantiate`.
Allocation budget is embedder policy, separate from semantic memory limits.
-/
private def checkedPrepareClosedInstantiation (store : Store) (module : Module)
    (addresses : List ExternAddr)
    (budgetPages : Nat := growthBudgetPages) :
    Except InstantiationError
      { config : Configuration // ClosedModulePrepared store module addresses config }
    := by
  if hi : ImportsMatch store module.types module.imports addresses
      (module.resolvedTypes?.getD []) then
    if module.mems.all (fun memory => memory.min ≤ budgetPages) &&
        module.tables.all (fun table => table.type.min ≤ tableGrowthBudget) then
      if module.allocatingInitializers then
        match functionSignatures module.types module.funcs with
        | none => exact .error .allocation
        | some signatures =>
          let base := allocatedModule store module (linkedImports module addresses)
          match allocateExports base module.exports with
          | none => exact .error .allocation
          | some entries =>
            let owner := {base with exports := entries.val}
            let initialStore := allocatedFunctions store module owner signatures.val
            match evaluateAllocatedGlobals initialStore
                (initializerModule store module addresses) module.globals with
            | none => exact .error .initializer
            | some globals =>
              match evaluateAllocatedRefs globals.val.1 globals.val.2.1 module.tableExpressions with
              | none => exact .error .initializer
              | some tables =>
                match evaluateAllocatedRefs tables.val.1 globals.val.2.1 module.elemExpressions with
                | none => exact .error .initializer
                | some elems =>
                  exact .ok ⟨⟨allocatedStore elems.val.1 module owner [] [] tables.val.2 elems.val.2,
                    {module := owner}, instructions module.initializationCode⟩,
                    .allocating hi signatures.property entries.property globals.property
                      tables.property elems.property⟩
      else
        match evaluateGlobals store (initializerModule store module addresses) module.globals with
        | none => exact .error .initializer
        | some globals =>
          match evaluateRefs globals.val.1 globals.val.2.1 module.tableExpressions with
          | none => exact .error .initializer
          | some tableValues =>
            match evaluateRefs globals.val.1 globals.val.2.1 module.elemExpressions with
            | none => exact .error .initializer
            | some elemValues =>
              match functionSignatures module.types module.funcs with
              | none => exact .error .allocation
              | some signatures =>
                let base := allocatedModule globals.val.1 module
                  (linkedImports module addresses)
                match allocateExports base module.exports with
                | none => exact .error .allocation
                | some entries =>
                  let owner := { base with exports := entries.val }
                  exact .ok ⟨⟨allocatedStore globals.val.1 module owner globals.val.2.2
                    signatures.val tableValues.val elemValues.val,
                    { module := owner }, instructions module.initializationCode⟩,
                    .prepare hi globals.property tableValues.property elemValues.property
                      signatures.property entries.property⟩
    else exact .error .resourceLimit
  else exact .error .imports

inductive ModulePrepared (store : Store) (module : Module) (addresses : List ExternAddr) :
    Configuration → Prop where
  | closed (hc : module.close? = some closed)
      (hp : ClosedModulePrepared store closed addresses config) :
      ModulePrepared store module addresses config

def checkedPrepareInstantiation (store : Store) (module : Module) (addresses : List ExternAddr)
    (budgetPages : Nat := growthBudgetPages) : Except InstantiationError
      { config : Configuration // ModulePrepared store module addresses config } := by
  match hc : module.close? with
  | none => exact .error .allocation
  | some closed =>
    exact (checkedPrepareClosedInstantiation store closed addresses budgetPages).map fun result =>
      ⟨result.val, .closed hc result.property⟩

structure InstantiationResult where
  execution : ConfigurationRunResult
  deriving BEq, Repr

def InstantiationResult.module? (result : InstantiationResult) : Option ModuleInst :=
  match result.execution.status with
  | .finished [] => some result.execution.state.frame.module
  | _ => none

def resumeInstantiation (fuel : Nat) (result : InstantiationResult) : InstantiationResult :=
  ⟨runConfiguration fuel result.execution.state⟩

theorem resumeInstantiation_sound :
    ConfigSteps result.execution.state (resumeInstantiation fuel result).execution.state :=
  runConfiguration_sound

inductive InstantiationExecution (store : Store) (module : Module) (addresses : List ExternAddr) :
    Configuration → Prop where
  | run (hv : module.Valid) (hp : ModulePrepared store module addresses initial)
      (hr : ConfigSteps initial final) : InstantiationExecution store module addresses final

/-- Instantiate a proved-valid module. Exhaustion returns a resumable configuration;
traps retain allocation and all preceding writes, including writes to imported memory.
-/
def instantiate (fuel : Nat) (store : Store) (module : ValidatedModule)
    (addresses : List ExternAddr) (budgetPages : Nat := growthBudgetPages) :
    Except InstantiationError InstantiationResult :=
  match checkedPrepareInstantiation store module.val addresses budgetPages with
  | .error error => .error error
  | .ok prepared => .ok ⟨runConfiguration fuel prepared.val⟩

theorem instantiate_sound (h : instantiate fuel store module addresses budget = .ok result) :
    InstantiationExecution store module.val addresses result.execution.state := by
  unfold instantiate at h
  cases hp : checkedPrepareInstantiation store module.val addresses budget with
  | error error => simp [hp] at h
  | ok prepared =>
    simp [hp] at h
    subst result
    exact .run module.property prepared.property runConfiguration_sound

theorem instantiate_finished
    (h : instantiate fuel store module addresses budget = .ok result)
    (hf : result.execution.status = .finished []) :
    InstantiationExecution store module.val addresses result.execution.state ∧
      result.execution.state.code = [] := by
  refine ⟨instantiate_sound h, ?_⟩
  unfold instantiate at h
  cases hp : checkedPrepareInstantiation store module.val addresses budget with
  | error error => simp [hp] at h
  | ok prepared =>
    simp [hp] at h
    subst result
    exact runConfiguration_finished hf

theorem allocatedStore_preserves_functions (store : Store) (module : Module)
    (owner : ModuleInst) (vs : List Value) (signatures : List FuncType) (address : FuncAddr)
    (h : address.index < store.funcs.length) :
    (allocatedStore store module owner vs signatures).func? address = store.func? address := by
  simp [allocatedStore, Store.func?, List.getElem?_append, h]

theorem allocatedStore_preserves_memories (store : Store) (module : Module)
    (owner : ModuleInst) (vs : List Value) (signatures : List FuncType) (address : MemAddr)
    (h : address.index < store.mems.length) :
    (allocatedStore store module owner vs signatures).mem? address = store.mem? address := by
  simp [allocatedStore, Store.mem?, List.getElem?_append, h]

theorem allocatedStore_preserves_globals (store : Store) (module : Module)
    (owner : ModuleInst) (vs : List Value) (signatures : List FuncType) (address : GlobalAddr)
    (h : address.index < store.globals.length) :
    (allocatedStore store module owner vs signatures).global? address = store.global? address := by
  simp [allocatedStore, Store.global?, List.getElem?_append, h]

theorem allocatedStore_preserves_data (store : Store) (module : Module)
    (owner : ModuleInst) (vs : List Value) (signatures : List FuncType) (address : DataAddr)
    (h : address.index < store.datas.length) :
    (allocatedStore store module owner vs signatures).data? address = store.data? address := by
  simp [allocatedStore, Store.data?, List.getElem?_append, h]

theorem allocatedStore_preserves_tables (store : Store) (module : Module)
    (owner : ModuleInst) (vs : List Value) (signatures : List FuncType)
    (tableValues elemValues : List RefValue) (address : TableAddr)
    (h : address.index < store.tables.length) :
    (allocatedStore store module owner vs signatures tableValues elemValues).table? address =
      store.table? address := by
  simp [allocatedStore, Store.table?, List.getElem?_append, h]

theorem allocatedStore_preserves_elements (store : Store) (module : Module)
    (owner : ModuleInst) (vs : List Value) (signatures : List FuncType)
    (tableValues elemValues : List RefValue) (address : ElemAddr)
    (h : address.index < store.elems.length) :
    (allocatedStore store module owner vs signatures tableValues elemValues).elem? address =
      store.elem? address := by
  simp [allocatedStore, Store.elem?, List.getElem?_append, h]

end Wasm
