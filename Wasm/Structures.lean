import Wasm.GCStorage
import Wasm.StructValidation
import Wasm.FamilyScanner
import Wasm.RuntimeMatchingCompleteness
import Wasm.RuntimeExpectedTypesInvariant

namespace Wasm

def packStructFields : List Types.FieldType → List Value → Option (List Value)
  | [], [] => some []
  | field :: fields, value :: values => do
    let packed ← field.storage.packValue value
    return packed :: (← packStructFields fields values)
  | _, _ => none

def Store.writeStruct (store : Store) (address : StructAddr) (object : StructInst) : Store :=
  {store with structs := store.structs.modify address.index (fun _ => object)}

inductive StructReduces : Store → Frame → List AdminInstr → Store → List AdminInstr → Prop where
  | new (ht : state.module.definedTypes[x]? = some type)
      (hf : type.expandComposite? = some (.struct_ fields))
      (hs : structFieldTypes fields = some ts) (ha : ArgsTyped store args ts)
      (hp : packStructFields fields args = some packed) :
      StructReduces store state (values args ++ [.instr (.structNew x false)])
        {store with structs := store.structs ++ [⟨type, packed⟩]}
        (values [.ref (.struct_ ⟨store.structs.length⟩)])
  | newDefault (ht : state.module.definedTypes[x]? = some type)
      (hf : type.expandComposite? = some (.struct_ fields))
      (hs : structFieldTypes fields = some ts) (hd : ts.mapM Value.default = some args)
      (ha : ArgsTyped store args ts) (hp : packStructFields fields args = some packed) :
      StructReduces store state [.instr (.structNew x true)]
        {store with structs := store.structs ++ [⟨type, packed⟩]}
        (values [.ref (.struct_ ⟨store.structs.length⟩)])
  | getNull : StructReduces store state
      [ .instr (.const (.ref (.null heap))), .instr (.structGet x y signed) ] store [.trap]
  | get (ht : state.module.definedTypes[x]? = some type)
      (hf : type.expandComposite? = some (.struct_ fields))
      (hs : fields[y]? = some field) (ho : store.struct? address = some object)
      (hr : Typed store (.ref (.struct_ address)) (.ref type.heap))
      (hv : object.fields[y]? = some packed)
      (hu : field.storage.unpackValue signed packed = some value) :
      StructReduces store state
        [ .instr (.const (.ref (.struct_ address))), .instr (.structGet x y signed) ] store
        (values [value])
  | setNull : StructReduces store state
      [ .instr (.const (.ref (.null heap))), .instr (.const value), .instr (.structSet x y) ]
      store [.trap]
  | set (ht : state.module.definedTypes[x]? = some type)
      (hf : type.expandComposite? = some (.struct_ fields))
      (hs : fields[y]? = some field) (hm : field.mutable = true)
      (ho : store.struct? address = some object)
      (hr : Typed store (.ref (.struct_ address)) (.ref type.heap))
      (hb : y < object.fields.length)
      (hv : Types.projectVal field.storage.unpack = some valueType)
      (ha : Typed store value valueType) (hp : field.storage.packValue value = some packed) :
      StructReduces store state
        [ .instr (.const (.ref (.struct_ address))), .instr (.const value),
          .instr (.structSet x y) ]
        (store.writeStruct address
          {object with fields := object.fields.modify y (fun _ => packed)})
        []

inductive StructStep : Store → Frame → List AdminInstr → Store → List AdminInstr → Prop where
  | redex : StructReduces store state code next code' → StructStep store state code next code'
  | context : StructStep store state code next code' →
      StructStep store state (values vs ++ code ++ tail) next (values vs ++ code' ++ tail)
  | label : StructStep store state body next body' →
      StructStep store state [.label n continuation body] next [.label n continuation body']
  | handler : StructStep store state body next body' →
      StructStep store state [.handler catches body] next [.handler catches body']
  | frame : StructStep store inner body next body' →
      StructStep store state [.frame n inner body] next [.frame n inner body']

abbrev CheckedStructStep (store : Store) (state : Frame) (code : List AdminInstr) :=
  Option {next : Store × List AdminInstr // StructStep store state code next.1 next.2}

private def checkedStructRedex (store : Store) (state : Frame) (instr : Instr)
    (args : List Value) : CheckedStructStep store state (values args ++ [.instr instr]) := by
  match instr with
  | .structNew x default =>
    match ht : state.module.definedTypes[x]? with
    | none => exact none
    | some type =>
      match hf : type.expandComposite? with
      | some (.struct_ fields) =>
        match hs : structFieldTypes fields with
        | none => exact none
        | some ts =>
          if hdflag : default = true then
            subst default
            match args with
            | [] =>
              match hd : ts.mapM Value.default with
              | none => exact none
              | some defaults =>
                match checkArgs store defaults ts, hp : packStructFields fields defaults with
                | some typed, some packed =>
                  exact some ⟨(_, values [.ref (.struct_ ⟨store.structs.length⟩)]),
                    .redex (.newDefault ht hf hs hd typed.down hp)⟩
                | _, _ => exact none
            | _ => exact none
          else
            have hdflagFalse : default = false := by simpa using hdflag
            subst default
            match checkArgs store args ts, hp : packStructFields fields args with
            | some typed, some packed =>
              exact some ⟨(_, values [.ref (.struct_ ⟨store.structs.length⟩)]),
                .redex (.new ht hf hs typed.down hp)⟩
            | _, _ => exact none
      | _ => exact none
  | .structGet x y signed =>
    match args with
    | [.ref (.null _)] => exact some ⟨(store, [.trap]), .redex .getNull⟩
    | [.ref (.struct_ address)] =>
      match ht : state.module.definedTypes[x]? with
      | none => exact none
      | some type =>
        match hf : type.expandComposite? with
        | some (.struct_ fields) =>
          match hs : fields[y]?, ho : store.struct? address with
          | some field, some object =>
            match checkValue store (.ref (.struct_ address)) (.ref type.heap) with
            | none => exact none
            | some typed =>
              match hv : object.fields[y]? with
              | none => exact none
              | some packed =>
                match hu : field.storage.unpackValue signed packed with
                | none => exact none
                | some value => exact some ⟨(store, values [value]),
                    .redex (.get ht hf hs ho typed.down hv hu)⟩
          | _, _ => exact none
        | _ => exact none
    | _ => exact none
  | .structSet x y =>
    match args with
    | [.ref (.null _), value] => exact some ⟨(store, [.trap]), .redex .setNull⟩
    | [.ref (.struct_ address), value] =>
      match ht : state.module.definedTypes[x]? with
      | none => exact none
      | some type =>
        match hf : type.expandComposite? with
        | some (.struct_ fields) =>
          match hs : fields[y]?, ho : store.struct? address with
          | some field, some object =>
            if hm : field.mutable = true then
              if hb : y < object.fields.length then
                match checkValue store (.ref (.struct_ address)) (.ref type.heap),
                    hv : Types.projectVal field.storage.unpack with
                | some referenceTyped, some valueType =>
                  match checkValue store value valueType, hp : field.storage.packValue value with
                  | some valueTyped, some packed => exact some ⟨(_, []),
                      .redex (.set ht hf hs hm ho referenceTyped.down hb hv valueTyped.down hp)⟩
                  | _, _ => exact none
                | _, _ => exact none
              else exact none
            else exact none
          | _, _ => exact none
        | _ => exact none
    | _ => exact none
  | _ => exact none

private def structOperands? (module : ModuleInst) : Instr → Option Nat
  | .structNew x default => if default then some 0 else do
    let .struct_ fields ← module.types[x]? | none
    some fields.length
  | .structGet _ _ _ => some 1
  | .structSet _ _ => some 2
  | _ => none

private def structScanner : FamilyScanner :=
  ⟨(fun state op => match op with
      | .instr instr => structOperands? state.module instr
      | _ => none),
    fun store state op args => match op with
      | .instr instr => (checkedStructRedex store state instr args).map Subtype.val
      | _ => none⟩

private theorem struct_family (step : FamilyStep
    (fun store state op args next code => StructStep store state (values args ++ [op]) next code)
    store state code next code') : StructStep store state code next code' := by
  induction step with
  | redex reduced => exact reduced
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

private theorem structScanner_sound (success : structScanner.scan store state code [] = some next) :
    StructStep store state code next.1 next.2 := by
  apply struct_family
  have localSound : ∀ store state op args next,
      structScanner.reduce store state op args = some next →
      StructStep store state (values args ++ [op]) next.1 next.2 := by
    intro store state op args next found
    cases op <;> simp only [structScanner] at found
    all_goals try contradiction
    obtain ⟨checked, lookup, same⟩ := Option.map_eq_some_iff.mp found
    cases same
    exact checked.property
  simpa [values] using structScanner.scan_sound localSound success

private def checkedStructStep (store : Store) (state : Frame) (code : List AdminInstr) :
    CheckedStructStep store state code :=
  match found : structScanner.scan store state code [] with
  | none => none
  | some next => some ⟨next, structScanner_sound found⟩

def stepStructs (store : Store) (state : Frame) (code : List AdminInstr) :
    Option (Store × List AdminInstr) := (checkedStructStep store state code).map Subtype.val

theorem stepStructs_sound (h : stepStructs store state code = some next) :
    StructStep store state code next.1 next.2 := by
  unfold stepStructs at h
  cases hs : checkedStructStep store state code with
  | none => simp [hs] at h
  | some result => simp [hs] at h; subst next; exact result.property

theorem StructStep.resources_preserved (h : StructStep store state code next code') :
    next.funcs = store.funcs ∧ next.globals = store.globals ∧ next.mems = store.mems ∧
      next.datas = store.datas ∧ next.tables = store.tables ∧ next.elems = store.elems := by
  induction h with
  | redex reduced => cases reduced <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

private theorem struct_new_arity {store : Store} {state : Frame} {index : Nat}
    {type : Types.DefinedType} {fields : List Types.FieldType} {types : List ValType}
    {args : List Value} (ready : state.RuntimeTypesReady)
    (lookup : state.module.definedTypes[index]? = some type)
    (expanded : type.expandComposite? = some (.struct_ fields))
    (projected : structFieldTypes fields = some types) (typed : ArgsTyped store args types) :
    structScanner.operands state (.instr (.structNew index false)) = some args.length := by
  have static := ready.1.struct_lookup lookup expanded
  have count := typed.length.trans (structFieldTypes_length projected).symm
  simp [structScanner, structOperands?, static, count]

private theorem struct_raw_complete (reduced : StructReduces store state code next code')
    (valid : store.RuntimeTypesValid) (ready : state.RuntimeTypesReady) :
    (structScanner.step store state code).isSome = true := by
  cases reduced
  case' new hf hs hp ha ht =>
    have arity := struct_new_arity ready ht hf hs ha
    have argsSuccess := checkArgs_complete valid (ready.struct_values ht hf hs) ha
    obtain ⟨_, argsFound⟩ := Option.isSome_iff_exists.mp argsSuccess
    rw [structScanner.step_atom_isSome (by trivial) arity]
  case' newDefault hf hs hd hp ha ht =>
    have argsSuccess := checkArgs_complete valid (ready.struct_values ht hf hs) ha
    obtain ⟨_, argsFound⟩ := Option.isSome_iff_exists.mp argsSuccess
    change (structScanner.step store state (values [] ++ [.instr (.structNew _ true)])).isSome = true
    rw [structScanner.step_atom_isSome (by trivial) rfl]
  case' get hf hs hv hu ho hr ht =>
    have referenceSuccess := checkValue_complete (type := .ref _) valid (.ref (ready.heap ht)) hr
    obtain ⟨_, referenceFound⟩ := Option.isSome_iff_exists.mp referenceSuccess
    change (structScanner.step store state (values [_] ++ [.instr (.structGet _ _ _)])).isSome = true
    rw [structScanner.step_atom_isSome (by trivial) rfl]
  case' set hf hs hm hb hv hp ho hr ha ht =>
    have referenceSuccess := checkValue_complete (type := .ref _) valid (.ref (ready.heap ht)) hr
    have valueSuccess := checkValue_complete valid (ready.struct_field ht hf hs hv) ha
    obtain ⟨_, referenceFound⟩ := Option.isSome_iff_exists.mp referenceSuccess
    obtain ⟨_, valueFound⟩ := Option.isSome_iff_exists.mp valueSuccess
    change (structScanner.step store state (values [_, _] ++ [.instr (.structSet _ _)])).isSome = true
    rw [structScanner.step_atom_isSome (by trivial) rfl]
  case' getNull =>
    change (structScanner.step store state (values [_] ++ [.instr (.structGet _ _ _)])).isSome = true
    rw [structScanner.step_atom_isSome (by trivial) rfl]
  case' setNull =>
    change (structScanner.step store state (values [_, _] ++ [.instr (.structSet _ _)])).isSome = true
    rw [structScanner.step_atom_isSome (by trivial) rfl]
  all_goals simp only [structScanner, Option.isSome_map, checkedStructRedex]
  all_goals repeat first
    | simp_all
    | split
  all_goals subst_vars
  all_goals try simp_all
  all_goals subst_vars
  all_goals repeat first | simp_all | split
  all_goals subst_vars
  all_goals first | simp_all | grind

private def StructLocal (store : Store) (state : Frame) (op : AdminInstr) (args : List Value)
    (next : Store) (code : List AdminInstr) : Prop :=
  op.ScannerAtom ∧ structScanner.operands state op = some args.length ∧
    StructReduces store state (values args ++ [op]) next code

private theorem StructStep.toFamily (step : StructStep store state code next code')
    (ready : state.RuntimeTypesReady) (frames : CodeFramesValid Frame.RuntimeTypesReady code) :
    FamilyStep StructLocal store state code next code' := by
  induction step with
  | redex reduced =>
    cases reduced
    all_goals first
      | refine FamilyStep.redex (op := .instr _) ?_
      | refine FamilyStep.redex (args := []) (op := .instr _) ?_
      | refine FamilyStep.redex (args := [_, _]) (op := .instr _) ?_
      | refine FamilyStep.redex (args := [_]) (op := .instr _) ?_
    all_goals refine ⟨by trivial, ?_, ?_⟩
    all_goals first
      | rfl
      | exact struct_new_arity ready (by assumption) (by assumption) (by assumption) (by assumption)
      | constructor <;> assumption
  | context _ ih =>
    simp only [codeFramesValid_append, codeFramesValid_values, true_and] at frames
    exact .context (ih ready frames.1)
  | label _ ih | handler _ ih =>
    simp only [codeFramesValid_singleton, AdminInstr.FramesValid] at frames
    first | exact .label (ih ready frames) | exact .handler (ih ready frames)
  | frame _ ih =>
    simp only [codeFramesValid_singleton, AdminInstr.FramesValid] at frames
    exact .frame (ih frames.1 frames.2)

/-- Structure execution is complete with valid fields and coherent module projections. -/
theorem stepStructs_complete (reduced : StructStep store state code next code')
    (valid : store.RuntimeTypesValid) (ready : state.RuntimeTypesReady)
    (frames : CodeFramesValid Frame.RuntimeTypesReady code) :
    (stepStructs store state code).isSome = true := by
  have localComplete : ∀ state op args next code, state.RuntimeTypesReady →
      StructLocal store state op args next code → op.ScannerAtom ∧
        structScanner.operands state op = some args.length ∧
        (structScanner.reduce store state op args).isSome = true := by
    intro state op args next code ready reduced
    obtain ⟨atom, arity, hr⟩ := reduced
    exact ⟨atom, arity, by
      rw [← structScanner.step_atom_isSome atom arity]
      exact struct_raw_complete hr valid ready⟩
  have success := structScanner.step_complete_on localComplete
    (reduced.toFamily ready frames) ready frames
  unfold FamilyScanner.step at success
  unfold stepStructs checkedStructStep
  split <;> rename_i found
  · simp [found] at success
  · simp

#print axioms stepStructs_complete

end Wasm
