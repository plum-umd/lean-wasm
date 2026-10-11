import Wasm.GCStorage
import Wasm.StructValidation

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

private def structContext (vs : List Value) (tail : List AdminInstr)
    (checked : CheckedStructStep store state code) :
    CheckedStructStep store state (values vs ++ code ++ tail) :=
  checked.map fun next => ⟨(next.val.1, values vs ++ next.val.2 ++ tail),
    .context next.property⟩

private def structOperands? (module : ModuleInst) : Instr → Option Nat
  | .structNew x default => if default then some 0 else do
    let .struct_ fields ← module.types[x]? | none
    some fields.length
  | .structGet _ _ _ => some 1
  | .structSet _ _ => some 2
  | _ => none

private def scanStructs (store : Store) (state : Frame) (code : List AdminInstr)
    (stack : List Value) : CheckedStructStep store state (values stack ++ code) := by
  match code with
  | .instr (.const value) :: tail =>
    simpa [values, List.map_append, List.append_assoc] using
      scanStructs store state tail (stack ++ [value])
  | .instr instr :: tail =>
    match structOperands? state.module instr with
    | none => exact none
    | some count =>
      if h : count ≤ stack.length then
        let below := stack.take (stack.length - count)
        let args := stack.drop (stack.length - count)
        have split : stack = below ++ args := (List.take_append_drop _ _).symm
        simpa [split, values, List.map_append, List.append_assoc] using
          structContext below tail (checkedStructRedex store state instr args)
      else exact none
  | .label n continuation body :: tail =>
    let inner : CheckedStructStep store state [.label n continuation body] :=
      (scanStructs store state body []).map fun next =>
        ⟨(next.val.1, [.label n continuation next.val.2]), .label next.property⟩
    simpa [values] using structContext stack tail inner
  | .handler catches body :: tail =>
    let inner : CheckedStructStep store state [.handler catches body] :=
      (scanStructs store state body []).map fun next =>
        ⟨(next.val.1, [.handler catches next.val.2]), .handler next.property⟩
    simpa [values] using structContext stack tail inner
  | .frame n inner body :: tail =>
    let checked : CheckedStructStep store state [.frame n inner body] :=
      (scanStructs store inner body []).map fun next =>
        ⟨(next.val.1, [.frame n inner next.val.2]), .frame next.property⟩
    simpa [values] using structContext stack tail checked
  | _ => exact none
termination_by sizeOf code

def stepStructs (store : Store) (state : Frame) (code : List AdminInstr) :
    Option (Store × List AdminInstr) := (scanStructs store state code []).map Subtype.val

theorem stepStructs_sound (h : stepStructs store state code = some next) :
    StructStep store state code next.1 next.2 := by
  unfold stepStructs at h
  cases hs : scanStructs store state code [] with
  | none => simp [hs] at h
  | some result => simp [hs] at h; subst next; simpa [values] using result.property

theorem StructStep.resources_preserved (h : StructStep store state code next code') :
    next.funcs = store.funcs ∧ next.globals = store.globals ∧ next.mems = store.mems ∧
      next.datas = store.datas ∧ next.tables = store.tables ∧ next.elems = store.elems := by
  induction h with
  | redex reduced => cases reduced <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

end Wasm
