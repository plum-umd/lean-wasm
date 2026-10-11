import Wasm.Fast.Runtime
import Wasm.Fast.Tables

namespace Wasm.Fast
inductive ArrayAccess (store : Store) (state : Frame) (x : Nat) (address : ArrayAddr)
    (object : ArrayInst) (field : Types.FieldType) : Prop where
  | mk (type : Types.DefinedType) (lookupType : state.module.definedTypes[x]? = some type)
      (expand : type.expandComposite? = some (.array field))
      (lookup : store.array? address = some object)
      (matched : Typed store (.ref (.array address)) (.ref type.heap)) :
      ArrayAccess store state x address object field

private def checkArrayAccess (store : Store) (state : Frame) (x : Nat) (address : ArrayAddr) :
    Option {result : ArrayInst × Types.FieldType //
      ArrayAccess store state x address result.1 result.2} := by
  match ht : state.module.definedTypes[x]? with
  | none => exact none
  | some type =>
    match hf : type.expandComposite? with
    | some (.array field) =>
      match ho : store.array? address with
      | none => exact none
      | some object =>
        match checkValue store (.ref (.array address)) (.ref type.heap) with
        | none => exact none
        | some typed => exact some ⟨(object, field), ⟨type, ht, hf, ho, typed.down⟩⟩
    | _ => exact none

inductive ArrayNull : ArrayOp → List Value → Prop where
  | get : ArrayNull (.get x signed) [.ref (.null heap), .i32 index]
  | set : ArrayNull (.set x) [.ref (.null heap), .i32 index, value]
  | len : ArrayNull .len [.ref (.null heap)]
  | fill : ArrayNull (.fill x) [.ref (.null heap), .i32 index, value, .i32 count]
  | copyDestination : ArrayNull (.copy x y)
      [.ref (.null heap), .i32 dst, source, .i32 src, .i32 count]
  | copySource : ArrayNull (.copy x y)
      [destination, .i32 dst, .ref (.null heap), .i32 src, .i32 count]
  | initData : ArrayNull (.initData x y)
      [.ref (.null heap), .i32 dst, .i32 src, .i32 count]
  | initElem : ArrayNull (.initElem x y)
      [.ref (.null heap), .i32 dst, .i32 src, .i32 count]

inductive ArrayReduces : Store → Frame → ArrayOp → List Value →
    Store → List AdminInstr → Prop where
  | null (h : ArrayNull op args) : ArrayReduces store state op args store [.trap]
  | new (ht : state.module.definedTypes[x]? = some type)
      (hf : type.expandComposite? = some (.array field))
      (hv : Types.projectVal field.storage.unpack = some valueType)
      (ha : Typed store value valueType) (hp : field.storage.packValue value = some packed) :
      ArrayReduces store state (.new_ x false) [value, .i32 count]
        {store with arrays := store.arrays ++ [⟨type, Array.replicate count.toNat packed⟩]}
        (values [.ref (.array ⟨store.arrays.length⟩)])
  | newDefault (ht : state.module.definedTypes[x]? = some type)
      (hf : type.expandComposite? = some (.array field))
      (hv : Types.projectVal field.storage.unpack = some valueType)
      (hd : Value.default valueType = some value)
      (ha : Typed store value valueType) (hp : field.storage.packValue value = some packed) :
      ArrayReduces store state (.new_ x true) [.i32 count]
        {store with arrays := store.arrays ++ [⟨type, Array.replicate count.toNat packed⟩]}
        (values [.ref (.array ⟨store.arrays.length⟩)])
  | newFixed (ht : state.module.definedTypes[x]? = some type)
      (hf : type.expandComposite? = some (.array field))
      (hv : Types.projectVal field.storage.unpack = some valueType)
      (hn : args.length = count) (ha : ArgsTyped store args (List.replicate count valueType))
      (hp : args.mapM field.storage.packValue = some packed) :
      ArrayReduces store state (.newFixed x count) args
        {store with arrays := store.arrays ++ [⟨type, packed.toArray⟩]}
        (values [.ref (.array ⟨store.arrays.length⟩)])
  | len (ho : store.array? address = some object) :
      ArrayReduces store state .len [.ref (.array address)] store
        (values [.i32 (BitVec.ofNat 32 object.fields.size)])
  | get (access : ArrayAccess store state x address object field)
      (hb : index.toNat < object.fields.size)
      (hv : object.fields[index.toNat]? = some packed)
      (hu : field.storage.unpackValue signed packed = some value) :
      ArrayReduces store state (.get x signed) [.ref (.array address), .i32 index]
        store (values [value])
  | getBounds (access : ArrayAccess store state x address object field)
      (hb : ¬ index.toNat < object.fields.size) :
      ArrayReduces store state (.get x signed) [.ref (.array address), .i32 index] store [.trap]
  | set (access : ArrayAccess store state x address object field) (hm : field.mutable = true)
      (hb : index.toNat < object.fields.size)
      (hv : Types.projectVal field.storage.unpack = some valueType)
      (ha : Typed store value valueType) (hp : field.storage.packValue value = some packed) :
      ArrayReduces store state (.set x) [.ref (.array address), .i32 index, value]
        (store.writeArray address {object with fields :=
          (object.fields.modify index.toNat (fun _ => packed))}) []
  | setBounds (access : ArrayAccess store state x address object field)
      (hb : ¬ index.toNat < object.fields.size) :
      ArrayReduces store state (.set x) [.ref (.array address), .i32 index, value] store [.trap]
  | fill (access : ArrayAccess store state x address object field) (hm : field.mutable = true)
      (hb : start.toNat + count.toNat ≤ object.fields.size)
      (hv : Types.projectVal field.storage.unpack = some valueType)
      (ha : Typed store value valueType) (hp : field.storage.packValue value = some packed) :
      ArrayReduces store state (.fill x) [.ref (.array address), .i32 start, value, .i32 count]
        (store.writeArray address
          (object.replace start.toNat (Array.replicate count.toNat packed))) []
  | fillBounds (access : ArrayAccess store state x address object field)
      (hb : ¬ start.toNat + count.toNat ≤ object.fields.size) :
      ArrayReduces store state (.fill x) [.ref (.array address), .i32 start, value, .i32 count]
        store [.trap]
  | copy (hd : ArrayAccess store state x destination dstObject dstField)
      (hs : ArrayAccess store state y source srcObject srcField) (hm : dstField.mutable = true)
      (matched : Types.StorageMatches {} srcField.storage dstField.storage)
      (hb : dst.toNat + count.toNat ≤ dstObject.fields.size ∧
        src.toNat + count.toNat ≤ srcObject.fields.size) :
      ArrayReduces store state (.copy x y)
        [.ref (.array destination), .i32 dst, .ref (.array source), .i32 src, .i32 count]
        (store.writeArray destination (dstObject.replace dst.toNat
          (srcObject.fields.extract src.toNat (src.toNat + count.toNat)))) []
  | copyBounds (hd : ArrayAccess store state x destination dstObject dstField)
      (hs : ArrayAccess store state y source srcObject srcField)
      (hb : ¬ (dst.toNat + count.toNat ≤ dstObject.fields.size ∧
        src.toNat + count.toNat ≤ srcObject.fields.size)) :
      ArrayReduces store state (.copy x y)
        [.ref (.array destination), .i32 dst, .ref (.array source), .i32 src, .i32 count]
        store [.trap]
  | newData (ht : state.module.definedTypes[x]? = some type)
      (hf : type.expandComposite? = some (.array field))
      (hd : store.resolveData? state.module y = some data)
      (hv : arrayDataValues field.storage data.bytes start.toNat count.toNat = some fields) :
      ArrayReduces store state (.newData x y) [.i32 start, .i32 count]
        {store with arrays := store.arrays ++ [⟨type, fields⟩]}
        (values [.ref (.array ⟨store.arrays.length⟩)])
  | newDataBounds (ht : state.module.definedTypes[x]? = some type)
      (hf : type.expandComposite? = some (.array field))
      (hw : field.storage.byteWidth? = some width)
      (hd : store.resolveData? state.module y = some data)
      (hb : ¬ start.toNat + count.toNat * width ≤ data.bytes.size) :
      ArrayReduces store state (.newData x y) [.i32 start, .i32 count] store [.trap]
  | initData (access : ArrayAccess store state x address object field) (hm : field.mutable = true)
      (hd : store.resolveData? state.module y = some data)
      (hb : dst.toNat + count.toNat ≤ object.fields.size)
      (hv : arrayDataValues field.storage data.bytes src.toNat count.toNat = some fields) :
      ArrayReduces store state (.initData x y)
        [.ref (.array address), .i32 dst, .i32 src, .i32 count]
        (store.writeArray address (object.replace dst.toNat fields)) []
  | initDataBounds (access : ArrayAccess store state x address object field)
      (hw : field.storage.byteWidth? = some width)
      (hd : store.resolveData? state.module y = some data)
      (hb : ¬ (dst.toNat + count.toNat ≤ object.fields.size ∧
        src.toNat + count.toNat * width ≤ data.bytes.size)) :
      ArrayReduces store state (.initData x y)
        [.ref (.array address), .i32 dst, .i32 src, .i32 count] store [.trap]
  | newElem (ht : state.module.definedTypes[x]? = some type)
      (hf : type.expandComposite? = some (.array field))
      (hv : Types.projectVal field.storage.unpack = some valueType)
      (he : store.resolveElem? state.module y = some elem)
      (hb : start.toNat + count.toNat ≤ elem.refs.size)
      (ha : ArgsTyped store ((elem.refs.extract start.toNat (start.toNat + count.toNat)).toList.map
        Value.ref) (List.replicate count.toNat valueType)) :
      ArrayReduces store state (.newElem x y) [.i32 start, .i32 count]
        {store with arrays := store.arrays ++ [⟨type,
          (elem.refs.extract start.toNat (start.toNat + count.toNat)).map Value.ref⟩]}
        (values [.ref (.array ⟨store.arrays.length⟩)])
  | newElemBounds (ht : state.module.definedTypes[x]? = some type)
      (hf : type.expandComposite? = some (.array field))
      (he : store.resolveElem? state.module y = some elem)
      (hb : ¬ start.toNat + count.toNat ≤ elem.refs.size) :
      ArrayReduces store state (.newElem x y) [.i32 start, .i32 count] store [.trap]
  | initElem (access : ArrayAccess store state x address object field) (hm : field.mutable = true)
      (hv : Types.projectVal field.storage.unpack = some valueType)
      (he : store.resolveElem? state.module y = some elem)
      (hb : dst.toNat + count.toNat ≤ object.fields.size ∧
        src.toNat + count.toNat ≤ elem.refs.size)
      (ha : ArgsTyped store ((elem.refs.extract src.toNat (src.toNat + count.toNat)).toList.map
        Value.ref) (List.replicate count.toNat valueType)) :
      ArrayReduces store state (.initElem x y)
        [.ref (.array address), .i32 dst, .i32 src, .i32 count]
        (store.writeArray address (object.replace dst.toNat
          ((elem.refs.extract src.toNat (src.toNat + count.toNat)).map Value.ref))) []
  | initElemBounds (access : ArrayAccess store state x address object field)
      (he : store.resolveElem? state.module y = some elem)
      (hb : ¬ (dst.toNat + count.toNat ≤ object.fields.size ∧
        src.toNat + count.toNat ≤ elem.refs.size)) :
      ArrayReduces store state (.initElem x y)
        [.ref (.array address), .i32 dst, .i32 src, .i32 count] store [.trap]

inductive ArrayStep : Store → Frame → List AdminInstr → Store → List AdminInstr → Prop where
  | redex : ArrayReduces store state op args next code →
      ArrayStep store state (values args ++ [.instr (.arrayOp op)]) next code
  | context : ArrayStep store state code next code' →
      ArrayStep store state (values vs ++ code ++ tail) next (values vs ++ code' ++ tail)
  | label : ArrayStep store state body next body' →
      ArrayStep store state [.label n continuation body] next [.label n continuation body']
  | handler : ArrayStep store state body next body' →
      ArrayStep store state [.handler catches body] next [.handler catches body']
  | frame : ArrayStep store inner body next body' →
      ArrayStep store state [.frame n inner body] next [.frame n inner body']

abbrev CheckedArrayRedex (store : Store) (state : Frame) (op : ArrayOp) (args : List Value) :=
  Option {next : Store × List AdminInstr // ArrayReduces store state op args next.1 next.2}

private def checkArrayType (state : Frame) (x : Nat) :
    Option {result : Types.DefinedType × Types.FieldType //
      state.module.definedTypes[x]? = some result.1 ∧
        result.1.expandComposite? = some (.array result.2)} := by
  match ht : state.module.definedTypes[x]? with
  | none => exact none
  | some type =>
    match hf : type.expandComposite? with
    | some (.array field) => exact some ⟨(type, field), by simp, by simp [hf]⟩
    | _ => exact none

private def checkedArrayRedex (store : Store) (state : Frame) (op : ArrayOp)
    (args : List Value) : CheckedArrayRedex store state op args := by
  match op, args with
  | .new_ x false, [value, .i32 count] =>
    if count.toNat ≤ arrayAllocationBudget then
      match checkArrayType state x with
      | none => exact none
      | some info =>
        match hv : Types.projectVal info.val.2.storage.unpack with
        | none => exact none
        | some valueType =>
          match checkValue store value valueType, hp : info.val.2.storage.packValue value with
          | some typed, some packed => exact some ⟨(_, _),
              .new info.property.1 info.property.2 hv typed.down hp⟩
          | _, _ => exact none
    else exact none
  | .new_ x true, [.i32 count] =>
    if count.toNat ≤ arrayAllocationBudget then
      match checkArrayType state x with
      | none => exact none
      | some info =>
        match hv : Types.projectVal info.val.2.storage.unpack with
        | none => exact none
        | some valueType =>
          match hd : Value.default valueType with
          | none => exact none
          | some value =>
            match checkValue store value valueType, hp : info.val.2.storage.packValue value with
            | some typed, some packed => exact some ⟨(_, _),
                .newDefault info.property.1 info.property.2 hv hd typed.down hp⟩
            | _, _ => exact none
    else exact none
  | .newFixed x count, args =>
    if hn : args.length = count then
      if count ≤ arrayAllocationBudget then
        match checkArrayType state x with
        | none => exact none
        | some info =>
          match hv : Types.projectVal info.val.2.storage.unpack with
          | none => exact none
          | some valueType =>
            match checkArgs store args (List.replicate count valueType),
                hp : args.mapM info.val.2.storage.packValue with
            | some typed, some packed => exact some ⟨(_, _),
                .newFixed info.property.1 info.property.2 hv hn typed.down hp⟩
            | _, _ => exact none
      else exact none
    else exact none
  | .len, [.ref (.null _)] => exact some ⟨(store, [.trap]), .null .len⟩
  | .len, [.ref (.array address)] =>
    match ho : store.array? address with
    | none => exact none
    | some object => exact some ⟨(_, _), .len ho⟩
  | .get _ _, [.ref (.null _), .i32 _] => exact some ⟨(store, [.trap]), .null .get⟩
  | .get x signed, [.ref (.array address), .i32 index] =>
    match checkArrayAccess store state x address with
    | none => exact none
    | some access =>
      if hb : index.toNat < access.val.1.fields.size then
        match hv : access.val.1.fields[index.toNat]? with
        | none => exact none
        | some packed =>
          match hu : access.val.2.storage.unpackValue signed packed with
          | none => exact none
          | some value => exact some ⟨(_, _), .get access.property hb hv hu⟩
      else exact some ⟨(store, [.trap]), .getBounds access.property hb⟩
  | .set _, [.ref (.null _), .i32 _, _] => exact some ⟨(store, [.trap]), .null .set⟩
  | .set x, [.ref (.array address), .i32 index, value] =>
    match checkArrayAccess store state x address with
    | none => exact none
    | some access =>
      if hb : index.toNat < access.val.1.fields.size then
        if hm : access.val.2.mutable = true then
          match hv : Types.projectVal access.val.2.storage.unpack with
          | none => exact none
          | some valueType =>
            match checkValue store value valueType, hp : access.val.2.storage.packValue value with
            | some typed, some packed => exact some ⟨(_, _),
                .set access.property hm hb hv typed.down hp⟩
            | _, _ => exact none
        else exact none
      else exact some ⟨(store, [.trap]), .setBounds access.property hb⟩
  | .fill _, [.ref (.null _), .i32 _, _, .i32 _] =>
    exact some ⟨(store, [.trap]), .null .fill⟩
  | .fill x, [.ref (.array address), .i32 start, value, .i32 count] =>
    match checkArrayAccess store state x address with
    | none => exact none
    | some access =>
      if hb : start.toNat + count.toNat ≤ access.val.1.fields.size then
        if hm : access.val.2.mutable = true then
          match hv : Types.projectVal access.val.2.storage.unpack with
          | none => exact none
          | some valueType =>
            match checkValue store value valueType, hp : access.val.2.storage.packValue value with
            | some typed, some packed => exact some ⟨(_, _),
                .fill access.property hm hb hv typed.down hp⟩
            | _, _ => exact none
        else exact none
      else exact some ⟨(store, [.trap]), .fillBounds access.property hb⟩
  | .copy _ _, [.ref (.null _), .i32 _, _, .i32 _, .i32 _] =>
    exact some ⟨(store, [.trap]), .null .copyDestination⟩
  | .copy _ _, [_, .i32 _, .ref (.null _), .i32 _, .i32 _] =>
    exact some ⟨(store, [.trap]), .null .copySource⟩
  | .copy x y, [.ref (.array destination), .i32 dst, .ref (.array source), .i32 src, .i32 count] =>
    match checkArrayAccess store state x destination, checkArrayAccess store state y source with
    | some dstAccess, some srcAccess =>
      if hb : dst.toNat + count.toNat ≤ dstAccess.val.1.fields.size ∧
          src.toNat + count.toNat ≤ srcAccess.val.1.fields.size then
        if hm : dstAccess.val.2.mutable = true then
          if matched : Types.Algorithm.storageMatches {} srcAccess.val.2.storage
              dstAccess.val.2.storage = true then
            exact some ⟨(_, _), .copy dstAccess.property srcAccess.property hm
              (Types.Algorithm.storageMatches_sound matched) hb⟩
          else exact none
        else exact none
      else exact some ⟨(store, [.trap]), .copyBounds dstAccess.property srcAccess.property hb⟩
    | _, _ => exact none
  | .newData x y, [.i32 start, .i32 count] =>
    match checkArrayType state x, hd : store.resolveData? state.module y with
    | some info, some data =>
      match hw : info.val.2.storage.byteWidth? with
      | none => exact none
      | some width =>
        if hb : start.toNat + count.toNat * width ≤ data.bytes.size then
          if count.toNat ≤ arrayAllocationBudget then
            match hv : arrayDataValues info.val.2.storage data.bytes start.toNat count.toNat with
            | none => exact none
            | some fields => exact some ⟨(_, _), .newData info.property.1 info.property.2 hd hv⟩
          else exact none
        else exact some ⟨(store, [.trap]), .newDataBounds info.property.1 info.property.2 hw hd hb⟩
    | _, _ => exact none
  | .initData _ _, [.ref (.null _), .i32 _, .i32 _, .i32 _] =>
    exact some ⟨(store, [.trap]), .null .initData⟩
  | .initData x y, [.ref (.array address), .i32 dst, .i32 src, .i32 count] =>
    match checkArrayAccess store state x address, hd : store.resolveData? state.module y with
    | some access, some data =>
      match hw : access.val.2.storage.byteWidth? with
      | none => exact none
      | some width =>
        if hb : dst.toNat + count.toNat ≤ access.val.1.fields.size ∧
            src.toNat + count.toNat * width ≤ data.bytes.size then
          if hm : access.val.2.mutable = true then
            match hv : arrayDataValues access.val.2.storage data.bytes src.toNat count.toNat with
            | none => exact none
            | some fields => exact some ⟨(_, _), .initData access.property hm hd hb.1 hv⟩
          else exact none
        else exact some ⟨(store, [.trap]), .initDataBounds access.property hw hd hb⟩
    | _, _ => exact none
  | .newElem x y, [.i32 start, .i32 count] =>
    match checkArrayType state x, he : store.resolveElem? state.module y with
    | some info, some elem =>
      if hb : start.toNat + count.toNat ≤ elem.refs.size then
        if count.toNat ≤ arrayAllocationBudget then
          match hv : Types.projectVal info.val.2.storage.unpack with
          | none => exact none
          | some valueType =>
            let refs := (elem.refs.extract start.toNat (start.toNat + count.toNat)).toList
            match checkArgs store (refs.map Value.ref) (List.replicate count.toNat valueType) with
            | none => exact none
            | some typed => exact some ⟨(_, _),
                .newElem info.property.1 info.property.2 hv he hb typed.down⟩
        else exact none
      else exact some ⟨(store, [.trap]), .newElemBounds info.property.1 info.property.2 he hb⟩
    | _, _ => exact none
  | .initElem _ _, [.ref (.null _), .i32 _, .i32 _, .i32 _] =>
    exact some ⟨(store, [.trap]), .null .initElem⟩
  | .initElem x y, [.ref (.array address), .i32 dst, .i32 src, .i32 count] =>
    match checkArrayAccess store state x address, he : store.resolveElem? state.module y with
    | some access, some elem =>
      if hb : dst.toNat + count.toNat ≤ access.val.1.fields.size ∧
          src.toNat + count.toNat ≤ elem.refs.size then
        if hm : access.val.2.mutable = true then
          match hv : Types.projectVal access.val.2.storage.unpack with
          | none => exact none
          | some valueType =>
            let refs := (elem.refs.extract src.toNat (src.toNat + count.toNat)).toList
            match checkArgs store (refs.map Value.ref) (List.replicate count.toNat valueType) with
            | none => exact none
            | some typed => exact some ⟨(_, _), .initElem access.property hm hv he hb typed.down⟩
        else exact none
      else exact some ⟨(store, [.trap]), .initElemBounds access.property he hb⟩
    | _, _ => exact none
  | _, _ => exact none

abbrev CheckedArrayStep (store : Store) (state : Frame) (code : List AdminInstr) :=
  Option {next : Store × List AdminInstr // ArrayStep store state code next.1 next.2}

private def arrayContext (vs : List Value) (tail : List AdminInstr)
    (checked : CheckedArrayStep store state code) :
    CheckedArrayStep store state (values vs ++ code ++ tail) :=
  checked.map fun next => ⟨(next.val.1, values vs ++ next.val.2 ++ tail), .context next.property⟩

def ArrayOp.operandCount : ArrayOp → Nat
  | .new_ _ true | .len => 1
  | .new_ _ false | .newData _ _ | .newElem _ _ | .get _ _ => 2
  | .newFixed _ count => count
  | .set _ => 3
  | .fill _ | .initData _ _ | .initElem _ _ => 4
  | .copy _ _ => 5

private def scanArrays (store : Store) (state : Frame) (code : List AdminInstr)
    (stack : List Value) : CheckedArrayStep store state (values stack ++ code) := by
  match code with
  | .instr (.const value) :: tail =>
    simpa [values, List.map_append, List.append_assoc] using
      scanArrays store state tail (stack ++ [value])
  | .instr (.arrayOp op) :: tail =>
    if h : op.operandCount ≤ stack.length then
      let below := stack.take (stack.length - op.operandCount)
      let args := stack.drop (stack.length - op.operandCount)
      have split : stack = below ++ args := (List.take_append_drop _ _).symm
      let checked : CheckedArrayStep store state (values args ++ [.instr (.arrayOp op)]) :=
        (checkedArrayRedex store state op args).map fun next =>
        ⟨next.val, ArrayStep.redex next.property⟩
      simpa [split, values, List.map_append, List.append_assoc] using
        arrayContext below tail checked
    else exact none
  | .label n continuation body :: tail =>
    let inner : CheckedArrayStep store state [.label n continuation body] :=
      (scanArrays store state body []).map fun next =>
        ⟨(next.val.1, [.label n continuation next.val.2]), .label next.property⟩
    simpa [values] using arrayContext stack tail inner
  | .handler catches body :: tail =>
    let inner : CheckedArrayStep store state [.handler catches body] :=
      (scanArrays store state body []).map fun next =>
        ⟨(next.val.1, [.handler catches next.val.2]), .handler next.property⟩
    simpa [values] using arrayContext stack tail inner
  | .frame n inner body :: tail =>
    let checked : CheckedArrayStep store state [.frame n inner body] :=
      (scanArrays store inner body []).map fun next =>
        ⟨(next.val.1, [.frame n inner next.val.2]), .frame next.property⟩
    simpa [values] using arrayContext stack tail checked
  | _ => exact none
termination_by sizeOf code

def stepArrays (store : Store) (state : Frame) (code : List AdminInstr) :
    Option (Store × List AdminInstr) := (scanArrays store state code []).map Subtype.val

theorem stepArrays_sound (h : stepArrays store state code = some next) :
    ArrayStep store state code next.1 next.2 := by
  unfold stepArrays at h
  cases hs : scanArrays store state code [] with
  | none => simp [hs] at h
  | some result => simp [hs] at h; subst next; simpa [values] using result.property

theorem ArrayStep.resources_preserved (h : ArrayStep store state code next code') :
    next.funcs = store.funcs ∧ next.globals = store.globals ∧ next.mems = store.mems ∧
      next.datas = store.datas ∧ next.tables = store.tables ∧ next.elems = store.elems := by
  induction h with
  | redex reduced => cases reduced <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih

end Wasm.Fast
