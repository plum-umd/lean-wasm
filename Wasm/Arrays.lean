import Wasm.ArrayValidation
import Wasm.Tables
import Wasm.RuntimeMatchingCompleteness
import Wasm.RuntimeExpectedTypesInvariant
import Wasm.FamilyScanner
import Wasm.OperandScanner

namespace Wasm

def arrayAllocationBudget : Nat := gcAllocationBudget

def Store.writeArray (store : Store) (address : ArrayAddr) (object : ArrayInst) : Store :=
  {store with arrays := store.arrays.modify address.index (fun _ => object)}

def ArrayInst.replace (object : ArrayInst) (start : Nat) (fields : Array Value) : ArrayInst :=
  {object with fields := object.fields.extract 0 start ++ fields ++
    object.fields.extract (start + fields.size) object.fields.size}

def Types.StorageType.decodeArrayValue : Types.StorageType → Array Byte → Option Value
  | .i8, bytes | .i16, bytes | .val .i32, bytes =>
    some (.i32 (BitVec.ofNat 32 (decodeBytes bytes.toList)))
  | .val .i64, bytes => some (.i64 (BitVec.ofNat 64 (decodeBytes bytes.toList)))
  | .val .f32, bytes => some (.f32 (BitVec.ofNat 32 (decodeBytes bytes.toList)))
  | .val .f64, bytes => some (.f64 (BitVec.ofNat 64 (decodeBytes bytes.toList)))
  | .val .v128, bytes => some (.v128 (BitVec.ofNat 128 (decodeBytes bytes.toList)))
  | _, _ => none

def arrayDataValues (storage : Types.StorageType) (bytes : Array Byte)
    (start count : Nat) : Option (Array Value) := do
  let width ← storage.byteWidth?
  if start + count * width ≤ bytes.size then
    let values ← (List.range count).mapM fun index =>
      storage.decodeArrayValue (bytes.extract (start + index * width) (start + (index + 1) * width))
    some values.toArray
  else none

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

private def arrayTypeData? (state : Frame) (x : Nat) :
    Option (Types.DefinedType × Types.FieldType) := do
  let type ← state.module.definedTypes[x]?
  let .array field ← type.expandComposite? | none
  pure (type, field)

private theorem arrayTypeData?_sound
    (found : arrayTypeData? state index = some (type, field)) :
    state.module.definedTypes[index]? = some type ∧
      type.expandComposite? = some (.array field) := by
  unfold arrayTypeData? at found
  cases ht : state.module.definedTypes[index]? with
  | none => simp [ht] at found
  | some actual =>
    simp only [ht] at found
    dsimp only [Bind.bind, Option.bind] at found
    split at found <;> simp_all
    split at found <;> simp_all

private def checkArrayType (state : Frame) (x : Nat) :
    Option {result : Types.DefinedType × Types.FieldType //
      state.module.definedTypes[x]? = some result.1 ∧
        result.1.expandComposite? = some (.array result.2)} :=
  match found : arrayTypeData? state x with
  | none => none
  | some result => some ⟨result, arrayTypeData?_sound found⟩

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
          match checkRuntimeStorage srcAccess.val.2.storage dstAccess.val.2.storage with
          | some matched => exact some ⟨(_, _),
              .copy dstAccess.property srcAccess.property hm matched.down hb⟩
          | none => exact none
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

private def ArrayLocal : FamilyRedex := fun store state instruction args next code =>
  match instruction with
  | .instr (.arrayOp op) => ArrayReduces store state op args next code
  | _ => False

private def arrayScanner : FamilyScanner where
  operands _ instruction := match instruction with
    | .instr (.arrayOp op) => some op.operandCount
    | _ => none
  reduce store state instruction args := match instruction with
    | .instr (.arrayOp op) => (checkedArrayRedex store state op args).map Subtype.val
    | _ => none

private theorem FamilyStep.arrays (h : FamilyStep ArrayLocal store state code next code') :
    ArrayStep store state code next code' := by
  induction h with
  | @redex _ instruction args _ _ h =>
    cases instruction <;> simp only [ArrayLocal] at h
    all_goals try contradiction
    rename_i instr
    cases instr <;> simp only [ArrayLocal] at h
    all_goals try contradiction
    exact .redex h
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

private theorem arrayScanner_sound (h : arrayScanner.scan store state code stack = some next) :
    ArrayStep store state (values stack ++ code) next.1 next.2 := by
  apply FamilyStep.arrays
  apply arrayScanner.scan_sound (redex := ArrayLocal) ?_ h
  intro store state instruction args next found
  cases instruction <;> simp only [arrayScanner] at found
  all_goals try contradiction
  rename_i instr
  cases instr <;> simp only [arrayScanner] at found
  all_goals try contradiction
  obtain ⟨checked, _, same⟩ := Option.map_eq_some_iff.mp found
  cases same
  exact checked.property

private def checkedArrayStep (store : Store) (state : Frame) (code : List AdminInstr) :
    CheckedArrayStep store state code :=
  match found : arrayScanner.step store state code with
  | none => none
  | some next => some ⟨next, by simpa [FamilyScanner.step, values] using arrayScanner_sound found⟩

/-- Detect the allocation guard at the active redex without allocating the requested array.
Data/element bounds are checked first, matching the executor's trap priority. -/
private def arrayRedexResourceLimit? (store : Store) (state : Frame) (op : ArrayOp)
    (args : List Value) : Option ResourceLimit := do
  let count ← match op, args with
    | .new_ _ false, [_, .i32 count] => some count.toNat
    | .new_ _ true, [.i32 count] => some count.toNat
    | .newFixed _ count, args => if args.length = count then some count else none
    | .newData x y, [.i32 start, .i32 count] => do
      let info ← checkArrayType state x
      let data ← store.resolveData? state.module y
      let width ← info.val.2.storage.byteWidth?
      if start.toNat + count.toNat * width ≤ data.bytes.size then some count.toNat else none
    | .newElem x y, [.i32 start, .i32 count] => do
      let _ ← checkArrayType state x
      let elem ← store.resolveElem? state.module y
      if start.toNat + count.toNat ≤ elem.refs.size then some count.toNat else none
    | _, _ => none
  if count > arrayAllocationBudget then
    some (.arrayElements count arrayAllocationBudget)
  else none

private def arrayLimitProbe (store : Store) (state : Frame)
    (instruction : AdminInstr) (args : List Value) : Option ResourceLimit :=
  match instruction with
  | .instr (.arrayOp op) => arrayRedexResourceLimit? store state op args
  | _ => none

private def scanArrayResourceLimit? (store : Store) (state : Frame)
    (code : List AdminInstr) (stack : List Value) : Option ResourceLimit :=
  scanOperands arrayScanner.operands arrayLimitProbe store state code stack

/-- Resource classification uses the same operand and administrative boundaries as stepping. -/
def arrayResourceLimit? (store : Store) (state : Frame) (code : List AdminInstr) :
    Option ResourceLimit := scanArrayResourceLimit? store state code []

def stepArrays (store : Store) (state : Frame) (code : List AdminInstr) :
    Option (Store × List AdminInstr) := (checkedArrayStep store state code).map Subtype.val

theorem stepArrays_sound (h : stepArrays store state code = some next) :
    ArrayStep store state code next.1 next.2 := by
  unfold stepArrays at h
  cases hs : checkedArrayStep store state code with
  | none => simp [hs] at h
  | some result => simp [hs] at h; subst next; simpa [values] using result.property

theorem ArrayStep.resources_preserved (h : ArrayStep store state code next code') :
    next.funcs = store.funcs ∧ next.globals = store.globals ∧ next.mems = store.mems ∧
      next.datas = store.datas ∧ next.tables = store.tables ∧ next.elems = store.elems := by
  induction h with
  | redex reduced => cases reduced <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | context _ ih | label _ ih | handler _ ih | frame _ ih => exact ih


private theorem checkArrayType_complete
    (lookup : state.module.definedTypes[index]? = some type)
    (expanded : type.expandComposite? = some (.array field)) :
    ∃ proof, checkArrayType state index = some ⟨(type, field), proof⟩ := by
  have data : arrayTypeData? state index = some (type, field) := by
    simp [arrayTypeData?, lookup, expanded]
  simp only [checkArrayType]
  split <;> simp_all

private theorem ArrayAccess.checked_complete
    (access : ArrayAccess store state index address object field)
    (valid : store.RuntimeTypesValid) (ready : state.RuntimeTypesReady) :
    ∃ proof, checkArrayAccess store state index address = some ⟨(object, field), proof⟩ := by
  have semantic := access
  cases access with
  | mk type lookup expanded found matched =>
    have success := checkValue_complete (type := .ref _) valid (.ref (ready.heap lookup)) matched
    obtain ⟨_, valueFound⟩ := Option.isSome_iff_exists.mp success
    simp only [checkArrayAccess]
    repeat first | simp_all | split
    subst_vars
    repeat first | simp_all | split
    all_goals subst_vars
    all_goals repeat first | simp_all | split
    all_goals subst_vars
    all_goals first | rfl | exact ⟨_, rfl⟩ | exact semantic

private theorem ArrayAccess.storage_valid
    (access : ArrayAccess store state index address object field)
    (ready : state.RuntimeTypesReady) : Types.RuntimeValValid {} field.storage.unpack := by
  cases access with
  | mk type lookup expanded _ _ =>
    exact ready.2 type (List.mem_of_getElem? lookup) _ expanded _
      (by simp [Types.CompType.valTypes])

private theorem ArrayAccess.value_valid
    (access : ArrayAccess store state index address object field)
    (ready : state.RuntimeTypesReady)
    (projected : Types.projectVal field.storage.unpack = some valueType) :
    Types.RuntimeValValid {} (Types.embedVal valueType) := by
  cases access with
  | mk type lookup expanded _ _ => exact ready.array_value lookup expanded projected

private theorem arrayDataValues_bounds
    (found : arrayDataValues storage bytes start count = some fields) :
    ∃ width, storage.byteWidth? = some width ∧ start + count * width ≤ bytes.size := by
  unfold arrayDataValues at found
  cases hw : storage.byteWidth? with
  | none => simp [hw] at found
  | some width =>
    simp only [hw] at found
    dsimp only [Bind.bind, Option.bind] at found
    split at found
    · exact ⟨width, rfl, by assumption⟩
    · simp_all

/-- Allocation counts within the executor's declared array resource budget. -/
def ArrayAllocationAdmissible : ArrayOp → List Value → Prop
  | .new_ _ false, [_, .i32 count] | .new_ _ true, [.i32 count]
  | .newData _ _, [.i32 _, .i32 count] | .newElem _ _, [.i32 _, .i32 count] =>
    count.toNat ≤ arrayAllocationBudget
  | .newFixed _ count, _ => count ≤ arrayAllocationBudget
  | _, _ => True

private theorem Store.array_allocation_ne (store : Store) (object : ArrayInst) :
    {store with arrays := store.arrays ++ [object]} ≠ store := by
  intro same
  have lengths := congrArg (fun store => store.arrays.length) same
  simp at lengths

private theorem ArrayReduces.operand_arity (reduced : ArrayReduces store state op args next code) :
    op.operandCount = args.length := by
  cases reduced
  case null h => cases h <;> rfl
  all_goals simp_all [ArrayOp.operandCount]

set_option maxHeartbeats 2000000 in
private theorem array_raw_complete (reduced : ArrayReduces store state op args next code)
    (valid : store.RuntimeTypesValid) (ready : state.RuntimeTypesReady)
    (budget : ArrayAllocationAdmissible op args ∨ next = store) :
    (checkedArrayRedex store state op args).isSome = true := by
  cases reduced
  case' null h => cases h
  case' new hf hv hp ha ht =>
    obtain ⟨_, typeFound⟩ := checkArrayType_complete ht hf
    have success := checkValue_complete valid (ready.array_value ht hf hv) ha
    obtain ⟨_, valueFound⟩ := Option.isSome_iff_exists.mp success
  case' newDefault hf hv hd hp ha ht =>
    obtain ⟨_, typeFound⟩ := checkArrayType_complete ht hf
    have success := checkValue_complete valid (ready.array_value ht hf hv) ha
    obtain ⟨_, valueFound⟩ := Option.isSome_iff_exists.mp success
  case' newFixed hf hv ht hn hp ha =>
    obtain ⟨_, typeFound⟩ := checkArrayType_complete ht hf
    have success := checkArgs_complete valid
      (by intro type member; simp only [List.mem_replicate] at member
          simpa only [member.2] using ready.array_value ht hf hv) ha
    obtain ⟨_, argsFound⟩ := Option.isSome_iff_exists.mp success
  case' get hb hv hu access => obtain ⟨_, accessFound⟩ := access.checked_complete valid ready
  case' getBounds hb access => obtain ⟨_, accessFound⟩ := access.checked_complete valid ready
  case' set hm hb hv hp ha access =>
    obtain ⟨_, accessFound⟩ := access.checked_complete valid ready
    have success := checkValue_complete valid (access.value_valid ready hv) ha
    obtain ⟨_, valueFound⟩ := Option.isSome_iff_exists.mp success
  case' setBounds hb access => obtain ⟨_, accessFound⟩ := access.checked_complete valid ready
  case' fill hm hb hv hp ha access =>
    obtain ⟨_, accessFound⟩ := access.checked_complete valid ready
    have success := checkValue_complete valid (access.value_valid ready hv) ha
    obtain ⟨_, valueFound⟩ := Option.isSome_iff_exists.mp success
  case' fillBounds hb access => obtain ⟨_, accessFound⟩ := access.checked_complete valid ready
  case' copy hm matched hb hd hs =>
    obtain ⟨_, dstFound⟩ := hd.checked_complete valid ready
    obtain ⟨_, srcFound⟩ := hs.checked_complete valid ready
    have success := checkRuntimeStorage_complete (hs.storage_valid ready) (hd.storage_valid ready) matched
    obtain ⟨_, storageFound⟩ := Option.isSome_iff_exists.mp success
  case' copyBounds hb hd hs =>
    obtain ⟨_, dstFound⟩ := hd.checked_complete valid ready
    obtain ⟨_, srcFound⟩ := hs.checked_complete valid ready
  case' newData hf hv ht hd =>
    obtain ⟨_, typeFound⟩ := checkArrayType_complete ht hf
    obtain ⟨width, widthFound, bounds⟩ := arrayDataValues_bounds hv
  case' newDataBounds hf hw hb ht hd => obtain ⟨_, typeFound⟩ := checkArrayType_complete ht hf
  case' initData hm hb hv access hd =>
    obtain ⟨_, accessFound⟩ := access.checked_complete valid ready
    obtain ⟨width, widthFound, bounds⟩ := arrayDataValues_bounds hv
  case' initDataBounds hw hb access hd => obtain ⟨_, accessFound⟩ := access.checked_complete valid ready
  case' newElem hf hv hb ha ht he =>
    obtain ⟨_, typeFound⟩ := checkArrayType_complete ht hf
    have success := checkArgs_complete valid
      (by intro type member; simp only [List.mem_replicate] at member
          simpa only [member.2] using ready.array_value ht hf hv) ha
    obtain ⟨_, argsFound⟩ := Option.isSome_iff_exists.mp success
  case' newElemBounds hf hb ht he => obtain ⟨_, typeFound⟩ := checkArrayType_complete ht hf
  case' initElem hm hv hb ha access he =>
    obtain ⟨_, accessFound⟩ := access.checked_complete valid ready
    have success := checkArgs_complete valid
      (by intro type member; simp only [List.mem_replicate] at member
          simpa only [member.2] using access.value_valid ready hv) ha
    obtain ⟨_, argsFound⟩ := Option.isSome_iff_exists.mp success
  case' initElemBounds hb access he => obtain ⟨_, accessFound⟩ := access.checked_complete valid ready
  all_goals simp only [ArrayAllocationAdmissible, Store.array_allocation_ne, or_false] at budget
  all_goals simp only [checkedArrayRedex]
  all_goals repeat first | simp_all | split
  all_goals subst_vars
  all_goals repeat first | simp_all | split
  all_goals subst_vars
  all_goals repeat first | simp_all | split
  all_goals first | simp_all | grind

private theorem array_limit_complete (reduced : ArrayReduces store state op args next code)
    (budget : ¬ ArrayAllocationAdmissible op args) (unchanged : next ≠ store) :
    (arrayRedexResourceLimit? store state op args).isSome = true := by
  cases reduced
  case' newData hf hv ht hd =>
    obtain ⟨_, typeFound⟩ := checkArrayType_complete ht hf
    obtain ⟨_, widthFound, bounds⟩ := arrayDataValues_bounds hv
  case' newElem hf hv hb ha ht he => obtain ⟨_, typeFound⟩ := checkArrayType_complete ht hf
  all_goals simp only [ArrayAllocationAdmissible, Store.array_allocation_ne, or_false] at budget
  all_goals try contradiction
  all_goals simp only [arrayRedexResourceLimit?]
  all_goals repeat first | simp_all | split
  all_goals subst_vars
  all_goals repeat first | simp_all | split
  all_goals subst_vars
  all_goals first | simp_all | omega
private theorem array_raw_complete_or_limit (reduced : ArrayReduces store state op args next code)
    (valid : store.RuntimeTypesValid) (ready : state.RuntimeTypesReady) :
    (checkedArrayRedex store state op args).isSome = true ∨
      (arrayRedexResourceLimit? store state op args).isSome = true := by
  by_cases budget : ArrayAllocationAdmissible op args
  · exact .inl (array_raw_complete reduced valid ready (.inl budget))
  · by_cases unchanged : next = store
    · exact .inl (array_raw_complete reduced valid ready (.inr unchanged))
    · exact .inr (array_limit_complete reduced budget unchanged)

private def arrayProgressScanner : FamilyScanner where
  operands := arrayScanner.operands
  reduce store state instruction args :=
    (arrayScanner.reduce store state instruction args).orElse fun _ =>
      (arrayLimitProbe store state instruction args).map fun _ => (store, [])

private theorem array_progress_probe :
    (arrayProgressScanner.reduce store state instruction args).isSome =
      ((arrayScanner.reduce store state instruction args).isSome ||
        (arrayLimitProbe store state instruction args).isSome) := by
  simp only [arrayProgressScanner]
  cases arrayScanner.reduce store state instruction args <;>
    cases arrayLimitProbe store state instruction args <;> rfl

private theorem ArrayStep.family (reduced : ArrayStep store state code next code') :
    FamilyStep ArrayLocal store state code next code' := by
  induction reduced with
  | redex h => exact .redex h
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih

/-- Array execution either steps or reports its explicit allocation limit. -/
theorem stepArrays_complete_or_limit (reduced : ArrayStep store state code next code')
    (valid : store.RuntimeTypesValid) (ready : state.RuntimeTypesReady)
    (frames : CodeFramesValid Frame.RuntimeTypesReady code) :
    (stepArrays store state code).isSome = true ∨
      (arrayResourceLimit? store state code).isSome = true := by
  have progress : (arrayProgressScanner.step store state code).isSome = true := by
    apply arrayProgressScanner.step_complete_on (redex := ArrayLocal) ?_ reduced.family ready frames
    intro state instruction args next code ready reduced
    cases instruction <;> simp only [ArrayLocal] at reduced
    all_goals try contradiction
    rename_i instr
    cases instr <;> simp only [ArrayLocal] at reduced
    all_goals try contradiction
    refine ⟨by simp [AdminInstr.ScannerAtom], ?_, ?_⟩
    · simp only [arrayProgressScanner, arrayScanner]
      rw [reduced.operand_arity]
    · rw [array_progress_probe]
      simpa [arrayScanner, arrayLimitProbe, Option.isSome_map, Bool.or_eq_true] using
        array_raw_complete_or_limit reduced valid ready
  simp only [FamilyScanner.step, FamilyScanner.scan_isSome_eq_hasOperands,
    array_progress_probe] at progress
  change hasOperands arrayScanner.operands (fun store state op args =>
    (arrayScanner.reduce store state op args).isSome ||
      (arrayLimitProbe store state op args).isSome) store state code [] = true at progress
  rw [hasOperands_or] at progress
  rw [← arrayScanner.scan_isSome_eq_hasOperands,
    ← scanOperands_isSome] at progress
  have stepSome : (stepArrays store state code).isSome =
      (arrayScanner.scan store state code []).isSome := by
    simp only [stepArrays, checkedArrayStep, FamilyScanner.step]
    split <;> simp_all
  simpa [stepSome, arrayResourceLimit?, scanArrayResourceLimit?, Bool.or_eq_true] using progress

#print axioms stepArrays_complete_or_limit

#print axioms array_raw_complete_or_limit

#print axioms array_raw_complete

end Wasm
