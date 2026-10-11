import Wasm.StructValidation
import Wasm.GCStorage
import Wasm.TypeValidationAlgorithm

namespace Wasm

inductive ArrayInstrTyping (types : TypeContext) (defined : List Types.DefinedType)
    (elems : List ValType) (dataCount : Nat) : ArrayOp → List ValType → List ValType → Prop where
  | new (ht : types[x]? = some (.array field))
      (hv : Types.projectVal field.storage.unpack = some type) :
      ArrayInstrTyping types defined elems dataCount (.new_ x false) [type, .i32]
        [.refNonNull (.typeIdx x)]
  | newDefault (ht : types[x]? = some (.array field))
      (hv : Types.projectVal field.storage.unpack = some type) (hd : type.defaultable = true) :
      ArrayInstrTyping types defined elems dataCount (.new_ x true) [.i32]
        [.refNonNull (.typeIdx x)]
  | newFixed (ht : types[x]? = some (.array field))
      (hv : Types.projectVal field.storage.unpack = some type) :
      ArrayInstrTyping types defined elems dataCount (.newFixed x n) (List.replicate n type)
        [.refNonNull (.typeIdx x)]
  | get (ht : types[x]? = some (.array field))
      (hv : field.storage.readType? signed = some type) :
      ArrayInstrTyping types defined elems dataCount (.get x signed) [.ref (.typeIdx x), .i32]
        [type]
  | set (ht : types[x]? = some (.array field)) (hm : field.mutable = true)
      (hv : Types.projectVal field.storage.unpack = some type) :
      ArrayInstrTyping types defined elems dataCount (.set x) [.ref (.typeIdx x), .i32, type] []
  | len : ArrayInstrTyping types defined elems dataCount .len [.ref .array] [.i32]
  | fill (ht : types[x]? = some (.array field)) (hm : field.mutable = true)
      (hv : Types.projectVal field.storage.unpack = some type) :
      ArrayInstrTyping types defined elems dataCount (.fill x)
        [.ref (.typeIdx x), .i32, type, .i32] []
  | copy (hd : types[x]? = some (.array destination))
      (hs : types[y]? = some (.array source)) (hm : destination.mutable = true)
      (ht : Types.StorageMatches ⟨defined, []⟩ source.storage destination.storage) :
      ArrayInstrTyping types defined elems dataCount (.copy x y)
        [.ref (.typeIdx x), .i32, .ref (.typeIdx y), .i32, .i32] []
  | newData (ht : types[x]? = some (.array field))
      (hn : field.storage.byteWidth?.isSome = true) (hd : y < dataCount) :
      ArrayInstrTyping types defined elems dataCount (.newData x y) [.i32, .i32]
        [.refNonNull (.typeIdx x)]
  | initData (ht : types[x]? = some (.array field)) (hm : field.mutable = true)
      (hn : field.storage.byteWidth?.isSome = true) (hd : y < dataCount) :
      ArrayInstrTyping types defined elems dataCount (.initData x y)
        [.ref (.typeIdx x), .i32, .i32, .i32] []
  | newElem (ht : types[x]? = some (.array field)) (he : elems[y]? = some type)
      (hm : Types.ValMatches ⟨defined, []⟩ (Types.embedVal type) field.storage.unpack) :
      ArrayInstrTyping types defined elems dataCount (.newElem x y) [.i32, .i32]
        [.refNonNull (.typeIdx x)]
  | initElem (ht : types[x]? = some (.array field)) (hf : field.mutable = true)
      (he : elems[y]? = some type)
      (hm : Types.ValMatches ⟨defined, []⟩ (Types.embedVal type) field.storage.unpack) :
      ArrayInstrTyping types defined elems dataCount (.initElem x y)
        [.ref (.typeIdx x), .i32, .i32, .i32] []

def arrayField? (types : TypeContext) (x : Nat) : Option Types.FieldType := do
  let .array field ← types[x]? | none
  some field

def arraySignature? (types : TypeContext) (defined : List Types.DefinedType)
    (elems : List ValType) (dataCount : Nat) : ArrayOp → Option FuncType
  | .len => some ⟨[.ref .array], [.i32]⟩
  | .new_ x default => do
    let field ← arrayField? types x
    let type ← Types.projectVal field.storage.unpack
    if default && !type.defaultable then none
    else some ⟨if default then [.i32] else [type, .i32], [.refNonNull (.typeIdx x)]⟩
  | .newFixed x n => do
    let field ← arrayField? types x
    let type ← Types.projectVal field.storage.unpack
    some ⟨List.replicate n type, [.refNonNull (.typeIdx x)]⟩
  | .get x signed => do
    let field ← arrayField? types x
    let type ← field.storage.readType? signed
    some ⟨[.ref (.typeIdx x), .i32], [type]⟩
  | .set x => do
    let field ← arrayField? types x
    let type ← Types.projectVal field.storage.unpack
    if !field.mutable then none
    else some ⟨[.ref (.typeIdx x), .i32, type], []⟩
  | .fill x => do
    let field ← arrayField? types x
    let type ← Types.projectVal field.storage.unpack
    if !field.mutable then none
    else some ⟨[.ref (.typeIdx x), .i32, type, .i32], []⟩
  | .copy x y => do
    let destination ← arrayField? types x
    let source ← arrayField? types y
    if destination.mutable && Types.Algorithm.storageMatches ⟨defined, []⟩
        source.storage destination.storage then
      some ⟨[.ref (.typeIdx x), .i32, .ref (.typeIdx y), .i32, .i32], []⟩
    else none
  | .newData x y => do
    let field ← arrayField? types x
    if field.storage.byteWidth?.isSome && decide (y < dataCount) then
      some ⟨[.i32, .i32], [.refNonNull (.typeIdx x)]⟩
    else none
  | .initData x y => do
    let field ← arrayField? types x
    if field.mutable && field.storage.byteWidth?.isSome && decide (y < dataCount) then
      some ⟨[.ref (.typeIdx x), .i32, .i32, .i32], []⟩
    else none
  | .newElem x y => do
    let field ← arrayField? types x
    let type ← elems[y]?
    if Types.Algorithm.valMatches (Types.Algorithm.budget ⟨defined, []⟩
        (Types.embedVal type) field.storage.unpack) ⟨defined, []⟩
        (Types.embedVal type) field.storage.unpack then
      some ⟨[.i32, .i32], [.refNonNull (.typeIdx x)]⟩
    else none
  | .initElem x y => do
    let field ← arrayField? types x
    let type ← elems[y]?
    if field.mutable && Types.Algorithm.valMatches (Types.Algorithm.budget ⟨defined, []⟩
        (Types.embedVal type) field.storage.unpack) ⟨defined, []⟩
        (Types.embedVal type) field.storage.unpack then
      some ⟨[.ref (.typeIdx x), .i32, .i32, .i32], []⟩
    else none

theorem arrayField?_sound (h : arrayField? types x = some field) :
    types[x]? = some (.array field) := by
  cases ht : types[x]? <;> simp [arrayField?, ht, bind, Option.bind] at h
  rename_i comp
  cases comp <;> simp_all

theorem arraySignature?_sound (h : arraySignature? types defined elems dataCount op = some ft) :
    ArrayInstrTyping types defined elems dataCount op ft.params ft.results := by
  cases op <;> simp only [arraySignature?, bind, Option.bind] at h
  case len => cases h; exact .len
  case new_ x default =>
    cases hf : arrayField? types x <;> simp [hf] at h
    rename_i field
    have ht := arrayField?_sound hf
    cases hv : Types.projectVal field.storage.unpack <;> simp [hv] at h
    cases default <;> simp at h
    · cases h; exact .new ht hv
    · rcases h with ⟨hd, rfl⟩; exact .newDefault ht hv hd
  case newFixed x n =>
    cases hf : arrayField? types x <;> simp [hf] at h
    rename_i field
    cases hv : Types.projectVal field.storage.unpack <;> simp [hv] at h
    cases h; exact .newFixed (arrayField?_sound hf) hv
  case get x signed =>
    cases hf : arrayField? types x <;> simp [hf] at h
    rename_i field
    cases hv : field.storage.readType? signed <;> simp [hv] at h
    cases h; exact .get (arrayField?_sound hf) hv
  case set x =>
    cases hf : arrayField? types x <;> simp [hf] at h
    rename_i field
    cases hv : Types.projectVal field.storage.unpack <;> simp [hv] at h
    rcases h with ⟨hm, rfl⟩; exact .set (arrayField?_sound hf) hm hv
  case fill x =>
    cases hf : arrayField? types x <;> simp [hf] at h
    rename_i field
    cases hv : Types.projectVal field.storage.unpack <;> simp [hv] at h
    rcases h with ⟨hm, rfl⟩; exact .fill (arrayField?_sound hf) hm hv
  case copy x y =>
    cases hd : arrayField? types x <;> simp [hd] at h
    cases hs : arrayField? types y <;> simp [hs] at h
    rcases h with ⟨⟨hm, matched⟩, rfl⟩
    exact .copy (arrayField?_sound hd) (arrayField?_sound hs) hm
      (Types.Algorithm.storageMatches_sound matched)
  case newData x y =>
    cases hf : arrayField? types x <;> simp [hf] at h
    rcases h with ⟨⟨hn, hd⟩, rfl⟩
    exact .newData (arrayField?_sound hf) hn hd
  case initData x y =>
    cases hf : arrayField? types x <;> simp [hf] at h
    rcases h with ⟨⟨⟨hm, hn⟩, hd⟩, rfl⟩
    exact .initData (arrayField?_sound hf) hm hn hd
  case newElem x y =>
    cases hf : arrayField? types x <;> simp [hf] at h
    cases he : elems[y]? <;> simp [he] at h
    rcases h with ⟨hm, rfl⟩
    exact .newElem (arrayField?_sound hf) he (Types.Algorithm.valMatches_sound hm)
  case initElem x y =>
    cases hf : arrayField? types x <;> simp [hf] at h
    cases he : elems[y]? <;> simp [he] at h
    rcases h with ⟨⟨hm, matched⟩, rfl⟩
    exact .initElem (arrayField?_sound hf) hm he (Types.Algorithm.valMatches_sound matched)

end Wasm
