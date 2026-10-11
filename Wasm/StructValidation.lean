import Wasm.Runtime

namespace Wasm

def structFieldTypes (fields : List Types.FieldType) : Option (List ValType) :=
  fields.mapM fun field => Types.projectVal field.storage.unpack

def Types.StorageType.readType? (signed : Option Bool) : Types.StorageType → Option Wasm.ValType
  | .val type => if signed.isNone then Types.projectVal type else none
  | .i8 | .i16 => if signed.isSome then some .i32 else none

inductive StructInstrTyping (types : TypeContext) :
    Instr → List ValType → List ValType → Prop where
  | new (ht : types[x]? = some (.struct_ fields))
      (hf : structFieldTypes fields = some ts) :
      StructInstrTyping types (.structNew x false) ts [.refNonNull (.typeIdx x)]
  | newDefault (ht : types[x]? = some (.struct_ fields))
      (hf : structFieldTypes fields = some ts) (hd : ts.all ValType.defaultable = true) :
      StructInstrTyping types (.structNew x true) [] [.refNonNull (.typeIdx x)]
  | get (ht : types[x]? = some (.struct_ fields)) (hf : fields[y]? = some field)
      (hv : field.storage.readType? signed = some type) :
      StructInstrTyping types (.structGet x y signed) [.ref (.typeIdx x)] [type]
  | set (ht : types[x]? = some (.struct_ fields)) (hf : fields[y]? = some field)
      (hm : field.mutable = true) (hv : Types.projectVal field.storage.unpack = some type) :
      StructInstrTyping types (.structSet x y) [.ref (.typeIdx x), type] []

def structSignature? (types : TypeContext) : Instr → Option FuncType
  | .structNew x default => do
    let .struct_ fields ← types[x]? | none
    let ts ← structFieldTypes fields
    if default && !ts.all ValType.defaultable then none
    else some ⟨if default then [] else ts, [.refNonNull (.typeIdx x)]⟩
  | .structGet x y signed => do
    let .struct_ fields ← types[x]? | none
    let field ← fields[y]?
    let type ← field.storage.readType? signed
    some ⟨[.ref (.typeIdx x)], [type]⟩
  | .structSet x y => do
    let .struct_ fields ← types[x]? | none
    let field ← fields[y]?
    if !field.mutable then none
    else do
      let type ← Types.projectVal field.storage.unpack
      some ⟨[.ref (.typeIdx x), type], []⟩
  | _ => none

theorem structSignature?_sound (h : structSignature? types instr = some signature) :
    StructInstrTyping types instr signature.params signature.results := by
  cases instr <;> simp only [structSignature?, bind, Option.bind] at h
  all_goals try contradiction
  case structNew x default =>
    cases ht : types[x]? <;> simp [ht] at h
    rename_i comp
    cases comp <;> simp_all
    rename_i fields
    cases hf : structFieldTypes fields <;> simp [hf] at h
    cases default <;> simp at h
    · cases h; exact .new ht hf
    · rcases h with ⟨hd, rfl⟩
      exact .newDefault ht hf (by simpa only [List.all_eq_true] using hd)
  case structGet x y signed =>
    cases ht : types[x]? <;> simp [ht] at h
    rename_i comp
    cases comp <;> simp_all
    rename_i fields
    cases hf : fields[y]? <;> simp [hf] at h
    rename_i field
    cases hv : Types.StorageType.readType? signed field.storage <;> simp [hv] at h
    cases h
    exact .get ht hf hv
  case structSet x y =>
    cases ht : types[x]? <;> simp [ht] at h
    rename_i comp
    cases comp <;> simp_all
    rename_i fields
    cases hf : fields[y]? <;> simp [hf] at h
    rename_i field
    cases hv : Types.projectVal field.storage.unpack <;> simp [hv] at h
    rcases h with ⟨hm, rfl⟩
    exact .set ht hf hm hv

end Wasm
