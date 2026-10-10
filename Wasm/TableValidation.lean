import Wasm.Tables

namespace Wasm

inductive ReferenceInstrTyping (funcs : List FuncType) (declared : List Nat) :
    Instr → List ValType → List ValType → Prop where
  | null : ReferenceInstrTyping funcs declared (.refNull kind) [] [.ref kind]
  | func (hf : funcs[x]? = some ft) (hd : x ∈ declared) :
      ReferenceInstrTyping funcs declared (.refFunc x) [] [.ref .func]
  | funcNonNull (hf : funcs[x]? = some ft) (hd : x ∈ declared) :
      ReferenceInstrTyping funcs declared (.refFunc x) [] [.refNonNull .func]
  | isNull : ReferenceInstrTyping funcs declared .refIsNull [.ref kind] [.i32]
  | isNullNonNull : ReferenceInstrTyping funcs declared .refIsNull [.refNonNull kind] [.i32]

inductive TableInstrTyping (types : TypeContext) (tables : List TableType)
    (elems : List RefKind) : Instr → List ValType → List ValType → Prop where
  | get (ht : tables[x]? = some table) :
      TableInstrTyping types tables elems (.tableGet x) [table.addrType] [table.refType]
  | set (ht : tables[x]? = some table) :
      TableInstrTyping types tables elems (.tableSet x) [table.addrType, table.refType] []
  | size (ht : tables[x]? = some table) :
      TableInstrTyping types tables elems (.tableSize x) [] [table.addrType]
  | grow (ht : tables[x]? = some table) :
      TableInstrTyping types tables elems (.tableGrow x)
        [table.refType, table.addrType] [table.addrType]
  | fill (ht : tables[x]? = some table) :
      TableInstrTyping types tables elems (.tableFill x)
        [table.addrType, table.refType, table.addrType] []
  | copy (hd : tables[x]? = some dst) (hs : tables[y]? = some src) (hk : src.kind = dst.kind)
      (hn : src.nullable = false ∨ dst.nullable = true) :
      TableInstrTyping types tables elems (.tableCopy x y)
        [dst.addrType, src.addrType, dst.addrType.minAddress src.addrType] []
  | init (ht : tables[x]? = some table) (he : elems[y]? = some table.kind)
      (hn : table.nullable = true) :
      TableInstrTyping types tables elems (.tableInit x y) [table.addrType, .i32, .i32] []
  | drop (he : elems[y]? = some kind) :
      TableInstrTyping types tables elems (.elemDrop y) [] []
  | indirect (ht : tables[x]? = some table) (hk : table.kind = .func)
      (hf : types[y]? = some ft) :
      TableInstrTyping types tables elems (.callIndirect x y)
        (ft.params ++ [table.addrType]) ft.results

end Wasm
