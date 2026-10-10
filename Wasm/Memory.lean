import Wasm.Runtime

namespace Wasm

def pageSize : Nat := 65536

def MemoryType.pageLimit (type : MemoryType) : Nat := 2 ^ (type.addrType.bits - 16)

def MemoryType.Valid (type : MemoryType) : Prop :=
  type.addrType.IsInteger ∧ type.min ≤ type.pageLimit ∧
    ∀ maximum ∈ type.max, type.min ≤ maximum ∧ maximum ≤ type.pageLimit

instance (type : MemoryType) : Decidable type.Valid := by
  unfold MemoryType.Valid
  infer_instance

def MemoryInst.pages (memory : MemoryInst) : Nat := memory.bytes.size / pageSize

def MemoryInst.Valid (memory : MemoryInst) : Prop :=
  memory.type.Valid ∧ memory.bytes.size % pageSize = 0 ∧ memory.type.min = memory.pages

def ModuleInst.memAddr? (module : ModuleInst) (index : Nat) : Option MemAddr := module.mems[index]?
def Store.mem? (store : Store) (address : MemAddr) : Option MemoryInst := store.mems[address.index]?
def Store.resolveMem? (store : Store) (module : ModuleInst) (index : Nat) : Option MemoryInst :=
  (module.memAddr? index).bind store.mem?
def Store.allocateMemory (store : Store) (memory : MemoryInst) : MemAddr × Store :=
  (⟨store.mems.length⟩, { store with mems := store.mems ++ [memory] })

theorem Store.allocateMemory_lookup (store : Store) (memory : MemoryInst) :
    (store.allocateMemory memory).2.mem? (store.allocateMemory memory).1 = some memory := by
  simp [Store.allocateMemory, Store.mem?]

theorem Store.allocateMemory_preserves (store : Store) (memory : MemoryInst) (address : MemAddr)
    (h : address.index < store.mems.length) :
    (store.allocateMemory memory).2.mem? address = store.mem? address := by
  simp [Store.allocateMemory, Store.mem?, List.getElem?_append, h]
def Store.setMemory (store : Store) (address : MemAddr) (memory : MemoryInst) : Store :=
  { store with mems := store.mems.set address.index memory }

def Value.unsigned : Value → Nat
  | .i32 bits => bits.toNat
  | .i64 bits => bits.toNat
  | .f32 bits => bits.toNat
  | .f64 bits => bits.toNat
  | .ref _ => 0
def Value.ofNat (type : ValType) (n : Nat) : Value :=
  match type with
  | .i32 => .i32 (BitVec.ofNat 32 n)
  | .i64 => .i64 (BitVec.ofNat 64 n)
  | .f32 => .f32 (BitVec.ofNat 32 n)
  | .f64 => .f64 (BitVec.ofNat 64 n)
  | .ref kind | .refNonNull kind => .ref (.null kind)
def Value.ofInt (type : ValType) (n : Int) : Value :=
  match type with
  | .i32 => .i32 (BitVec.ofInt 32 n)
  | .i64 => .i64 (BitVec.ofInt 64 n)
  | .f32 => .f32 (BitVec.ofInt 32 n)
  | .f64 => .f64 (BitVec.ofInt 64 n)
  | .ref kind | .refNonNull kind => .ref (.null kind)
def Value.address? (type : ValType) (value : Value) : Option Nat :=
  if type.IsInteger ∧ value.type = type then some value.unsigned else none

/-- Decode little-endian bytes before extending a packed load. -/
def decodeBytes : List Byte → Nat
  | [] => 0
  | b :: tail => b.toNat + 256 * decodeBytes tail

def encodeBytes (n count : Nat) : Array Byte :=
  ((List.range count).map fun i => BitVec.ofNat 8 (n / 256 ^ i)).toArray

theorem encodeBytes_size : (encodeBytes n count).size = count := by simp [encodeBytes]

def decodeLoad (op : LoadOp) (bytes : Array Byte) : Value :=
  let n := decodeBytes bytes.toList
  let width := 8 * op.bytes
  let signed : Int := if op.signed && n ≥ 2 ^ (width - 1) then (n : Int) - 2 ^ width else n
  Value.ofInt op.type signed

def MemoryInst.read (memory : MemoryInst) (start count : Nat) : Array Byte :=
  memory.bytes.extract start (start + count)

def MemoryInst.write (memory : MemoryInst) (start : Nat) (bytes : Array Byte) : MemoryInst :=
  { memory with bytes := memory.bytes.extract 0 start ++ bytes ++
      memory.bytes.extract (start + bytes.size) memory.bytes.size }

theorem MemoryInst.read_size (memory : MemoryInst) (start count : Nat)
    (h : start + count ≤ memory.bytes.size) : (memory.read start count).size = count := by
  simp [MemoryInst.read, Array.size_extract]
  omega

theorem MemoryInst.write_size (memory : MemoryInst) (start : Nat) (bytes : Array Byte)
    (h : start + bytes.size ≤ memory.bytes.size) :
    (memory.write start bytes).bytes.size = memory.bytes.size := by
  simp [MemoryInst.write, Array.size_extract]
  omega

def MemoryInst.CanGrow (memory : MemoryInst) (delta : Nat) : Prop :=
  memory.pages + delta ≤ memory.type.pageLimit ∧
    match memory.type.max with
    | none => True
    | some maximum => memory.pages + delta ≤ maximum

instance (memory : MemoryInst) (delta : Nat) : Decidable (memory.CanGrow delta) := by
  unfold MemoryInst.CanGrow
  cases memory.type.max <;> infer_instance

def MemoryInst.grown (memory : MemoryInst) (delta : Nat) : MemoryInst :=
  { type := { memory.type with min := memory.pages + delta },
    bytes := memory.bytes ++ Array.replicate (delta * pageSize) 0 }

theorem MemoryInst.grown_size (memory : MemoryInst) (delta : Nat) :
    (memory.grown delta).bytes.size = memory.bytes.size + delta * pageSize := by
  simp [MemoryInst.grown]

theorem MemoryInst.grown_pages (memory : MemoryInst) (delta : Nat) :
    (memory.grown delta).pages = memory.pages + delta := by
  simp [MemoryInst.pages, MemoryInst.grown, pageSize, Nat.add_mul_div_right]

/-- Executable embedder policy: fail growth beyond 1024 pages (64 MiB).
The relational semantics permits resource failure at any size, independently of this budget.
-/
def growthBudgetPages : Nat := 1024

def MemoryInst.grow? (memory : MemoryInst) (delta : Nat)
    (budgetPages : Nat := growthBudgetPages) : Option MemoryInst :=
  if memory.CanGrow delta ∧ memory.pages + delta ≤ budgetPages then
    some (memory.grown delta)
  else none

theorem MemoryInst.grow?_sound {memory : MemoryInst} {delta budget : Nat}
    (h : memory.grow? delta budget = some next) :
    memory.CanGrow delta ∧ next = memory.grown delta := by
  unfold MemoryInst.grow? at h
  split at h
  · rename_i valid
    cases h
    exact ⟨valid.1, rfl⟩
  · cases h

inductive MemoryReduces (memory : MemoryInst) :
    List AdminInstr → Option MemoryInst → List AdminInstr → Prop where
  | load (hn : Value.address? memory.type.addrType a = some n)
      (hb : n + arg.offset + op.bytes ≤ memory.bytes.size) :
      MemoryReduces memory [.instr (.const a), .instr (.load op x arg)] none
        (values [decodeLoad op (memory.read (n + arg.offset) op.bytes)])
  | loadTrap (hn : Value.address? memory.type.addrType a = some n)
      (hb : n + arg.offset + op.bytes > memory.bytes.size) :
      MemoryReduces memory [.instr (.const a), .instr (.load op x arg)] none [.trap]
  | store (hn : Value.address? memory.type.addrType a = some n) (ht : v.type = op.type)
      (hb : n + arg.offset + op.bytes ≤ memory.bytes.size) :
      MemoryReduces memory [.instr (.const a), .instr (.const v), .instr (.store op x arg)]
        (some (memory.write (n + arg.offset) (encodeBytes v.unsigned op.bytes))) []
  | storeTrap (hn : Value.address? memory.type.addrType a = some n) (ht : v.type = op.type)
      (hb : n + arg.offset + op.bytes > memory.bytes.size) :
      MemoryReduces memory [.instr (.const a), .instr (.const v), .instr (.store op x arg)]
        none [.trap]
  | size : MemoryReduces memory [.instr (.memorySize x)] none
      (values [Value.ofNat memory.type.addrType memory.pages])
  | grow (hn : Value.address? memory.type.addrType v = some delta)
      (hg : memory.CanGrow delta) :
      MemoryReduces memory [.instr (.const v), .instr (.memoryGrow x)]
        (some (memory.grown delta)) (values [Value.ofNat memory.type.addrType memory.pages])
  | growFail (hn : Value.address? memory.type.addrType v = some delta) :
      MemoryReduces memory [.instr (.const v), .instr (.memoryGrow x)] none
        (values [Value.ofInt memory.type.addrType (-1)])

def Store.applyMemory (store : Store) (address : MemAddr) (change : Option MemoryInst) : Store :=
  match change with
  | none => store
  | some memory => store.setMemory address memory

def memoryIndex? : List AdminInstr → Option Nat
  | [.instr (.memorySize x)] => some x
  | [.instr (.const _), .instr (.memoryGrow x)] => some x
  | [.instr (.const _), .instr (.load _ x _)] => some x
  | [.instr (.const _), .instr (.const _), .instr (.store _ x _)] => some x
  | _ => none

inductive MemoryStep : Store → Frame → List AdminInstr → Store → List AdminInstr → Prop where
  | access (ha : state.module.memAddr? x = some address)
      (hm : store.mem? address = some memory)
      (hi : memoryIndex? es = some x)
      (hr : MemoryReduces memory es change es') :
      MemoryStep store state es (store.applyMemory address change) es'
  | context : MemoryStep store state es store' es' →
      MemoryStep store state (values vs ++ es ++ tail) store' (values vs ++ es' ++ tail)
  | label : MemoryStep store state body store' body' →
      MemoryStep store state [.label n continuation body] store' [.label n continuation body']
  | frame : MemoryStep store inner body store' body' →
      MemoryStep store state [.frame n inner body] store' [.frame n inner body']

theorem MemoryStep.functions_preserved (h : MemoryStep store state es store' es') :
    store'.funcs = store.funcs := by
  induction h with
  | access _ _ _ hr => cases hr <;> rfl
  | context _ ih | label _ ih | frame _ ih => exact ih

theorem MemoryStep.globals_preserved (h : MemoryStep store state es store' es') :
    store'.globals = store.globals := by
  induction h with
  | access _ _ _ hr => cases hr <;> rfl
  | context _ ih | label _ ih | frame _ ih => exact ih

theorem MemoryStep.count_preserved (h : MemoryStep store state es store' es') :
    store'.mems.length = store.mems.length := by
  induction h with
  | access _ _ _ hr => cases hr <;> simp [Store.applyMemory, Store.setMemory]
  | context _ ih | label _ ih | frame _ ih => exact ih

end Wasm
