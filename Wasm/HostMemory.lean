import Wasm.Host
import Wasm.Memory

namespace Wasm

/-! Checked byte access and transactional memory effects at host-call boundaries. -/

/-- The index is relative to the calling module, not the global store address space. -/
structure HostMemoryWrite where
  memoryIndex : Nat
  offset : Nat
  bytes : Array Byte
  deriving BEq, Repr

inductive HostMemoryError where
  | unknownMemory (index : Nat)
  | missingMemory (address : MemAddr)
  | outOfBounds (index offset count : Nat)
  deriving BEq, Repr

/-- Lookup and mathematical range bounds, independent of the executable checker. -/
structure HostMemoryAccess (store : Store) (caller : ModuleInst)
    (index offset count : Nat) (address : MemAddr) (memory : MemoryInst) : Prop where
  accessible : caller.memAddr? index = some address
  found : store.mem? address = some memory
  bounds : offset + count ≤ memory.bytes.size

private def checkHostMemoryAccess (store : Store) (caller : ModuleInst)
    (index offset count : Nat) :
    Except HostMemoryError { pair : MemAddr × MemoryInst //
      HostMemoryAccess store caller index offset count pair.1 pair.2 } :=
  match accessible : caller.memAddr? index with
  | none => .error (.unknownMemory index)
  | some address =>
    match found : store.mem? address with
    | none => .error (.missingMemory address)
    | some memory =>
      if bounds : offset + count ≤ memory.bytes.size then
        .ok ⟨(address, memory), ⟨accessible, found, bounds⟩⟩
      else .error (.outOfBounds index offset count)

inductive HostMemoryRead (store : Store) (caller : ModuleInst)
    (index offset count : Nat) : Array Byte → Prop where
  | read (access : HostMemoryAccess store caller index offset count address memory) :
      HostMemoryRead store caller index offset count (memory.read offset count)

/-- Read from the immutable suspension snapshot, using the active caller's memory mapping. -/
def readHostMemory (pending : PendingHostCall) (index offset count : Nat) :
    Except HostMemoryError (Array Byte) := do
  let range ← checkHostMemoryAccess pending.source.store pending.request.caller.module
    index offset count
  return range.val.2.read offset count

theorem readHostMemory_sound (h : readHostMemory pending index offset count = .ok bytes) :
    HostMemoryRead pending.source.store pending.request.caller.module index offset count bytes := by
  unfold readHostMemory at h
  cases checked : checkHostMemoryAccess pending.source.store pending.request.caller.module
      index offset count with
  | error error => simp [checked, bind, Except.bind] at h
  | ok range =>
    simp [checked, bind, Except.bind, pure, Except.pure] at h
    subst bytes
    exact .read range.property

theorem HostMemoryRead.size (h : HostMemoryRead store caller index offset count bytes) :
    bytes.size = count := by
  cases h with
  | read access => exact MemoryInst.read_size _ _ _ access.bounds

/-- Sequential host writes. Later writes win on overlap, including aliased module indices. -/
inductive HostMemoryEffects (caller : ModuleInst) :
    Store → List HostMemoryWrite → Store → Prop where
  | nil : HostMemoryEffects caller store [] store
  | cons (access : HostMemoryAccess store caller write.memoryIndex write.offset
      write.bytes.size address memory)
      (rest : HostMemoryEffects caller
        (store.setMemory address (memory.write write.offset write.bytes)) writes next) :
      HostMemoryEffects caller store (write :: writes) next

private def checkHostMemoryWrites (caller : ModuleInst) (store : Store) :
    (writes : List HostMemoryWrite) →
    Except HostMemoryError { next : Store // HostMemoryEffects caller store writes next }
  | [] => .ok ⟨store, .nil⟩
  | write :: writes => do
    let range ← checkHostMemoryAccess store caller write.memoryIndex write.offset write.bytes.size
    let next := store.setMemory range.val.1 (range.val.2.write write.offset write.bytes)
    let rest ← checkHostMemoryWrites caller next writes
    return ⟨rest.val, .cons range.property rest.property⟩

inductive HostMemoryReplyError where
  | reply (error : HostReplyError)
  | memory (error : HostMemoryError)
  deriving BEq, Repr

/-- Effectful returns are host transitions, never internal Wasm reductions. -/
inductive HostMemoryBoundaryStep :
    Configuration → List HostMemoryWrite → List Value → Configuration → Prop where
  | returned (site : HostSite store frame code request context)
      (scalar : request.scalar = true)
      (effects : HostMemoryEffects request.caller.module store writes store')
      (typed : ArgsTyped store' results request.type.results) :
      HostMemoryBoundaryStep ⟨store, frame, code⟩ writes results
        ⟨store', frame, context.fill
          (if request.tailCall then [.tailActivation (values results)] else values results)⟩

/-- Stage all writes privately, validate results in the resulting store, and commit together.
Errors return no changed configuration; the original pending call remains reusable. -/
def resumeHostCallWithMemory (pending : PendingHostCall) (results : List Value)
    (writes : List HostMemoryWrite) : Except HostMemoryReplyError Configuration := do
  if pending.request.scalar then
    let changed ← (checkHostMemoryWrites pending.request.caller.module
      pending.source.store writes).mapError HostMemoryReplyError.memory
    match checkArgs changed.val results pending.request.type.results with
    | none => .error (.reply .invalidResults)
    | some _ => .ok { pending.source with
        store := changed.val
        code := pending.context.fill (pending.resultCode results) }
  else .error (.reply .unsupportedSignature)

theorem resumeHostCallWithMemory_sound
    (h : resumeHostCallWithMemory pending results writes = .ok next) :
    HostMemoryBoundaryStep pending.source writes results next := by
  unfold resumeHostCallWithMemory at h
  split at h
  · rename_i scalar
    cases checked : checkHostMemoryWrites pending.request.caller.module
        pending.source.store writes with
    | error error => simp [checked, Except.mapError, bind, Except.bind] at h
    | ok changed =>
      simp only [checked, Except.mapError, bind, Except.bind] at h
      cases typed : checkArgs changed.val results pending.request.type.results with
      | none => simp [typed] at h
      | some proof =>
        simp [typed] at h
        subst next
        exact .returned pending.evidence scalar changed.property proof.down
  · cases h

theorem MemoryInst.host_write_valid {memory : MemoryInst} {bytes : Array Byte}
    (valid : memory.Valid)
    (bounds : offset + bytes.size ≤ memory.bytes.size) :
    (memory.write offset bytes).Valid := by
  simpa [MemoryInst.Valid, MemoryInst.pages, MemoryInst.write_size _ _ _ bounds,
    show (memory.write offset bytes).type = memory.type from rfl] using valid

theorem MemoryInst.host_write_outside {memory : MemoryInst} {bytes : Array Byte}
    (bounds : offset + bytes.size ≤ memory.bytes.size)
    (outside : index < offset ∨ offset + bytes.size ≤ index) :
    (memory.write offset bytes).bytes[index]? = memory.bytes[index]? := by
  have beforeSize : (memory.bytes.extract 0 offset).size = offset := by
    simp [Array.size_extract]
    omega
  simp only [MemoryInst.write]
  rcases outside with before | after
  · rw [Array.getElem?_append_left (by simp [beforeSize]; omega)]
    rw [Array.getElem?_append_left (by omega)]
    simp [show min offset memory.bytes.size = offset by omega, before]
  · rw [Array.getElem?_append_right (by simp [beforeSize]; omega)]
    rw [Array.getElem?_extract]
    simp only [Array.size_append, beforeSize, Nat.min_self]
    have restored : offset + bytes.size + (index - (offset + bytes.size)) = index := by omega
    rw [restored]
    by_cases present : index < memory.bytes.size
    · rw [if_pos (by omega)]
    · rw [if_neg (by omega)]
      simp [show memory.bytes.size ≤ index by omega]

theorem MemoryInst.host_write_inside {memory : MemoryInst} {bytes : Array Byte}
    (bounds : offset + bytes.size ≤ memory.bytes.size)
    (inside : index < bytes.size) :
    (memory.write offset bytes).bytes[offset + index]? = bytes[index]? := by
  have beforeSize : (memory.bytes.extract 0 offset).size = offset := by
    simp [Array.size_extract]
    omega
  simp only [MemoryInst.write]
  rw [Array.getElem?_append_left (by simp [beforeSize]; omega)]
  rw [Array.getElem?_append_right (by omega)]
  simp [beforeSize]

/-- Equality here preserves every non-memory component, including GC and exception objects. -/
def Store.withoutHostMemories (store : Store) : Store := { store with mems := [] }

def Store.hostMemoryShape (store : Store) : List (MemoryType × Nat) :=
  store.mems.map fun memory => (memory.type, memory.bytes.size)

theorem HostMemoryEffects.other_components
    (effects : HostMemoryEffects caller store writes next) :
    next.withoutHostMemories = store.withoutHostMemories := by
  induction effects with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem HostMemoryEffects.shape (effects : HostMemoryEffects caller store writes next) :
    next.hostMemoryShape = store.hostMemoryShape := by
  induction effects with
  | nil => rfl
  | @cons store address memory writes next write access _ ih =>
    rw [ih]
    have mapped : store.hostMemoryShape[address.index]? =
        some (memory.type, memory.bytes.size) := by
      simp only [Store.hostMemoryShape, List.getElem?_map]
      change (store.mem? address).map (fun memory => (memory.type, memory.bytes.size)) = _
      rw [access.found]
      rfl
    simp only [Store.hostMemoryShape, Store.setMemory, List.map_set,
      MemoryInst.write_size _ _ _ access.bounds]
    change store.hostMemoryShape.set address.index (memory.type, memory.bytes.size) =
      store.hostMemoryShape
    obtain ⟨bound, equality⟩ := List.getElem?_eq_some_iff.mp mapped
    rw [← equality]
    exact List.set_getElem_self bound

theorem HostMemoryEffects.memories_valid (effects : HostMemoryEffects caller store writes next)
    (valid : ∀ memory ∈ store.mems, memory.Valid) :
    ∀ memory ∈ next.mems, memory.Valid := by
  induction effects with
  | nil => exact valid
  | @cons store address memory writes next write access _ ih =>
    apply ih
    intro candidate member
    rcases List.mem_or_eq_of_mem_set member with original | replaced
    · exact valid candidate original
    · subst candidate
      exact MemoryInst.host_write_valid
        (valid memory (List.mem_of_getElem? access.found)) access.bounds

/-- Read a byte by store address, including an explicit `none` for absent memory or byte. -/
def Store.hostByte? (store : Store) (address : MemAddr) (index : Nat) : Option Byte :=
  (store.mem? address).bind fun memory => memory.bytes[index]?

theorem HostMemoryAccess.byte_outside
    {write : HostMemoryWrite}
    (access : HostMemoryAccess store caller write.memoryIndex write.offset
      write.bytes.size address memory)
    (outside : caller.memAddr? write.memoryIndex = some queried →
      index < write.offset ∨ write.offset + write.bytes.size ≤ index) :
    (store.setMemory address (memory.write write.offset write.bytes)).hostByte? queried index =
      store.hostByte? queried index := by
  by_cases same : address = queried
  · subst queried
    have bound : address.index < store.mems.length := by
      have found := access.found
      simp only [Store.mem?] at found
      exact (List.getElem?_eq_some_iff.mp found).1
    simp only [Store.hostByte?, Store.setMemory, Store.mem?, List.getElem?_set_self bound]
    rw [show store.mems[address.index]? = some memory from access.found]
    exact MemoryInst.host_write_outside access.bounds (outside access.accessible)
  · have different : address.index ≠ queried.index := by
      intro equality
      apply same
      cases address; cases queried; simp_all
    simp [Store.hostByte?, Store.setMemory, Store.mem?, List.getElem?_set_ne different]

theorem HostMemoryEffects.bytes_outside
    (effects : HostMemoryEffects caller store writes next)
    (outside : ∀ write ∈ writes, caller.memAddr? write.memoryIndex = some address →
      index < write.offset ∨ write.offset + write.bytes.size ≤ index) :
    next.hostByte? address index = store.hostByte? address index := by
  induction effects with
  | nil => rfl
  | @cons store selected memory writes next write access _ ih =>
    rw [ih (by intro write member; exact outside write (by simp [member]))]
    exact access.byte_outside (outside write (by simp))

theorem HostMemoryEffects.unwritten_memory
    (effects : HostMemoryEffects caller store writes next)
    (unwritten : ∀ write ∈ writes, caller.memAddr? write.memoryIndex ≠ some address) :
    next.mem? address = store.mem? address := by
  induction effects with
  | nil => rfl
  | @cons store selected memory writes next write access _ ih =>
    rw [ih (by intro write member; exact unwritten write (by simp [member]))]
    have different : selected.index ≠ address.index := by
      intro equality
      have same : selected = address := by cases selected; cases address; simp_all
      exact unwritten write (by simp) (same ▸ access.accessible)
    exact List.getElem?_set_ne different

theorem HostMemoryEffects.value_typing (effects : HostMemoryEffects caller store writes next)
    (typed : Typed store value type) : Typed next value type := by
  apply typed.store_funcs
  · simpa only [Store.withoutHostMemories] using congrArg Store.funcs effects.other_components
  · simpa only [Store.withoutHostMemories] using congrArg Store.structs effects.other_components
  · simpa only [Store.withoutHostMemories] using congrArg Store.arrays effects.other_components

theorem HostMemoryEffects.arguments_typing (effects : HostMemoryEffects caller store writes next)
    (typed : ArgsTyped store args types) : ArgsTyped next args types := by
  induction typed with
  | nil => exact .nil
  | cons head _ ih => exact .cons (effects.value_typing head) ih

theorem HostMemoryBoundaryStep.other_components
    (step : HostMemoryBoundaryStep config writes results next) :
    next.store.withoutHostMemories = config.store.withoutHostMemories := by
  cases step with
  | returned _ _ effects _ => exact effects.other_components

theorem HostMemoryBoundaryStep.shape
    (step : HostMemoryBoundaryStep config writes results next) :
    next.store.hostMemoryShape = config.store.hostMemoryShape := by
  cases step with
  | returned _ _ effects _ => exact effects.shape

theorem HostMemoryBoundaryStep.memories_valid
    (step : HostMemoryBoundaryStep config writes results next)
    (valid : ∀ memory ∈ config.store.mems, memory.Valid) :
    ∀ memory ∈ next.store.mems, memory.Valid := by
  cases step with
  | returned _ _ effects _ => exact effects.memories_valid valid

theorem HostMemoryBoundaryStep.frame_preserved
    (step : HostMemoryBoundaryStep config writes results next) :
    next.frame = config.frame := by cases step; rfl

theorem resumeHostCallWithMemory_empty : resumeHostCallWithMemory pending results [] =
    (resumeHostCall pending (.values results)).mapError HostMemoryReplyError.reply := by
  simp only [resumeHostCallWithMemory, checkHostMemoryWrites, resumeHostCall]
  split <;> simp_all [Except.mapError, bind, Except.bind]
  split <;> simp_all

/-- Successful resumption exposes the exact checked effects and retains every saved context. -/
theorem resumeHostCallWithMemory_spec
    (h : resumeHostCallWithMemory pending results writes = .ok next) :
    HostMemoryEffects pending.request.caller.module pending.source.store writes next.store ∧
      next.frame = pending.source.frame ∧
      next.code = pending.context.fill (pending.resultCode results) := by
  unfold resumeHostCallWithMemory at h
  split at h
  · cases checked : checkHostMemoryWrites pending.request.caller.module
        pending.source.store writes with
    | error error => simp [checked, Except.mapError, bind, Except.bind] at h
    | ok changed =>
      simp only [checked, Except.mapError, bind, Except.bind] at h
      cases typed : checkArgs changed.val results pending.request.type.results with
      | none => simp [typed] at h
      | some proof =>
        simp [typed] at h
        subst next
        exact ⟨changed.property, rfl, rfl⟩
  · cases h

theorem resumeHostCallWithMemory_bytes_outside
    (resumed : resumeHostCallWithMemory pending results writes = .ok next)
    (outside : ∀ write ∈ writes,
      pending.request.caller.module.memAddr? write.memoryIndex = some address →
        index < write.offset ∨ write.offset + write.bytes.size ≤ index) :
    next.store.hostByte? address index = pending.source.store.hostByte? address index :=
  (resumeHostCallWithMemory_spec resumed).1.bytes_outside outside

/-- Ordinary execution and both host interfaces share an explicit extended trace relation. -/
inductive HostMemoryExecutionStep : Configuration → Configuration → Prop where
  | existing : HostExecutionStep config next → HostMemoryExecutionStep config next
  | memory : HostMemoryBoundaryStep config writes results next →
      HostMemoryExecutionStep config next

inductive HostMemoryExecutionSteps : Configuration → Configuration → Prop where
  | refl : HostMemoryExecutionSteps config config
  | cons : HostMemoryExecutionStep config middle → HostMemoryExecutionSteps middle final →
      HostMemoryExecutionSteps config final

theorem HostExecutionSteps.toHostMemoryExecutionSteps (steps : HostExecutionSteps config final) :
    HostMemoryExecutionSteps config final := by
  induction steps with
  | refl => exact .refl
  | cons step _ ih => exact .cons (.existing step) ih

theorem HostMemoryExecutionSteps.trans (first : HostMemoryExecutionSteps config middle)
    (second : HostMemoryExecutionSteps middle final) : HostMemoryExecutionSteps config final := by
  induction first with
  | refl => exact second
  | cons step _ ih => exact .cons step (ih second)

theorem runUntilHost_resume_memory_sound
    (suspended : (runUntilHost fuel initial).status = .pending pending)
    (resumed : resumeHostCallWithMemory pending results writes = .ok next) :
    HostMemoryExecutionSteps initial next := by
  have boundary := resumeHostCallWithMemory_sound resumed
  rw [runUntilHost_pending_source suspended] at boundary
  exact runUntilHost_sound.toHostExecutionSteps.toHostMemoryExecutionSteps.trans
    (.cons (.memory boundary) .refl)

end Wasm
