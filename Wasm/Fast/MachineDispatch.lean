import Wasm.Fast.Machine

namespace Wasm.Fast.Machine

inductive RedexPlan where
  | ready (next : Configuration)
  | structures (change : StructChange) (code : List AdminInstr)

def RedexPlan.apply (plan : RedexPlan) (c : Configuration) : Configuration :=
  match plan with
  | .ready next => next
  | .structures change code => ⟨change.apply c.store, c.frame, code⟩

abbrev CheckedRedex (c : Configuration) :=
  Option {plan : RedexPlan // ConfigStep c (plan.apply c)}

private def checkedVectors (c : Configuration) : CheckedRedex c := by
  match h : stepVectors c.store c.frame c.code with
  | none => exact none
  | some next =>
    exact some ⟨.ready ({c with store := next.1, code := next.2}), .vectors (stepVectors_sound h)⟩

private def checkedArrays (c : Configuration) : CheckedRedex c := by
  match h : stepArrays c.store c.frame c.code with
  | none => exact none
  | some next =>
    exact some ⟨.ready ({c with store := next.1, code := next.2}), .arrays (stepArrays_sound h)⟩

private def checkedExceptions (c : Configuration) : CheckedRedex c := by
  match h : stepExceptions c.store c.frame c.code with
  | none => exact none
  | some next =>
    exact some ⟨.ready ({c with store := next.1, code := next.2}),
      .exceptions (stepExceptions_sound h)⟩

private def checkedLocals (c : Configuration) : CheckedRedex c := by
  match h : stepLocals c.frame c.code with
  | none => exact none
  | some next =>
    exact some ⟨.ready ({c with frame := next.1, code := next.2}), .locals (stepLocals_sound h)⟩

private def checkedCalls (c : Configuration) : CheckedRedex c := by
  match h : stepCalls c.store c.frame c.code with
  | none => exact none
  | some next =>
    exact some ⟨.ready ({c with code := next}), .call (stepCalls_sound h)⟩

private def checkedGlobals (c : Configuration) : CheckedRedex c := by
  match h : stepGlobals c.store c.frame c.code with
  | none => exact none
  | some next =>
    exact some ⟨.ready ({c with store := next.1, code := next.2}), .globals (stepGlobals_sound h)⟩

private def checkedMemory (c : Configuration) : CheckedRedex c := by
  match h : stepMemory c.store c.frame c.code with
  | none => exact none
  | some next =>
    exact some ⟨.ready ({c with store := next.1, code := next.2}), .memory (stepMemory_sound h)⟩

private def checkedReferences (c : Configuration) : CheckedRedex c := by
  match h : stepReferences c.store c.frame c.code with
  | none => exact none
  | some next =>
    exact some ⟨.ready ({c with code := next}), .references (stepReferences_sound h)⟩

private def checkedTables (c : Configuration) : CheckedRedex c := by
  match h : stepTables c.store c.frame c.code with
  | none => exact none
  | some next =>
    exact some ⟨.ready ({c with store := next.1, code := next.2}), .tables (stepTables_sound h)⟩

private def checkedBulk (c : Configuration) : CheckedRedex c := by
  match h : stepBulkMemory c.store c.frame c.code with
  | none => exact none
  | some next =>
    exact some ⟨.ready ({c with store := next.1, code := next.2}), .bulk (stepBulkMemory_sound h)⟩

private def checkedPure (c : Configuration) : CheckedRedex c := by
  match h : Wasm.step c.frame.module.types c.code with
  | none => exact none
  | some next =>
    exact some ⟨.ready ({c with code := next}), .pure (Wasm.step_sound h)⟩

private def checkedStructures (c : Configuration) : CheckedRedex c := by
  match h : planStructs c.store c.frame c.code with
  | none => exact none
  | some next => exact some ⟨.structures next.1 next.2, .structures (planStructs_sound h)⟩

-- Only the selected family sees the redex; it has no enclosing administrative contexts.
def dispatch (head : AdminInstr) (c : Configuration) : CheckedRedex c :=
  match head with
  | .instr i => match i with
    | .vector _ => checkedVectors c
    | .arrayOp _ => checkedArrays c
    | .structNew _ _ | .structGet _ _ _ | .structSet _ _ => checkedStructures c
    | .throw_ _ | .throwRef | .tryTable _ _ _ => checkedExceptions c
    | .localGet _ | .localSet _ | .localTee _ => checkedLocals c
    | .call _ | .callRef _ | .callIndirect _ _ | .returnCall _
      | .returnCallRef _ | .returnCallIndirect _ _ => checkedCalls c
    | .globalGet _ | .globalSet _ => checkedGlobals c
    | .load _ _ _ | .store _ _ _ | .memorySize _ | .memoryGrow _ => checkedMemory c
    | .memoryFill _ | .memoryCopy _ _ | .memoryInit _ _ | .dataDrop _ => checkedBulk c
    | .refNull _ | .refFunc _ | .refIsNull | .gcReference _ | .refAsNonNull
      | .refTest _ _ | .refCast _ _ | .brOnCast _ _ _ _ | .brOnNull _
      | .brOnNonNull _ => checkedReferences c
    | .tableGet _ | .tableSet _ | .tableSize _ | .tableGrow _ | .tableFill _
      | .tableCopy _ _ | .tableInit _ _ | .elemDrop _ => checkedTables c
    | _ => checkedPure c
  | .invoke _ _ | .invokeRef _ | .invokeDefined _ | .returnInvoke _ _
    | .returnInvokeRef _ | .returnInvokeDefined _ => checkedCalls c
  | .castFunc _ | .castDefined _ => checkedReferences c
  | .throwing _ => checkedExceptions c
  | _ => checkedPure c

def operandCount (store : Store) (frame : Frame) : AdminInstr → Option Nat
  | .instr i => match i with
    | .drop | .eqz _ | .if_ _ _ _ | .brIf _ | .brTable _ _ | .intUnary _ _
      | .intConvert _ | .localSet _ | .localTee _ | .globalSet _ | .load _ _ _
      | .memoryGrow _ | .refIsNull | .refAsNonNull | .refTest _ _ | .refCast _ _
      | .brOnCast _ _ _ _ | .brOnNull _ | .brOnNonNull _ | .tableGet _
      | .throwRef | .structGet _ _ _ => some 1
    | .binop _ _ | .intBinary _ _ | .intRel _ _ | .store _ _ _ | .structSet _ _
      | .tableSet _ | .tableGrow _ => some 2
    | .select _ | .memoryFill _ | .memoryCopy _ _ | .memoryInit _ _ | .tableFill _
      | .tableCopy _ _ | .tableInit _ _ => some 3
    | .vector op => some op.opcode.signature.params.length
    | .gcReference op => some (op.signature true).params.length
    | .arrayOp op => some op.operandCount
    | .structNew x false => do
      let type ← frame.module.definedTypes[x]?
      match ← type.expandComposite? with
      | .struct_ fields => some fields.length
      | _ => none
    | .block bt _ | .loop bt _ | .tryTable bt _ _ =>
      (bt.resolve frame.module.types).map fun ft => ft.params.length
    | .throw_ x => do
      let address ← frame.module.tags[x]?
      let tag ← store.tags[address.index]?
      some tag.type.params.length
    | .return_ | .br _ => none
    | _ => some 0
  | .invoke _ type | .returnInvoke _ type => some type.params.length
  | .invokeRef type | .returnInvokeRef type => some (type.params.length + 1)
  | .invokeDefined type | .returnInvokeDefined type =>
    some ((type.expand?.map fun ft => ft.params.length).getD 0 + 1)
  | .castFunc _ | .castDefined _ => some 1
  | _ => none

-- Boundary events inspect only the immediate suspended context.
def unwind (context : MachineContext) (head : Option AdminInstr)
    (c : Configuration) : CheckedRedex c :=
  match head with
  | some (.tailActivation _) => checkedCalls c
  | some (.throwing _) => checkedExceptions c
  | _ => match context.kind with
    | .handler _ => checkedExceptions c
    | _ => checkedPure c

end Wasm.Fast.Machine
