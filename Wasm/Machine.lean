import Wasm.Correspondence

namespace Wasm.Execution

inductive MachineContextKind where
  | label (arity : Nat) (continuation : List Instr)
  | handler (catches : List Catch)
  | call (arity : Nat) (caller : Frame)
  deriving BEq, Repr

structure MachineContext where
  kind : MachineContextKind
  operands : List Value
  rest : List AdminInstr
  deriving BEq, Repr

-- Contexts store operands in top-first order, just like the active operand stack.
def MachineContext.wrap (context : MachineContext) (c : Configuration) : Configuration :=
  let (frame, instruction) := match context.kind with
    | .label n continuation => (c.frame, AdminInstr.label n continuation c.code)
    | .handler catches => (c.frame, AdminInstr.handler catches c.code)
    | .call n caller => (caller, AdminInstr.frame n c.frame c.code)
  ⟨c.store, frame, values context.operands.reverse ++ [instruction] ++ context.rest⟩

structure Machine where
  store : Store
  frame : Frame
  code : List AdminInstr
  operands : List Value := []
  contexts : List MachineContext := []
  deriving BEq, Repr

namespace Machine

def active (m : Machine) : Configuration :=
  ⟨m.store, m.frame, values m.operands.reverse ++ m.code⟩

def plug : List MachineContext → Configuration → Configuration
  | [], c => c
  | context :: rest, c => plug rest (context.wrap c)

def toConfiguration (m : Machine) : Configuration := plug m.contexts m.active

def toSpec (m : Machine) : Wasm.Configuration := m.toConfiguration.toSpec

def ofConfiguration (c : Configuration) : Machine := ⟨c.store, c.frame, c.code, [], []⟩

@[simp] theorem toConfiguration_ofConfiguration (c : Configuration) :
    (ofConfiguration c).toConfiguration = c := by
  cases c; rfl

-- Lifting is entirely in proofs: execution never reconstructs enclosing code.
theorem inValues (h : ConfigStep c next) (vs : List Value) (tail : List AdminInstr) :
    ConfigStep ⟨c.store, c.frame, values vs ++ c.code ++ tail⟩
      ⟨next.store, next.frame, values vs ++ next.code ++ tail⟩ := by
  cases h with
  | vectors h => exact .vectors (.context h)
  | arrays h => exact .arrays (.context h)
  | structures h => exact .structures (.context h)
  | exceptions h => exact .exceptions (.context h)
  | pure h => exact .pure (.context h)
  | locals h => exact .locals (.context h)
  | call h => exact .call (.context h)
  | globals h => exact .globals (.context h)
  | memory h => exact .memory (.context h)
  | references h => exact .references (.context h)
  | tables h => exact .tables (.context h)
  | bulk h => exact .bulk (.context h)

theorem wrapStep (context : MachineContext) (h : ConfigStep c next) :
    ConfigStep (context.wrap c) (context.wrap next) := by
  cases context with
  | mk kind operands rest =>
    cases kind with
    | label n continuation =>
      cases h with
      | vectors h => exact .vectors (.context (.label h))
      | arrays h => exact .arrays (.context (.label h))
      | structures h => exact .structures (.context (.label h))
      | exceptions h => exact .exceptions (.context (.label h))
      | pure h => exact .pure (.context (.label h))
      | locals h => exact .locals (.context (.label h))
      | call h => exact .call (.context (.label h))
      | globals h => exact .globals (.context (.label h))
      | memory h => exact .memory (.context (.label h))
      | references h => exact .references (.context (.label h))
      | tables h => exact .tables (.context (.label h))
      | bulk h => exact .bulk (.context (.label h))
    | handler catches =>
      cases h with
      | vectors h => exact .vectors (.context (.handler h))
      | arrays h => exact .arrays (.context (.handler h))
      | structures h => exact .structures (.context (.handler h))
      | exceptions h => exact .exceptions (.context (.handler h))
      | pure h => exact .pure (.context (.handler h))
      | locals h => exact .locals (.context (.handler h))
      | call h => exact .call (.context (.handler h))
      | globals h => exact .globals (.context (.handler h))
      | memory h => exact .memory (.context (.handler h))
      | references h => exact .references (.context (.handler h))
      | tables h => exact .tables (.context (.handler h))
      | bulk h => exact .bulk (.context (.handler h))
    | call n caller =>
      cases h with
      | vectors h => exact .vectors (.context (.frame h))
      | arrays h => exact .arrays (.context (.frame h))
      | structures h => exact .structures (.context (.frame h))
      | exceptions h => exact .exceptions (.context (.frame h))
      | pure h => exact .pure (.context (.frame h))
      | locals h => exact .locals (.context (.frame h))
      | call h => exact .call (.context (.frame h))
      | globals h => exact .globals (.context (.frame h))
      | memory h => exact .memory (.context (.frame h))
      | references h => exact .references (.context (.frame h))
      | tables h => exact .tables (.context (.frame h))
      | bulk h => exact .bulk (.context (.frame h))

theorem plugStep (contexts : List MachineContext) (h : ConfigStep c next) :
    ConfigStep (plug contexts c) (plug contexts next) := by
  induction contexts generalizing c next with
  | nil => exact h
  | cons context rest ih => exact ih (wrapStep context h)

private def checkedBookkeeping (m : Machine) :
    Option {next : Machine // next.toConfiguration = m.toConfiguration ∧
      sizeOf next.code < sizeOf m.code} := by
  match hc : m.code with
  | .instr (.const value) :: tail =>
    exact some ⟨{m with operands := value :: m.operands, code := tail}, by
      constructor
      · simp [toConfiguration, active, hc, values, List.map_append, List.append_assoc]
      · simp; omega⟩
  | .label n continuation body :: tail =>
    exact some ⟨{m with
      operands := [], code := body
      contexts := ⟨.label n continuation, m.operands, tail⟩ :: m.contexts}, by
      constructor
      · simp [toConfiguration, active, plug, MachineContext.wrap, hc, values]
      · simp; omega⟩
  | .handler catches body :: tail =>
    exact some ⟨{m with
      operands := [], code := body
      contexts := ⟨.handler catches, m.operands, tail⟩ :: m.contexts}, by
      constructor
      · simp [toConfiguration, active, plug, MachineContext.wrap, hc, values]
      · simp; omega⟩
  | .frame n inner body :: tail =>
    exact some ⟨{m with
      frame := inner, operands := [], code := body
      contexts := ⟨.call n m.frame, m.operands, tail⟩ :: m.contexts}, by
      constructor
      · simp [toConfiguration, active, plug, MachineContext.wrap, hc, values]
      · simp; omega⟩
  | _ => exact none

def normalize (m : Machine) : Machine :=
  match checkedBookkeeping m with
  | none => m
  | some next => normalize next.val
termination_by sizeOf m.code
decreasing_by exact next.property.2

theorem normalize_same (m : Machine) : (normalize m).toConfiguration = m.toConfiguration := by
  rw [normalize]
  split
  · rfl
  · rename_i next he
    exact (normalize_same _).trans next.property.1
termination_by sizeOf m.code
decreasing_by
  rename_i next _ _
  exact next.property.2

end Machine
end Wasm.Execution
