import Wasm.RuntimeCallCompleteness
import Wasm.ContextualScanner

namespace Wasm

/-! Direct/indirect-call resolution and invocation for the supported runtime projection.
`invoke` retains the non-null reference address and closed signature used by `call_ref`.
https://webassembly.github.io/spec/core/exec/instructions.html#control-instructions
-/
inductive CallStep (store : Store) : Frame → List AdminInstr → List AdminInstr → Prop where
  | call (ha : state.module.funcAddr? x = some address)
      (hf : store.func? address = some function) :
      CallStep store state [.instr (.call x)] [.invoke address function.type]
  | callRef (ht : state.module.definedTypes[x]? = some type) :
      CallStep store state [.instr (.callRef x)] [.invokeDefined type]
  | indirect (ht : state.module.types.func? (y) = some ft) :
      CallStep store state [.instr (.callIndirect x y)]
        [.instr (.tableGet x), .castFunc ft, .invokeRef ft]
  | indirectTyped (ht : state.module.definedTypes[y]? = some type) :
      CallStep store state [.instr (.callIndirect x y)]
        [.instr (.tableGet x), .castDefined type, .invokeDefined type]
  | returnCall (ha : state.module.funcAddr? x = some address)
      (hf : store.func? address = some function) :
      CallStep store state [.instr (.returnCall x)] [.returnInvoke address function.type]
  | returnCallRef (ht : state.module.definedTypes[x]? = some type) :
      CallStep store state [.instr (.returnCallRef x)] [.returnInvokeDefined type]
  | returnIndirect (ht : state.module.types.func? (y) = some ft) :
      CallStep store state [.instr (.returnCallIndirect x y)]
        [.instr (.tableGet x), .castFunc ft, .returnInvokeRef ft]
  | returnIndirectTyped (ht : state.module.definedTypes[y]? = some type) :
      CallStep store state [.instr (.returnCallIndirect x y)]
        [.instr (.tableGet x), .castDefined type, .returnInvokeDefined type]
  | refNull : CallStep store state
      [ .instr (.const (.ref (.null heap))), .invokeRef ft ] [.trap]
  | refInvoke (hf : store.func? address = some function)
      (ht : Types.HeapMatches {} function.runtimeType.heap ft.definedType.heap)
      (ha : Invokes store function args activation) :
      CallStep store state (values args ++ [.instr (.const (.ref (.func address))), .invokeRef ft])
        [activation]
  | invoke (hf : store.func? address = some function) (ht : function.type = type)
      (ha : Invokes store function args activation) :
      CallStep store state (values args ++ [.invoke address type]) [activation]
  | typedNull : CallStep store state
      [.instr (.const (.ref (.null heap))), .invokeDefined type] [.trap]
  | typedInvoke (hf : store.func? address = some function)
      (ht : Types.HeapMatches {} function.runtimeType.heap type.heap)
      (he : type.expand? = some signature) (ha : Invokes store function args activation) :
      CallStep store state (values args ++
        [.instr (.const (.ref (.func address))), .invokeDefined type]) [activation]
  | returnRefNull : CallStep store state
      [ .instr (.const (.ref (.null heap))), .returnInvokeRef ft ] [.trap]
  | returnRefInvoke (hf : store.func? address = some function)
      (ht : Types.HeapMatches {} function.runtimeType.heap ft.definedType.heap)
      (ha : Invokes store function args activation) :
      CallStep store state (values args ++ [.instr (.const (.ref (.func address))), .returnInvokeRef ft])
        [.tailActivation [activation]]
  | returnInvoke (hf : store.func? address = some function) (ht : function.type = type)
      (ha : Invokes store function args activation) :
      CallStep store state (values args ++ [.returnInvoke address type]) [.tailActivation [activation]]
  | returnTypedNull : CallStep store state
      [.instr (.const (.ref (.null heap))), .returnInvokeDefined type] [.trap]
  | returnTypedInvoke (hf : store.func? address = some function)
      (ht : Types.HeapMatches {} function.runtimeType.heap type.heap)
      (he : type.expand? = some signature) (ha : Invokes store function args activation) :
      CallStep store state (values args ++
        [.instr (.const (.ref (.func address))), .returnInvokeDefined type]) [.tailActivation [activation]]
  | tailLabel : CallStep store state
      [.label n continuation (values discarded ++ [.tailActivation body] ++ tail)]
      [.tailActivation body]
  | tailHandler : CallStep store state
      [.handler catches (values discarded ++ [.tailActivation body] ++ tail)]
      [.tailActivation body]
  | tailFrame : CallStep store state
      [.frame n inner (values discarded ++ [.tailActivation body] ++ tail)] body
  | context : CallStep store state es es' →
      CallStep store state (values vs ++ es ++ tail) (values vs ++ es' ++ tail)
  | label : CallStep store state body body' →
      CallStep store state [.label n continuation body] [.label n continuation body']
  | handler : CallStep store state body body' →
      CallStep store state [.handler catches body] [.handler catches body']
  | frame : CallStep store inner body body' →
      CallStep store state [.frame n inner body] [.frame n inner body']

private inductive CallRoot (store : Store) : Frame → List AdminInstr → List AdminInstr → Prop where
  | call (ha : state.module.funcAddr? x = some address)
      (hf : store.func? address = some function) :
      CallRoot store state [.instr (.call x)] [.invoke address function.type]
  | callRef (ht : state.module.definedTypes[x]? = some type) :
      CallRoot store state [.instr (.callRef x)] [.invokeDefined type]
  | indirect (ht : state.module.types.func? (y) = some ft) :
      CallRoot store state [.instr (.callIndirect x y)]
        [.instr (.tableGet x), .castFunc ft, .invokeRef ft]
  | indirectTyped (ht : state.module.definedTypes[y]? = some type) :
      CallRoot store state [.instr (.callIndirect x y)]
        [.instr (.tableGet x), .castDefined type, .invokeDefined type]
  | returnCall (ha : state.module.funcAddr? x = some address)
      (hf : store.func? address = some function) :
      CallRoot store state [.instr (.returnCall x)] [.returnInvoke address function.type]
  | returnCallRef (ht : state.module.definedTypes[x]? = some type) :
      CallRoot store state [.instr (.returnCallRef x)] [.returnInvokeDefined type]
  | returnIndirect (ht : state.module.types.func? (y) = some ft) :
      CallRoot store state [.instr (.returnCallIndirect x y)]
        [.instr (.tableGet x), .castFunc ft, .returnInvokeRef ft]
  | returnIndirectTyped (ht : state.module.definedTypes[y]? = some type) :
      CallRoot store state [.instr (.returnCallIndirect x y)]
        [.instr (.tableGet x), .castDefined type, .returnInvokeDefined type]
  | refNull : CallRoot store state
      [ .instr (.const (.ref (.null heap))), .invokeRef ft ] [.trap]
  | refInvoke (hf : store.func? address = some function)
      (ht : Types.HeapMatches {} function.runtimeType.heap ft.definedType.heap)
      (ha : Invokes store function args activation) :
      CallRoot store state (values args ++ [.instr (.const (.ref (.func address))), .invokeRef ft])
        [activation]
  | invoke (hf : store.func? address = some function) (ht : function.type = type)
      (ha : Invokes store function args activation) :
      CallRoot store state (values args ++ [.invoke address type]) [activation]
  | typedNull : CallRoot store state
      [.instr (.const (.ref (.null heap))), .invokeDefined type] [.trap]
  | typedInvoke (hf : store.func? address = some function)
      (ht : Types.HeapMatches {} function.runtimeType.heap type.heap)
      (he : type.expand? = some signature) (ha : Invokes store function args activation) :
      CallRoot store state (values args ++
        [.instr (.const (.ref (.func address))), .invokeDefined type]) [activation]
  | returnRefNull : CallRoot store state
      [ .instr (.const (.ref (.null heap))), .returnInvokeRef ft ] [.trap]
  | returnRefInvoke (hf : store.func? address = some function)
      (ht : Types.HeapMatches {} function.runtimeType.heap ft.definedType.heap)
      (ha : Invokes store function args activation) :
      CallRoot store state (values args ++ [.instr (.const (.ref (.func address))), .returnInvokeRef ft])
        [.tailActivation [activation]]
  | returnInvoke (hf : store.func? address = some function) (ht : function.type = type)
      (ha : Invokes store function args activation) :
      CallRoot store state (values args ++ [.returnInvoke address type]) [.tailActivation [activation]]
  | returnTypedNull : CallRoot store state
      [.instr (.const (.ref (.null heap))), .returnInvokeDefined type] [.trap]
  | returnTypedInvoke (hf : store.func? address = some function)
      (ht : Types.HeapMatches {} function.runtimeType.heap type.heap)
      (he : type.expand? = some signature) (ha : Invokes store function args activation) :
      CallRoot store state (values args ++
        [.instr (.const (.ref (.func address))), .returnInvokeDefined type]) [.tailActivation [activation]]
  | tailLabel : CallRoot store state
      [.label n continuation (values discarded ++ [.tailActivation body] ++ tail)]
      [.tailActivation body]
  | tailHandler : CallRoot store state
      [.handler catches (values discarded ++ [.tailActivation body] ++ tail)]
      [.tailActivation body]
  | tailFrame : CallRoot store state
      [.frame n inner (values discarded ++ [.tailActivation body] ++ tail)] body

abbrev CheckedCallStep (store : Store) (state : Frame) (es : List AdminInstr) :=
  Option { next : List AdminInstr // CallStep store state es next }

private def callContext (vs : List Value) (tail : List AdminInstr)
    (s : CheckedCallStep store state es) :
    CheckedCallStep store state (values vs ++ es ++ tail) :=
  s.map fun next => ⟨values vs ++ next.val ++ tail, .context next.property⟩

private def pendingTail : List AdminInstr → Option (List Value × List AdminInstr × List AdminInstr)
  | .tailActivation body :: tail => some ([], body, tail)
  | .instr (.const value) :: tail => (pendingTail tail).map fun p => (value :: p.1, p.2)
  | _ => none

private theorem pendingTail_sound (found : pendingTail code = some p) :
    code = values p.1 ++ [.tailActivation p.2.1] ++ p.2.2 := by
  cases code with
  | nil => simp [pendingTail] at found
  | cons op tail =>
    cases op with
    | tailActivation body => simp [pendingTail] at found; cases found; rfl
    | instr instr =>
      cases instr with
      | const value =>
        obtain ⟨next, checked, same⟩ := Option.map_eq_some_iff.mp found
        cases same
        simpa [values] using congrArg (.instr (.const value) :: ·) (pendingTail_sound checked)
      | _ => simp [pendingTail] at found
    | _ => simp [pendingTail] at found
termination_by sizeOf code

private def checkedCallLeaf (store : Store) (state : Frame) (op : AdminInstr)
    (stack : List Value) (tail : List AdminInstr) :
    CheckedCallStep store state (values stack ++ op :: tail) := by
  match op with
  | .instr (.call x) =>
    match ha : state.module.funcAddr? x with
    | none => exact none
    | some address =>
      match hf : store.func? address with
      | none => exact none
      | some function =>
        exact (callContext stack tail (some ⟨[.invoke address function.type], CallStep.call ha hf⟩)).map fun next =>
          ⟨next.val, by simpa  using next.property⟩
  | .instr (.callRef x) =>
    match ht : state.module.definedTypes[x]? with
    | none => exact none
    | some type =>
      exact (callContext stack tail (some ⟨_, CallStep.callRef ht⟩)).map fun next =>
        ⟨next.val, by simpa  using next.property⟩
  | .instr (.callIndirect x y) =>
    match defined : state.module.definedTypes[y]? with
    | some type =>
      exact (callContext stack tail (some ⟨_, CallStep.indirectTyped defined⟩)).map fun next =>
        ⟨next.val, by simpa  using next.property⟩
    | none =>
    match ht : state.module.types.func? (y) with
    | none => exact none
    | some ft =>
      exact (callContext stack tail (some ⟨_, CallStep.indirect ht⟩)).map fun next =>
        ⟨next.val, by simpa  using next.property⟩
  | .instr (.returnCall x) =>
    match ha : state.module.funcAddr? x with
    | none => exact none
    | some address =>
      match hf : store.func? address with
      | none => exact none
      | some function =>
        exact (callContext stack tail (some ⟨[.returnInvoke address function.type], CallStep.returnCall ha hf⟩)).map fun next =>
          ⟨next.val, by simpa  using next.property⟩
  | .instr (.returnCallRef x) =>
    match ht : state.module.definedTypes[x]? with
    | none => exact none
    | some type =>
      exact (callContext stack tail (some ⟨_, CallStep.returnCallRef ht⟩)).map fun next =>
        ⟨next.val, by simpa  using next.property⟩
  | .instr (.returnCallIndirect x y) =>
    match defined : state.module.definedTypes[y]? with
    | some type =>
      exact (callContext stack tail (some ⟨_, CallStep.returnIndirectTyped defined⟩)).map fun next =>
        ⟨next.val, by simpa  using next.property⟩
    | none =>
    match ht : state.module.types.func? (y) with
    | none => exact none
    | some ft =>
      exact (callContext stack tail (some ⟨_, CallStep.returnIndirect ht⟩)).map fun next =>
        ⟨next.val, by simpa  using next.property⟩
  | .invokeRef ft =>
    match hs : stack.reverse with
    | .ref (.null heap) :: rest =>
      have he : stack = rest.reverse ++ [.ref (.null heap)] := by
        have he := congrArg List.reverse hs
        simpa using he
      exact (callContext rest.reverse tail (some ⟨_, CallStep.refNull⟩)).map fun next =>
        ⟨next.val, by simpa [he, values, List.map_append, List.append_assoc] using next.property⟩
    | .ref (.func address) :: rest =>
      match hf : store.func? address with
      | none => exact none
      | some function =>
        match checkRuntimeHeap function.runtimeType.heap ft.definedType.heap with
        | some ht =>
          let operands := rest.reverse
          let n := ft.params.length
          if hn : n ≤ operands.length then
            let below := operands.take (operands.length - n)
            let args := operands.drop (operands.length - n)
            match ha : function.activation? args store with
            | none => exact none
            | some activation =>
              have he : stack = operands ++ [.ref (.func address)] := by
                have he := congrArg List.reverse hs
                simpa using he
              have hp : operands = below ++ args := (List.take_append_drop _ _).symm
              exact (callContext below tail (some ⟨_, CallStep.refInvoke hf ht.down (FuncInst.activation?_sound ha)⟩)).map fun next =>
                ⟨next.val, by simpa [he, hp, values, List.map_append, List.append_assoc] using next.property⟩
          else exact none
        | none => exact none
    | _ => exact none
  | .invokeDefined type =>
    match hs : stack.reverse with
    | .ref (.null heap) :: rest =>
      have he : stack = rest.reverse ++ [.ref (.null heap)] := by
        have := congrArg List.reverse hs
        simpa using this
      exact (callContext rest.reverse tail (some ⟨_, CallStep.typedNull⟩)).map fun next =>
        ⟨next.val, by simpa [he, values, List.map_append, List.append_assoc] using next.property⟩
    | .ref (.func address) :: rest =>
      match hf : store.func? address, he : type.expand? with
      | some function, some signature =>
        match checkRuntimeHeap function.runtimeType.heap type.heap with
        | none => exact none
        | some matched =>
          let operands := rest.reverse
          let n := signature.params.length
          if hn : n ≤ operands.length then
            let below := operands.take (operands.length - n)
            let args := operands.drop (operands.length - n)
            match ha : function.activation? args store with
            | none => exact none
            | some activation =>
              have hv : stack = operands ++ [.ref (.func address)] := by
                have := congrArg List.reverse hs
                simpa using this
              have hp : operands = below ++ args := (List.take_append_drop _ _).symm
              exact (callContext below tail (some ⟨_, CallStep.typedInvoke hf matched.down he (FuncInst.activation?_sound ha)⟩)).map fun next =>
                ⟨next.val, by simpa [hv, hp, values, List.map_append, List.append_assoc] using next.property⟩
          else exact none
      | _, _ => exact none
    | _ => exact none
  | .invoke address type =>
    match hf : store.func? address with
    | none => exact none
    | some function =>
      if ht : function.type = type then
        let n := function.type.params.length
        if hn : n ≤ stack.length then
          let below := stack.take (stack.length - n)
          let args := stack.drop (stack.length - n)
          match ha : function.activation? args store with
          | none => exact none
          | some activation =>
            have hs : stack = below ++ args := (List.take_append_drop _ _).symm
            exact (callContext below tail (some ⟨[activation], CallStep.invoke hf ht (FuncInst.activation?_sound ha)⟩)).map fun next =>
              ⟨next.val, by simpa [hs, values, List.map_append, List.append_assoc] using next.property⟩
        else exact none
      else exact none
  | .returnInvokeRef ft =>
    match hs : stack.reverse with
    | .ref (.null heap) :: rest =>
      have he : stack = rest.reverse ++ [.ref (.null heap)] := by
        have he := congrArg List.reverse hs
        simpa using he
      exact (callContext rest.reverse tail (some ⟨_, CallStep.returnRefNull⟩)).map fun next =>
        ⟨next.val, by simpa [he, values, List.map_append, List.append_assoc] using next.property⟩
    | .ref (.func address) :: rest =>
      match hf : store.func? address with
      | none => exact none
      | some function =>
        match checkRuntimeHeap function.runtimeType.heap ft.definedType.heap with
        | some ht =>
          let operands := rest.reverse
          let n := ft.params.length
          if hn : n ≤ operands.length then
            let below := operands.take (operands.length - n)
            let args := operands.drop (operands.length - n)
            match ha : function.activation? args store with
            | none => exact none
            | some activation =>
              have he : stack = operands ++ [.ref (.func address)] := by
                have he := congrArg List.reverse hs
                simpa using he
              have hp : operands = below ++ args := (List.take_append_drop _ _).symm
              exact (callContext below tail (some ⟨_, CallStep.returnRefInvoke hf ht.down (FuncInst.activation?_sound ha)⟩)).map fun next =>
                ⟨next.val, by simpa [he, hp, values, List.map_append, List.append_assoc] using next.property⟩
          else exact none
        | none => exact none
    | _ => exact none
  | .returnInvokeDefined type =>
    match hs : stack.reverse with
    | .ref (.null heap) :: rest =>
      have he : stack = rest.reverse ++ [.ref (.null heap)] := by
        have := congrArg List.reverse hs
        simpa using this
      exact (callContext rest.reverse tail (some ⟨_, CallStep.returnTypedNull⟩)).map fun next =>
        ⟨next.val, by simpa [he, values, List.map_append, List.append_assoc] using next.property⟩
    | .ref (.func address) :: rest =>
      match hf : store.func? address, he : type.expand? with
      | some function, some signature =>
        match checkRuntimeHeap function.runtimeType.heap type.heap with
        | none => exact none
        | some matched =>
          let operands := rest.reverse
          let n := signature.params.length
          if hn : n ≤ operands.length then
            let below := operands.take (operands.length - n)
            let args := operands.drop (operands.length - n)
            match ha : function.activation? args store with
            | none => exact none
            | some activation =>
              have hv : stack = operands ++ [.ref (.func address)] := by
                have := congrArg List.reverse hs
                simpa using this
              have hp : operands = below ++ args := (List.take_append_drop _ _).symm
              exact (callContext below tail (some ⟨_, CallStep.returnTypedInvoke hf matched.down he (FuncInst.activation?_sound ha)⟩)).map fun next =>
                ⟨next.val, by simpa [hv, hp, values, List.map_append, List.append_assoc] using next.property⟩
          else exact none
      | _, _ => exact none
    | _ => exact none
  | .returnInvoke address type =>
    match hf : store.func? address with
    | none => exact none
    | some function =>
      if ht : function.type = type then
        let n := function.type.params.length
        if hn : n ≤ stack.length then
          let below := stack.take (stack.length - n)
          let args := stack.drop (stack.length - n)
          match ha : function.activation? args store with
          | none => exact none
          | some activation =>
            have hs : stack = below ++ args := (List.take_append_drop _ _).symm
            exact (callContext below tail (some ⟨[.tailActivation [activation]], CallStep.returnInvoke hf ht (FuncInst.activation?_sound ha)⟩)).map fun next =>
              ⟨next.val, by simpa [hs, values, List.map_append, List.append_assoc] using next.property⟩
        else exact none
      else exact none
  | _ => exact none

private def checkedCallBoundary (store : Store) (state : Frame) (op : AdminInstr) :
    CheckedCallStep store state [op] := by
  match op with
  | .label n continuation body =>
    let inner : CheckedCallStep store state [.label n continuation body] :=
      match found : pendingTail body with
      | some p => some ⟨[.tailActivation p.2.1], by
          simpa [pendingTail_sound found] using (CallStep.tailLabel (store := store) (state := state)
            (n := n) (continuation := continuation)
            (discarded := p.1) (body := p.2.1) (tail := p.2.2))⟩
      | none => none
    exact inner
  | .handler catches body =>
    let inner : CheckedCallStep store state [.handler catches body] :=
      match found : pendingTail body with
      | some p => some ⟨[.tailActivation p.2.1], by
          simpa [pendingTail_sound found] using (CallStep.tailHandler (store := store) (state := state)
            (catches := catches)
            (discarded := p.1) (body := p.2.1) (tail := p.2.2))⟩
      | none => none
    exact inner
  | .frame n frame body =>
    let inner : CheckedCallStep store state [.frame n frame body] :=
      match found : pendingTail body with
      | some p => some ⟨p.2.1, by
          simpa [pendingTail_sound found] using (CallStep.tailFrame (store := store) (state := state)
            (n := n) (inner := frame)
            (discarded := p.1) (body := p.2.1) (tail := p.2.2))⟩
      | none => none
    exact inner
  | _ => exact none

private def callScanner : ContextualScanner where
  leaf store state op stack tail :=
    (checkedCallLeaf store state op stack tail).map fun next => (store, next.val)
  boundary store state op := (checkedCallBoundary store state op).map fun next => (store, next.val)

private def CallRelation : ContextualRedex :=
  fun store state code next code' => next = store ∧ CallStep store state code code'

private theorem ContextualStep.calls (h : ContextualStep CallRelation store state code next code') :
    next = store ∧ CallStep store state code code' := by
  induction h with
  | redex h => exact h
  | context _ ih => exact ⟨ih.1, .context ih.2⟩
  | label _ ih => exact ⟨ih.1, .label ih.2⟩
  | handler _ ih => exact ⟨ih.1, .handler ih.2⟩
  | frame _ ih => exact ⟨ih.1, .frame ih.2⟩

def stepCalls (store : Store) (state : Frame) (es : List AdminInstr) :
    Option (List AdminInstr) := (callScanner.step store state es).map Prod.snd

theorem stepCalls_sound (h : stepCalls store state es = some next) :
    CallStep store state es next := by
  obtain ⟨result, found, same⟩ := Option.map_eq_some_iff.mp h
  cases same
  have lifted := ContextualScanner.scan_sound (redex := CallRelation) (scanner := callScanner)
    (by
      intro store state op stack tail next found
      obtain ⟨checked, _, same⟩ := Option.map_eq_some_iff.mp found
      cases same
      exact .redex ⟨rfl, checked.property⟩)
    (by
      intro store state op next found
      obtain ⟨checked, _, same⟩ := Option.map_eq_some_iff.mp found
      cases same
      exact .redex ⟨rfl, checked.property⟩) found
  simpa [values] using lifted.calls.2

/-- Expected heap types of reference invocations are declaratively valid. -/
def CallExpectedTypesValid (_state : Frame) : AdminInstr → Prop
  | .invokeRef type | .returnInvokeRef type => Types.HeapValid {} type.definedType.heap
  | .invokeDefined type | .returnInvokeDefined type => Types.HeapValid {} type.heap
  | _ => True

private def CallRootRelation : ContextualRedex :=
  fun store state code next code' => next = store ∧ CallRoot store state code code'

private theorem CallStep.contextual (h : CallStep store state code code') :
    ContextualStep CallRootRelation store state code store code' := by
  induction h with
  | context _ ih => exact .context ih
  | label _ ih => exact .label ih
  | handler _ ih => exact .handler ih
  | frame _ ih => exact .frame ih
  | call ha hf => exact .redex ⟨rfl, .call ha hf⟩
  | callRef ht => exact .redex ⟨rfl, .callRef ht⟩
  | indirect ht => exact .redex ⟨rfl, .indirect ht⟩
  | indirectTyped ht => exact .redex ⟨rfl, .indirectTyped ht⟩
  | returnCall ha hf => exact .redex ⟨rfl, .returnCall ha hf⟩
  | returnCallRef ht => exact .redex ⟨rfl, .returnCallRef ht⟩
  | returnIndirect ht => exact .redex ⟨rfl, .returnIndirect ht⟩
  | returnIndirectTyped ht => exact .redex ⟨rfl, .returnIndirectTyped ht⟩
  | refNull  => exact .redex ⟨rfl, .refNull ⟩
  | refInvoke hf ht ha => exact .redex ⟨rfl, .refInvoke hf ht ha⟩
  | invoke hf ht ha => exact .redex ⟨rfl, .invoke hf ht ha⟩
  | typedNull  => exact .redex ⟨rfl, .typedNull ⟩
  | typedInvoke hf ht he ha => exact .redex ⟨rfl, .typedInvoke hf ht he ha⟩
  | returnRefNull  => exact .redex ⟨rfl, .returnRefNull ⟩
  | returnRefInvoke hf ht ha => exact .redex ⟨rfl, .returnRefInvoke hf ht ha⟩
  | returnInvoke hf ht ha => exact .redex ⟨rfl, .returnInvoke hf ht ha⟩
  | returnTypedNull  => exact .redex ⟨rfl, .returnTypedNull ⟩
  | returnTypedInvoke hf ht he ha => exact .redex ⟨rfl, .returnTypedInvoke hf ht he ha⟩
  | tailLabel  => exact .redex ⟨rfl, .tailLabel ⟩
  | tailHandler  => exact .redex ⟨rfl, .tailHandler ⟩
  | tailFrame  => exact .redex ⟨rfl, .tailFrame ⟩

private theorem pendingTail_complete (vs : List Value) :
    (pendingTail (values vs ++ [.tailActivation body] ++ tail)).isSome = true := by
  induction vs with
  | nil => rfl
  | cons value vs ih => simpa [values, pendingTail] using ih

private theorem Invokes.prepare_suffix (invoked : Invokes store function args activation)
    (valid : store.RuntimeTypesValid)
    (parameters : ∀ type ∈ function.type.params, Types.RuntimeValValid {} (Types.embedVal type))
    (arity : args.length = count) (stack : List Value) :
    function.activation? ((stack ++ args).drop ((stack ++ args).length - count)) store =
      some activation := by
  have dropped : (stack ++ args).drop ((stack ++ args).length - count) = args := by
    rw [List.length_append, ← arity, Nat.add_sub_cancel]
    simp
  rw [dropped]
  exact function.activation?_complete_runtime invoked valid parameters

private theorem call_target_ref {type : FuncType}
    (ready : CodeScopedValid CallExpectedTypesValid state
      (values args ++ [.instr (.const value), .invokeRef type])) :
    Types.HeapValid {} type.definedType.heap :=
by
  simpa only [AdminInstr.ScopedValid, CallExpectedTypesValid] using
    ready (.invokeRef type) (by simp)

private theorem call_target_returnRef {type : FuncType}
    (ready : CodeScopedValid CallExpectedTypesValid state
      (values args ++ [.instr (.const value), .returnInvokeRef type])) :
    Types.HeapValid {} type.definedType.heap :=
by
  simpa only [AdminInstr.ScopedValid, CallExpectedTypesValid] using
    ready (.returnInvokeRef type) (by simp)

private theorem call_target_defined {type : Types.DefinedType}
    (ready : CodeScopedValid CallExpectedTypesValid state
      (values args ++ [.instr (.const value), .invokeDefined type])) :
    Types.HeapValid {} type.heap :=
by
  simpa only [AdminInstr.ScopedValid, CallExpectedTypesValid] using
    ready (.invokeDefined type) (by simp)

private theorem call_target_returnDefined {type : Types.DefinedType}
    (ready : CodeScopedValid CallExpectedTypesValid state
      (values args ++ [.instr (.const value), .returnInvokeDefined type])) :
    Types.HeapValid {} type.heap :=
by
  simpa only [AdminInstr.ScopedValid, CallExpectedTypesValid] using
    ready (.returnInvokeDefined type) (by simp)

private theorem drop_reverse_suffix {args stack rest : List Value} {count : Nat}
    (same : args.reverse ++ stack.reverse = rest) (arity : args.length = count) :
    rest.reverse.drop (rest.length - count) = args := by
  subst rest
  simp [List.reverse_append, List.length_append, ← arity, List.drop_append]

set_option maxHeartbeats 2000000 in
private theorem call_local_complete (valid : store.RuntimeTypesValid)
    (parameters : store.FunctionParametersValid)
    (reduced : CallRoot store state code code')
    (ready : CodeScopedValid CallExpectedTypesValid state code)
    (stack : List Value) (tail : List AdminInstr) :
    (callScanner.scan store state (code ++ tail) stack).isSome = true := by
  cases reduced
  case' invoke hf ht ha =>
    have arity := ha.args_typed.length
    have prepared := ha.prepare_suffix valid (parameters _ (List.mem_of_getElem? hf)) arity stack
  case' returnInvoke hf ht ha =>
    have arity := ha.args_typed.length
    have prepared := ha.prepare_suffix valid (parameters _ (List.mem_of_getElem? hf)) arity stack
  case' refInvoke hf ht ha =>
    have arity := ha.legacy_arity hf valid ht
    have prepared := ha.prepare_suffix valid (parameters _ (List.mem_of_getElem? hf)) arity stack
    have matched := Types.checkHeap_complete_runtime ht (valid.function_heap hf)
      (call_target_ref ready)
    obtain ⟨_, matchedFound⟩ := Option.isSome_iff_exists.mp matched
    change checkRuntimeHeap _ _ = some _ at matchedFound
  case' returnRefInvoke hf ht ha =>
    have arity := ha.legacy_arity hf valid ht
    have prepared := ha.prepare_suffix valid (parameters _ (List.mem_of_getElem? hf)) arity stack
    have matched := Types.checkHeap_complete_runtime ht (valid.function_heap hf)
      (call_target_returnRef ready)
    obtain ⟨_, matchedFound⟩ := Option.isSome_iff_exists.mp matched
    change checkRuntimeHeap _ _ = some _ at matchedFound
  case' typedInvoke hf ht he ha =>
    have arity := ha.defined_arity hf valid ht he
    have prepared := ha.prepare_suffix valid (parameters _ (List.mem_of_getElem? hf)) arity stack
    have matched := Types.checkHeap_complete_runtime ht (valid.function_heap hf)
      (call_target_defined ready)
    obtain ⟨_, matchedFound⟩ := Option.isSome_iff_exists.mp matched
    change checkRuntimeHeap _ _ = some _ at matchedFound
  case' returnTypedInvoke hf ht he ha =>
    have arity := ha.defined_arity hf valid ht he
    have prepared := ha.prepare_suffix valid (parameters _ (List.mem_of_getElem? hf)) arity stack
    have matched := Types.checkHeap_complete_runtime ht (valid.function_heap hf)
      (call_target_returnDefined ready)
    obtain ⟨_, matchedFound⟩ := Option.isSome_iff_exists.mp matched
    change checkRuntimeHeap _ _ = some _ at matchedFound
  case' tailLabel n continuation discarded suffix body =>
    have pending := pendingTail_complete (body := body) (tail := suffix) discarded
    simp only [List.append_assoc, List.singleton_append] at pending
  case' tailHandler catches discarded suffix body =>
    have pending := pendingTail_complete (body := body) (tail := suffix) discarded
    simp only [List.append_assoc, List.singleton_append] at pending
  case' tailFrame n inner discarded suffix =>
    have pending := pendingTail_complete (body := code') (tail := suffix) discarded
    simp only [List.append_assoc, List.singleton_append] at pending
  all_goals try simp only [List.append_assoc, ContextualScanner.scan_values]
  all_goals simp only [List.singleton_append, List.cons_append, List.nil_append,
    ContextualScanner.scan, callScanner, checkedCallLeaf,
    checkedCallBoundary, Option.isSome_map, callContext]
  all_goals repeat first | simp_all | split
  all_goals subst_vars
  all_goals repeat first | simp_all | split
  all_goals subst_vars
  all_goals repeat first | simp_all | split
  all_goals repeat first | simp_all | split at *
  all_goals subst_vars
  all_goals try simp_all [List.singleton_append, List.cons_append, List.length_append,
    List.reverse_append, List.drop_append]
  all_goals repeat first | simp_all | split
  all_goals subst_vars
  all_goals first | simp_all [List.length_append, List.reverse_append, List.drop_append] | grind [drop_reverse_suffix]

/-- Calls and tail calls find a successor on valid invocation parameter and heap types. -/
theorem stepCalls_complete (reduced : CallStep store state code code')
    (valid : store.RuntimeTypesValid) (parameters : store.FunctionParametersValid)
    (targets : CodeScopedValid CallExpectedTypesValid state code) :
    (stepCalls store state code).isSome = true := by
  have success := ContextualScanner.step_complete (scanner := callScanner)
    (domain := CallExpectedTypesValid)
    (by
      intro state code next code' reduced ready stack tail
      obtain ⟨same, raw⟩ := reduced
      exact call_local_complete valid parameters raw ready stack tail)
    reduced.contextual targets
  simpa only [stepCalls, Option.isSome_map] using success

#print axioms stepCalls_complete

end Wasm
