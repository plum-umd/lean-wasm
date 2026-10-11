import Wasm.Fast.Runtime

namespace Wasm.Fast


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
      CallStep store state (values args ++
        [.instr (.const (.ref (.func address))), .returnInvokeRef ft])
        [.tailActivation [activation]]
  | returnInvoke (hf : store.func? address = some function) (ht : function.type = type)
      (ha : Invokes store function args activation) :
      CallStep store state (values args ++ [.returnInvoke address type])
        [.tailActivation [activation]]
  | returnTypedNull : CallStep store state
      [.instr (.const (.ref (.null heap))), .returnInvokeDefined type] [.trap]
  | returnTypedInvoke (hf : store.func? address = some function)
      (ht : Types.HeapMatches {} function.runtimeType.heap type.heap)
      (he : type.expand? = some signature) (ha : Invokes store function args activation) :
      CallStep store state (values args ++
        [.instr (.const (.ref (.func address))), .returnInvokeDefined type])
        [.tailActivation [activation]]
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

abbrev CheckedCallStep (store : Store) (state : Frame) (es : List AdminInstr) :=
  Option { next : List AdminInstr // CallStep store state es next }

private def callContext (vs : List Value) (tail : List AdminInstr)
    (s : CheckedCallStep store state es) :
    CheckedCallStep store state (values vs ++ es ++ tail) :=
  s.map fun next => ⟨values vs ++ next.val ++ tail, .context next.property⟩

private def pendingTail (es : List AdminInstr) :
    Option { p : List Value × List AdminInstr × List AdminInstr //
      es = values p.1 ++ [.tailActivation p.2.1] ++ p.2.2 } := by
  match es with
  | .tailActivation body :: tail => exact some ⟨([], body, tail), rfl⟩
  | .instr (.const v) :: tail =>
    exact (pendingTail tail).map fun p => ⟨(v :: p.val.1, p.val.2), by
      simpa [values] using congrArg (.instr (.const v) :: ·) p.property⟩
  | _ => exact none

private def scanCalls (store : Store) (state : Frame) (es : List AdminInstr)
    (stack : List Value) : CheckedCallStep store state (values stack ++ es) := by
  match es with
  | .instr (.const v) :: tail =>
    simpa [values, List.map_append, List.append_assoc] using
      scanCalls store state tail (stack ++ [v])
  | .instr (.call x) :: tail =>
    match ha : state.module.funcAddr? x with
    | none => exact none
    | some address =>
      match hf : store.func? address with
      | none => exact none
      | some function =>
        simpa using callContext stack tail
          (some ⟨[.invoke address function.type], CallStep.call ha hf⟩)
  | .instr (.callRef x) :: tail =>
    match ht : state.module.definedTypes[x]? with
    | none => exact none
    | some type =>
      simpa using callContext stack tail (some ⟨_, CallStep.callRef ht⟩)
  | .instr (.callIndirect x y) :: tail =>
    match defined : state.module.definedTypes[y]? with
    | some type =>
      simpa using callContext stack tail (some ⟨_, CallStep.indirectTyped defined⟩)
    | none =>
    match ht : state.module.types.func? (y) with
    | none => exact none
    | some ft =>
      simpa using callContext stack tail
        (some ⟨_, CallStep.indirect ht⟩)
  | .instr (.returnCall x) :: tail =>
    match ha : state.module.funcAddr? x with
    | none => exact none
    | some address =>
      match hf : store.func? address with
      | none => exact none
      | some function =>
        simpa using callContext stack tail
          (some ⟨[.returnInvoke address function.type], CallStep.returnCall ha hf⟩)
  | .instr (.returnCallRef x) :: tail =>
    match ht : state.module.definedTypes[x]? with
    | none => exact none
    | some type =>
      simpa using callContext stack tail (some ⟨_, CallStep.returnCallRef ht⟩)
  | .instr (.returnCallIndirect x y) :: tail =>
    match defined : state.module.definedTypes[y]? with
    | some type =>
      simpa using callContext stack tail (some ⟨_, CallStep.returnIndirectTyped defined⟩)
    | none =>
    match ht : state.module.types.func? (y) with
    | none => exact none
    | some ft =>
      simpa using callContext stack tail
        (some ⟨_, CallStep.returnIndirect ht⟩)
  | .invokeRef ft :: tail =>
    match hs : stack.reverse with
    | .ref (.null heap) :: rest =>
      have he : stack = rest.reverse ++ [.ref (.null heap)] := by
        have he := congrArg List.reverse hs
        simpa using he
      simpa [he, values, List.map_append, List.append_assoc] using callContext rest.reverse tail
        (some ⟨_, CallStep.refNull⟩)
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
            match ha : FuncInst.activation? function args store with
            | none => exact none
            | some activation =>
              have he : stack = operands ++ [.ref (.func address)] := by
                have he := congrArg List.reverse hs
                simpa using he
              have hp : operands = below ++ args := (List.take_append_drop _ _).symm
              simpa [he, hp, values, List.map_append, List.append_assoc] using
                callContext below tail
                (some ⟨_, CallStep.refInvoke hf ht.down (FuncInst.activation?_sound ha)⟩)
          else exact none
        | none => exact none
    | _ => exact none
  | .invokeDefined type :: tail =>
    match hs : stack.reverse with
    | .ref (.null heap) :: rest =>
      have he : stack = rest.reverse ++ [.ref (.null heap)] := by
        have := congrArg List.reverse hs
        simpa using this
      simpa [he, values, List.map_append, List.append_assoc] using callContext rest.reverse tail
        (some ⟨_, CallStep.typedNull⟩)
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
            match ha : FuncInst.activation? function args store with
            | none => exact none
            | some activation =>
              have hv : stack = operands ++ [.ref (.func address)] := by
                have := congrArg List.reverse hs
                simpa using this
              have hp : operands = below ++ args := (List.take_append_drop _ _).symm
              simpa [hv, hp, values, List.map_append, List.append_assoc] using
                callContext below tail
                (some ⟨_, CallStep.typedInvoke hf matched.down he (FuncInst.activation?_sound ha)⟩)
          else exact none
      | _, _ => exact none
    | _ => exact none
  | .invoke address type :: tail =>
    match hf : store.func? address with
    | none => exact none
    | some function =>
      if ht : function.type = type then
        let n := function.type.params.length
        if hn : n ≤ stack.length then
          let below := stack.take (stack.length - n)
          let args := stack.drop (stack.length - n)
          match ha : FuncInst.activation? function args store with
          | none => exact none
          | some activation =>
            have hs : stack = below ++ args := (List.take_append_drop _ _).symm
            simpa [hs, values, List.map_append, List.append_assoc] using
              callContext below tail
                (some ⟨[activation], CallStep.invoke hf ht (FuncInst.activation?_sound ha)⟩)
        else exact none
      else exact none
  | .returnInvokeRef ft :: tail =>
    match hs : stack.reverse with
    | .ref (.null heap) :: rest =>
      have he : stack = rest.reverse ++ [.ref (.null heap)] := by
        have he := congrArg List.reverse hs
        simpa using he
      simpa [he, values, List.map_append, List.append_assoc] using callContext rest.reverse tail
        (some ⟨_, CallStep.returnRefNull⟩)
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
            match ha : FuncInst.activation? function args store with
            | none => exact none
            | some activation =>
              have he : stack = operands ++ [.ref (.func address)] := by
                have he := congrArg List.reverse hs
                simpa using he
              have hp : operands = below ++ args := (List.take_append_drop _ _).symm
              simpa [he, hp, values, List.map_append, List.append_assoc] using
                callContext below tail
                (some ⟨_, CallStep.returnRefInvoke hf ht.down (FuncInst.activation?_sound ha)⟩)
          else exact none
        | none => exact none
    | _ => exact none
  | .returnInvokeDefined type :: tail =>
    match hs : stack.reverse with
    | .ref (.null heap) :: rest =>
      have he : stack = rest.reverse ++ [.ref (.null heap)] := by
        have := congrArg List.reverse hs
        simpa using this
      simpa [he, values, List.map_append, List.append_assoc] using callContext rest.reverse tail
        (some ⟨_, CallStep.returnTypedNull⟩)
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
            match ha : FuncInst.activation? function args store with
            | none => exact none
            | some activation =>
              have hv : stack = operands ++ [.ref (.func address)] := by
                have := congrArg List.reverse hs
                simpa using this
              have hp : operands = below ++ args := (List.take_append_drop _ _).symm
              simpa [hv, hp, values, List.map_append, List.append_assoc] using
                callContext below tail
                (some ⟨_, CallStep.returnTypedInvoke hf matched.down he
                  (FuncInst.activation?_sound ha)⟩)
          else exact none
      | _, _ => exact none
    | _ => exact none
  | .returnInvoke address type :: tail =>
    match hf : store.func? address with
    | none => exact none
    | some function =>
      if ht : function.type = type then
        let n := function.type.params.length
        if hn : n ≤ stack.length then
          let below := stack.take (stack.length - n)
          let args := stack.drop (stack.length - n)
          match ha : FuncInst.activation? function args store with
          | none => exact none
          | some activation =>
            have hs : stack = below ++ args := (List.take_append_drop _ _).symm
            simpa [hs, values, List.map_append, List.append_assoc] using
              callContext below tail
                (some ⟨[.tailActivation [activation]],
                  CallStep.returnInvoke hf ht (FuncInst.activation?_sound ha)⟩)
        else exact none
      else exact none
  | .label n continuation body :: tail =>
    let inner : CheckedCallStep store state [.label n continuation body] :=
      match pendingTail body with
      | some p => some ⟨[.tailActivation p.val.2.1], by
          simpa [p.property] using (CallStep.tailLabel (store := store) (state := state)
            (n := n) (continuation := continuation)
            (discarded := p.val.1) (body := p.val.2.1) (tail := p.val.2.2))⟩
      | none => (scanCalls store state body []).map fun next =>
        ⟨[.label n continuation next.val], .label (by simpa [values] using next.property)⟩
    simpa using callContext stack tail inner
  | .handler catches body :: tail =>
    let inner : CheckedCallStep store state [.handler catches body] :=
      match pendingTail body with
      | some p => some ⟨[.tailActivation p.val.2.1], by
          simpa [p.property] using (CallStep.tailHandler (store := store) (state := state)
            (catches := catches)
            (discarded := p.val.1) (body := p.val.2.1) (tail := p.val.2.2))⟩
      | none => (scanCalls store state body []).map fun next =>
        ⟨[.handler catches next.val], .handler (by simpa [values] using next.property)⟩
    simpa using callContext stack tail inner
  | .frame n frame body :: tail =>
    let inner : CheckedCallStep store state [.frame n frame body] :=
      match pendingTail body with
      | some p => some ⟨p.val.2.1, by
          simpa [p.property] using (CallStep.tailFrame (store := store) (state := state)
            (n := n) (inner := frame)
            (discarded := p.val.1) (body := p.val.2.1) (tail := p.val.2.2))⟩
      | none => (scanCalls store frame body []).map fun next =>
        ⟨[.frame n frame next.val], .frame (by simpa [values] using next.property)⟩
    simpa using callContext stack tail inner
  | _ => exact none
termination_by sizeOf es
decreasing_by all_goals simp_wf; omega

def stepCalls (store : Store) (state : Frame) (es : List AdminInstr) :
    Option (List AdminInstr) :=
  (scanCalls store state es []).map Subtype.val

theorem stepCalls_sound (h : stepCalls store state es = some next) :
    CallStep store state es next := by
  unfold stepCalls at h
  cases hs : scanCalls store state es [] with
  | none => simp [hs] at h
  | some s =>
    simp [hs] at h
    subst next
    simpa [values] using s.property

end Wasm.Fast
