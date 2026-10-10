import Wasm.Runtime

namespace Wasm

/-! Direct/indirect-call resolution and invocation for the supported runtime projection.
`invoke` retains the non-null reference address and closed signature used by `call_ref`.
https://webassembly.github.io/spec/core/exec/instructions.html#control-instructions
-/
inductive CallStep (store : Store) : Frame → List AdminInstr → List AdminInstr → Prop where
  | call (ha : state.module.funcAddr? x = some address)
      (hf : store.func? address = some function) :
      CallStep store state [.instr (.call x)] [.invoke address function.type]
  | indirect (ht : state.module.types[y]? = some ft) :
      CallStep store state [.instr (.callIndirect x y)]
        [.instr (.tableGet x), .castFunc ft, .invokeRef ft]
  | indirectTyped (ht : state.module.definedTypes[y]? = some type) :
      CallStep store state [.instr (.callIndirect x y)]
        [.instr (.tableGet x), .castDefined type, .invokeDefined type]
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
  | context : CallStep store state es es' →
      CallStep store state (values vs ++ es ++ tail) (values vs ++ es' ++ tail)
  | label : CallStep store state body body' →
      CallStep store state [.label n continuation body] [.label n continuation body']
  | frame : CallStep store inner body body' →
      CallStep store state [.frame n inner body] [.frame n inner body']

abbrev CheckedCallStep (store : Store) (state : Frame) (es : List AdminInstr) :=
  Option { next : List AdminInstr // CallStep store state es next }

private def callContext (vs : List Value) (tail : List AdminInstr)
    (s : CheckedCallStep store state es) :
    CheckedCallStep store state (values vs ++ es ++ tail) :=
  s.map fun next => ⟨values vs ++ next.val ++ tail, .context next.property⟩

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
  | .instr (.callIndirect x y) :: tail =>
    match defined : state.module.definedTypes[y]? with
    | some type =>
      simpa using callContext stack tail (some ⟨_, CallStep.indirectTyped defined⟩)
    | none =>
    match ht : state.module.types[y]? with
    | none => exact none
    | some ft =>
      simpa using callContext stack tail
        (some ⟨_, CallStep.indirect ht⟩)
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
            match ha : function.activation? args store with
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
            match ha : function.activation? args store with
            | none => exact none
            | some activation =>
              have hv : stack = operands ++ [.ref (.func address)] := by
                have := congrArg List.reverse hs
                simpa using this
              have hp : operands = below ++ args := (List.take_append_drop _ _).symm
              simpa [hv, hp, values, List.map_append, List.append_assoc] using callContext below tail
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
          match ha : function.activation? args store with
          | none => exact none
          | some activation =>
            have hs : stack = below ++ args := (List.take_append_drop _ _).symm
            simpa [hs, values, List.map_append, List.append_assoc] using
              callContext below tail
                (some ⟨[activation], CallStep.invoke hf ht (FuncInst.activation?_sound ha)⟩)
        else exact none
      else exact none
  | .label n continuation body :: tail =>
    let inner : CheckedCallStep store state [.label n continuation body] :=
      (scanCalls store state body []).map fun next =>
        ⟨[.label n continuation next.val], .label (by simpa [values] using next.property)⟩
    simpa using callContext stack tail inner
  | .frame n frame body :: tail =>
    let inner : CheckedCallStep store state [.frame n frame body] :=
      (scanCalls store frame body []).map fun next =>
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

end Wasm
