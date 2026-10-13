import Wasm.ControlChoice

/-!
Executable stepping of the supported fragment. Each internal result carries a proof
of its `ExecStep`; proofs are erased by Lean's compiler. The public API returns plain
instruction sequences. Scanning operand values is bookkeeping, not a semantic step.
-/

namespace Wasm

open AdminInstr Instr

private abbrev CheckedStep (types : TypeContext) (es : List AdminInstr) :=
  Option { next : List AdminInstr // ExecStep types es next }

private structure ValuePrefix (es : List AdminInstr) where
  stack : List Value
  rest : List AdminInstr
  reconstruct : es = values stack ++ rest

private def splitValues : (es : List AdminInstr) → ValuePrefix es
  | instr (.const v) :: tail =>
      let p := splitValues tail
      ⟨v :: p.stack, p.rest, by simp [values, p.reconstruct]⟩
  | es => ⟨[], es, rfl⟩

private structure Operands (stack : List Value) (n : Nat) where
  below : List Value
  args : List Value
  reconstruct : stack = below ++ args
  arity : args.length = n

/-- Split off the top n operands, preserving their specification order. -/
private def operands (stack : List Value) (n : Nat) : Option (Operands stack n) :=
  if h : n ≤ stack.length then
    some ⟨stack.take (stack.length - n), stack.drop (stack.length - n),
      (List.take_append_drop _ _).symm, by simp; omega⟩
  else none

private def inContext (vs : List Value) (tail : List AdminInstr)
    (s : CheckedStep types es) : CheckedStep types (values vs ++ es ++ tail) :=
  s.map fun next => ⟨values vs ++ next.val ++ tail, .context next.property⟩

private def localStep (types : TypeContext) (es : List AdminInstr) : CheckedStep types es :=
  match h : reduce es with
  | some next => some ⟨next, .primitive (reduce_sound h)⟩
  | none =>
    match h : reduceInteger es with
    | some next => some ⟨next, .integer (reduceInteger_sound h)⟩
    | none =>
      match h : reduceControlChoice es with
      | some next => some ⟨next, .control (reduceControlChoice_sound h)⟩
      | none => none

private def fixedArity : Instr → Option Nat
  | .nop | .unreachable => some 0
  | .drop | .eqz _ | .if_ _ _ _ | .brIf _ | .brTable _ _
    | .intUnary _ _ | .intConvert _ => some 1
  | .binop _ _ | .intBinary _ _ | .intRel _ _ => some 2
  | .select _ => some 3
  | _ => none

private def focusStep (types : TypeContext) (stack : List Value) (i : Instr) :
    CheckedStep types (values stack ++ [instr i]) := by
  match i with
  | .block bt body =>
    match ht : bt.resolve types with
    | none => exact none
    | some ft =>
      match operands stack ft.params.length with
      | none => exact none
      | some p =>
        exact some ⟨values p.below ++
          [.label ft.results.length [] (values p.args ++ instructions body)], by
          simpa [p.reconstruct, values, List.map_append, List.append_assoc] using
            (ExecStep.context (vs := p.below) (tail := [])
              (.control (.block ht p.arity)))⟩
  | .loop bt body =>
    match ht : bt.resolve types with
    | none => exact none
    | some ft =>
      match operands stack ft.params.length with
      | none => exact none
      | some p =>
        exact some ⟨values p.below ++
          [.label ft.params.length [.loop bt body] (values p.args ++ instructions body)], by
          simpa [p.reconstruct, values, List.map_append, List.append_assoc] using
            (ExecStep.context (vs := p.below) (tail := [])
              (.control (.loop ht p.arity)))⟩
  | i =>
    match fixedArity i with
    | none => exact none
    | some n =>
      match operands stack n with
      | none => exact none
      | some p =>
        exact (localStep types (values p.args ++ [instr i])).map fun next =>
          ⟨values p.below ++ next.val, by
            simpa [p.reconstruct, values, List.map_append, List.append_assoc] using
              (ExecStep.context (vs := p.below) (tail := []) next.property)⟩

private def labelStep (types : TypeContext) (n : Nat) (continuation : List Instr)
    (body : List AdminInstr) (inner : CheckedStep types body) :
    CheckedStep types [.label n continuation body] := by
  let p := splitValues body
  match hr : p.rest with
  | [] =>
    exact some ⟨values p.stack, by
      simpa [p.reconstruct, hr] using
        (ExecStep.control (ControlReduces.labelDone (types := types)
          (n := n) (continuation := continuation) (vs := p.stack)))⟩
  | instr (.br 0) :: tail =>
    match operands p.stack n with
    | none => exact none
    | some args =>
      exact some ⟨values args.args ++ instructions continuation, by
        simpa [p.reconstruct, hr, args.reconstruct, values, List.map_append,
          List.append_assoc] using
          (ExecStep.control (ControlReduces.brZero (types := types)
            (discarded := args.below) (results := args.args)
            (continuation := continuation) (tail := tail) args.arity))⟩
  | instr (.br (l + 1)) :: tail =>
    exact some ⟨values p.stack ++ [instr (.br l)], by
      simpa [p.reconstruct, hr, List.append_assoc] using
        (ExecStep.control (ControlReduces.brSucc (types := types) (n := n)
          (continuation := continuation) (vs := p.stack) (l := l) (tail := tail)))⟩
  | instr .return_ :: tail =>
    exact some ⟨values p.stack ++ [instr .return_], by
      simpa [p.reconstruct, hr, List.append_assoc] using
        (ExecStep.control (ControlReduces.returnLabel (types := types)
          (n := n) (continuation := continuation) (vs := p.stack) (tail := tail)))⟩
  | _ =>
    match hb : body with
    | [.trap] => exact some ⟨[.trap], .control .labelTrap⟩
    | _ => exact inner.map fun next =>
        ⟨[.label n continuation next.val], .label (by simpa [hb] using next.property)⟩

private def pureFrameStep (types : TypeContext) (n : Nat) (state : Frame)
    (body : List AdminInstr) (inner : CheckedStep state.module.types body) :
    CheckedStep types [.frame n state body] := by
  let p := splitValues body
  match hr : p.rest with
  | [] =>
    if h : p.stack.length = n then
      exact some ⟨values p.stack, by
        simpa [p.reconstruct, hr] using
          (ExecStep.activation (types := types) (FrameReduces.done (state := state) h))⟩
    else exact none
  | instr .return_ :: tail =>
    match operands p.stack n with
    | none => exact none
    | some args =>
      exact some ⟨values args.args, by
        simpa [p.reconstruct, hr, args.reconstruct, values, List.map_append,
          List.append_assoc] using
          (ExecStep.activation (types := types) (FrameReduces.return_
            (state := state) (discarded := args.below) (results := args.args)
            (tail := tail) args.arity))⟩
  | _ =>
    match hb : body with
    | [.trap] => exact some ⟨[.trap], .activation .trap⟩
    | _ => exact inner.map fun next =>
        ⟨[.frame n state next.val], .frame (by simpa [hb] using next.property)⟩

private def frameStep (types : TypeContext) (n : Nat) (state : Frame)
    (body : List AdminInstr) (inner : CheckedStep state.module.types body) :
    CheckedStep types [.frame n state body] :=
  match checkedLocalStep state body with
  | some next => some ⟨[.frame n next.val.1 next.val.2], .localFrame next.property⟩
  | none => pureFrameStep types n state body inner

private def scan (types : TypeContext) (es : List AdminInstr) (stack : List Value) :
    CheckedStep types (values stack ++ es) := by
  match es with
  | [] => exact none
  | instr (.const v) :: tail =>
    exact (scan types tail (stack ++ [v])).map fun next =>
      ⟨next.val, by simpa [values, List.map_append, List.append_assoc] using next.property⟩
  | instr i :: tail =>
    exact (focusStep types stack i).map fun next =>
      ⟨next.val ++ tail, by simpa [values] using
        (ExecStep.context (vs := []) (tail := tail) next.property)⟩
  | .trap :: tail =>
    if h : stack.length + tail.length = 0 then exact none
    else
      exact some ⟨[.trap], by
        simpa [List.append_assoc] using
          (ExecStep.trap (types := types) (vs := stack) (tail := tail) (by
            intro he
            have hl := congrArg List.length he
            simp [values] at hl
            omega))⟩
  | .label n continuation body :: tail =>
    exact (labelStep types n continuation body (scan types body [])).map fun next =>
      ⟨values stack ++ next.val ++ tail, by
        simpa using (ExecStep.context (vs := stack) (tail := tail) next.property)⟩
  | .handler catches body :: tail =>
    let inner : CheckedStep types [.handler catches body] :=
      (scan types body []).map fun next =>
        ⟨[.handler catches next.val], .handler (by simpa [values] using next.property)⟩
    exact inner.map fun next =>
      ⟨values stack ++ next.val ++ tail, by
        simpa using (ExecStep.context (vs := stack) (tail := tail) next.property)⟩
  | .frame n state body :: tail =>
    exact (frameStep types n state body (scan state.module.types body [])).map fun next =>
      ⟨values stack ++ next.val ++ tail, by
        simpa using (ExecStep.context (vs := stack) (tail := tail) next.property)⟩
  | .invoke _ _ :: _ | .castFunc _ :: _ | .invokeRef _ :: _
  | .castDefined _ :: _ | .invokeDefined _ :: _
  | .returnInvoke _ _ :: _ | .returnInvokeRef _ :: _ | .returnInvokeDefined _ :: _
  | .tailActivation _ :: _ | .throwing _ :: _ => exact none
termination_by sizeOf es
decreasing_by all_goals simp_wf; omega

private def scanSucceeded (types : TypeContext) (code : List AdminInstr)
    (stack : List Value) : Bool := (scan types code stack).isSome

private def focusSucceeded (types : TypeContext) (stack : List Value) (instruction : Instr) :
    Bool := (focusStep types stack instruction).isSome

private theorem scan_values (vs : List Value) :
    scanSucceeded types (values vs ++ code) stack =
      scanSucceeded types code (stack ++ vs) := by
  induction vs generalizing stack with
  | nil => rw [List.append_nil]; rfl
  | cons value vs ih =>
    simp only [scanSucceeded, values, List.map_cons, List.cons_append, scan, Option.isSome_map]
    change scanSucceeded types (values vs ++ code) (stack ++ [value]) =
      scanSucceeded types code (stack ++ value :: vs)
    simpa only [List.append_assoc, List.singleton_append] using ih (stack := stack ++ [value])

private theorem scan_values_none : scanSucceeded types (values vs) stack = false := by
  have success := scan_values (types := types) (code := []) (stack := stack) vs
  rw [List.append_nil] at success
  exact success.trans (by simp only [scanSucceeded, scan, Option.isSome_none])

private theorem splitValues_values (vs : List Value) :
    (splitValues (values vs ++ code)).stack = vs ++ (splitValues code).stack ∧
      (splitValues (values vs ++ code)).rest = (splitValues code).rest := by
  induction vs with
  | nil => simp [values]
  | cons value vs ih =>
    simp only [values, List.map_cons, List.cons_append, splitValues]
    simp_all [values]

private theorem operands_complete (bound : n ≤ stack.length) :
    (operands stack n).isSome = true := by simp [operands, bound]

private theorem operands_suffix (below args : List Value) :
    ∃ proof, operands (below ++ args) args.length = some ⟨below, args, proof, rfl⟩ := by
  have bound : args.length ≤ (below ++ args).length := by simp
  simp only [operands, dif_pos bound, Option.some.injEq]
  have len : (below ++ args).length - args.length = below.length := by simp
  simp only [len, List.take_left, List.drop_left]
  exact ⟨trivial, trivial⟩

private theorem focus_fixed_complete
    (arity : fixedArity instruction = some args.length)
    (success : (localStep types (values args ++ [instr instruction])).isSome = true) :
    focusSucceeded types (stack ++ args) instruction = true := by
  obtain ⟨proof, found⟩ := operands_suffix stack args
  cases instruction <;> simp only [fixedArity] at arity
  all_goals try contradiction
  all_goals simp only [focusSucceeded, focusStep]
  all_goals simp_all only [fixedArity, Option.some.injEq]
  all_goals simpa only [Option.isSome_map] using success

private theorem scan_instr (instruction : Instr) :
    scanSucceeded types (instr instruction :: tail) stack =
      match instruction with
      | .const value => scanSucceeded types tail (stack ++ [value])
      | instruction => focusSucceeded types stack instruction := by
  cases instruction <;> simp only [scanSucceeded, scan, focusSucceeded, Option.isSome_map]

private theorem scan_fixed_complete
    (arity : fixedArity instruction = some args.length)
    (success : (localStep types (values args ++ [instr instruction])).isSome = true) :
    scanSucceeded types ((values args ++ [instr instruction]) ++ tail) stack = true := by
  rw [List.append_assoc, scan_values, List.singleton_append, scan_instr]
  cases instruction <;> simp only [fixedArity] at arity
  all_goals try contradiction
  all_goals exact focus_fixed_complete arity success

private theorem local_primitive_complete (reduced : Reduces code next) :
    (localStep types code).isSome = true := by
  have found := reduce_complete reduced
  simp only [localStep]
  split <;> simp_all

private theorem local_integer_complete (reduced : IntegerReduces code next) :
    (localStep types code).isSome = true := by
  have found := reduceInteger_complete reduced
  simp only [localStep]
  repeat first | simp_all | split

private theorem focus_primitive_complete (reduced : Reduces code next) :
    scanSucceeded types (code ++ tail) stack = true := by
  cases reduced with
  | nop => exact scan_fixed_complete (args := []) rfl (by simp [localStep, reduce, values])
  | unreachable => exact scan_fixed_complete (args := []) rfl (by simp [localStep, reduce, values])
  | drop =>
    apply scan_fixed_complete (args := [_]) rfl
    simp [localStep, reduce, values]
  | selectZero =>
    apply scan_fixed_complete (args := [_, _, .i32 0]) rfl
    simp [localStep, reduce, values]
  | selectNonzero h =>
    apply scan_fixed_complete (args := [_, _, .i32 _]) rfl
    simp [localStep, reduce, values]
  | binop h =>
    apply scan_fixed_complete (args := [_, _]) rfl
    exact local_primitive_complete (.binop h)
  | eqz h =>
    apply scan_fixed_complete (args := [_]) rfl
    exact local_primitive_complete (.eqz h)

private theorem focus_integer_complete (reduced : IntegerReduces code next) :
    scanSucceeded types (code ++ tail) stack = true := by
  cases reduced with
  | unary h =>
    exact scan_fixed_complete (args := [_]) rfl (local_integer_complete (.unary h))
  | conversion h =>
    exact scan_fixed_complete (args := [_]) rfl (local_integer_complete (.conversion h))
  | binary h =>
    exact scan_fixed_complete (args := [_, _]) rfl (local_integer_complete (.binary h))
  | rel h =>
    exact scan_fixed_complete (args := [_, _]) rfl (local_integer_complete (.rel h))

private def labelSucceeded (types : TypeContext) (n : Nat) (continuation : List Instr)
    (body : List AdminInstr) : Bool :=
  (labelStep types n continuation body (scan types body [])).isSome

private def frameSucceeded (types : TypeContext) (n : Nat) (state : Frame)
    (body : List AdminInstr) : Bool :=
  (frameStep types n state body (scan state.module.types body [])).isSome

private theorem scan_label :
    scanSucceeded types (.label n continuation body :: tail) stack =
      labelSucceeded types n continuation body := by
  simp only [scanSucceeded, scan, labelSucceeded, Option.isSome_map]

private theorem scan_frame :
    scanSucceeded types (.frame n state body :: tail) stack =
      frameSucceeded types n state body := by
  simp only [scanSucceeded, scan, frameSucceeded, Option.isSome_map]

private theorem scan_splitValues : scanSucceeded types body stack =
    scanSucceeded types (splitValues body).rest (stack ++ (splitValues body).stack) := by
  exact (congrArg (fun code => scanSucceeded types code stack)
    (splitValues body).reconstruct).trans (scan_values _)

private theorem scan_branch_none : scanSucceeded types (instr (.br n) :: tail) stack = false := by
  simp only [scan_instr, focusSucceeded, focusStep, fixedArity, Option.isSome_none]

private theorem scan_return_none : scanSucceeded types (instr .return_ :: tail) stack = false := by
  simp only [scan_instr, focusSucceeded, focusStep, fixedArity, Option.isSome_none]

private theorem label_preserves_progress (success : scanSucceeded types body [] = true) :
    labelSucceeded types n continuation body = true := by
  have inner := success
  rw [scan_splitValues] at inner
  simp only [labelSucceeded, labelStep]
  split
  · rfl
  · simp_all only [scan_branch_none, Bool.false_eq_true]
  · rfl
  · rfl
  · split <;> first | rfl | simpa only [Option.isSome_map, scanSucceeded] using success

private theorem frame_preserves_progress (success : scanSucceeded state.module.types body [] = true) :
    frameSucceeded types n state body = true := by
  have inner := success
  rw [scan_splitValues] at inner
  simp only [frameSucceeded, frameStep]
  split
  · rfl
  · simp only [pureFrameStep]
    split
    · have restNil : (splitValues body).rest = [] := by assumption
      rw [restNil] at inner
      simp only [scanSucceeded, scan, Option.isSome_none, Bool.false_eq_true] at inner
    · simp_all only [scan_return_none, Bool.false_eq_true]
    · split <;> first | rfl | simpa only [Option.isSome_map, scanSucceeded] using success

private theorem local_choice_complete (found : (reduceControlChoice code).isSome = true) :
    (localStep types code).isSome = true := by
  simp only [localStep]
  repeat first | simp_all | split

private theorem splitValues_all_values (vs : List Value) :
    (splitValues (values vs)).stack = vs ∧ (splitValues (values vs)).rest = [] := by
  induction vs with
  | nil => constructor <;> rfl
  | cons value vs ih =>
    simp only [values, List.map_cons, splitValues]
    simp_all [values]

private theorem operands_none_bound (missing : operands stack n = none) : stack.length < n := by
  by_cases bound : n ≤ stack.length
  · simp [operands, bound] at missing
  · omega

private theorem frame_priority
    (success : (pureFrameStep types n state body (scan state.module.types body [])).isSome = true) :
    frameSucceeded types n state body = true := by
  simp only [frameSucceeded, frameStep]
  split
  · rfl
  · exact success

private theorem block_focus_complete (ht : bt.resolve types = some ft)
    (ha : args.length = ft.params.length) :
    focusSucceeded types (stack ++ args) (.block bt body) = true := by
  have bound : ft.params.length ≤ (stack ++ args).length := by simp; omega
  have found := operands_complete bound
  simp only [focusSucceeded, focusStep]
  repeat first | rfl | simp_all | split
  all_goals subst_vars
  all_goals first | rfl | grind [operands_none_bound, List.length_append]

private theorem loop_focus_complete (ht : bt.resolve types = some ft)
    (ha : args.length = ft.params.length) :
    focusSucceeded types (stack ++ args) (.loop bt body) = true := by
  have bound : ft.params.length ≤ (stack ++ args).length := by simp; omega
  have found := operands_complete bound
  simp only [focusSucceeded, focusStep]
  repeat first | rfl | simp_all | split
  all_goals subst_vars
  all_goals first | rfl | grind [operands_none_bound, List.length_append]

private theorem label_done_complete : labelSucceeded types n continuation (values vs) = true := by
  have parts := splitValues_all_values vs
  simp only [labelSucceeded, labelStep]
  repeat first | simp_all | split

private theorem label_trap_complete : labelSucceeded types n continuation [.trap] = true := by
  simp only [labelSucceeded, labelStep, splitValues]
  repeat first | simp_all | split

private theorem label_return_complete :
    labelSucceeded types n continuation (values vs ++ instr .return_ :: suffix) = true := by
  have parts := splitValues_values vs (code := instr .return_ :: suffix)
  simp only [splitValues, List.append_nil] at parts
  simp only [labelSucceeded, labelStep]
  repeat first | simp_all | split

private theorem label_br_succ_complete :
    labelSucceeded types n continuation (values vs ++ instr (.br (l + 1)) :: suffix) = true := by
  have parts := splitValues_values vs (code := instr (.br (l + 1)) :: suffix)
  simp only [splitValues, List.append_nil] at parts
  simp only [labelSucceeded, labelStep]
  repeat first | simp_all | split

private theorem label_br_zero_complete (h : results.length = n) :
    labelSucceeded types n continuation
      (values discarded ++ values results ++ [instr (.br 0)] ++ suffix) = true := by
  have combined : values discarded ++ values results = values (discarded ++ results) := by
    simp [values]
  rw [combined, List.append_assoc, List.singleton_append]
  have parts := splitValues_values (discarded ++ results) (code := instr (.br 0) :: suffix)
  simp only [splitValues, List.append_nil] at parts
  have bound : n ≤ (discarded ++ results).length := by simp; omega
  have found := operands_complete bound
  simp only [labelSucceeded, labelStep]
  repeat first | rfl | simp_all | split
  all_goals subst_vars
  all_goals first | rfl | grind [operands_none_bound, List.length_append]

private theorem frame_done_complete (h : vs.length = n) :
    frameSucceeded types n state (values vs) = true := by
  apply frame_priority
  have parts := splitValues_all_values vs
  simp only [pureFrameStep]
  repeat first | simp_all | split

private theorem frame_trap_complete : frameSucceeded types n state [.trap] = true := by
  apply frame_priority
  simp only [pureFrameStep, splitValues]
  repeat first | simp_all | split

private theorem frame_return_complete (h : results.length = n) :
    frameSucceeded types n state
      (values discarded ++ values results ++ [instr .return_] ++ suffix) = true := by
  have combined : values discarded ++ values results = values (discarded ++ results) := by
    simp [values]
  rw [combined, List.append_assoc, List.singleton_append]
  apply frame_priority
  have parts := splitValues_values (discarded ++ results) (code := instr .return_ :: suffix)
  simp only [splitValues, List.append_nil] at parts
  have bound : n ≤ (discarded ++ results).length := by simp; omega
  have found := operands_complete bound
  simp only [pureFrameStep]
  repeat first | rfl | simp_all | split
  all_goals subst_vars
  all_goals first | rfl | grind [operands_none_bound, List.length_append]

private theorem focus_control_complete (reduced : ControlReduces types code next) :
    scanSucceeded types (code ++ tail) stack = true := by
  cases reduced with
  | block ht ha =>
    rw [List.append_assoc, scan_values, List.singleton_append, scan_instr]
    exact block_focus_complete ht ha
  | loop ht ha =>
    rw [List.append_assoc, scan_values, List.singleton_append, scan_instr]
    exact loop_focus_complete ht ha
  | ifZero | ifNonzero _ | brIfZero | brIfNonzero _ | brTableHit _ | brTableDefault _ =>
    apply scan_fixed_complete (args := [.i32 _]) rfl
    apply local_choice_complete
    simp [values, reduceControlChoice]
  | labelDone => rw [List.singleton_append, scan_label]; exact label_done_complete
  | labelTrap => rw [List.singleton_append, scan_label]; exact label_trap_complete
  | returnLabel =>
    rw [List.singleton_append, scan_label]
    simpa only [List.append_assoc, List.singleton_append] using label_return_complete
  | brSucc =>
    rw [List.singleton_append, scan_label]
    simpa only [List.append_assoc, List.singleton_append] using label_br_succ_complete
  | brZero h => rw [List.singleton_append, scan_label]; exact label_br_zero_complete h

private theorem focus_activation_complete (reduced : FrameReduces code next) :
    scanSucceeded types (code ++ tail) stack = true := by
  cases reduced with
  | done h => rw [List.singleton_append, scan_frame]; exact frame_done_complete h
  | trap => rw [List.singleton_append, scan_frame]; exact frame_trap_complete
  | return_ h => rw [List.singleton_append, scan_frame]; exact frame_return_complete h

private theorem frame_local_complete (reduced : LocalStep state body state' body') :
    frameSucceeded types n state body = true := by
  have found := stepLocals_complete reduced
  simp only [frameSucceeded, frameStep]
  split
  · rfl
  · simp_all [stepLocals]

private theorem scan_handler : scanSucceeded types (.handler catches body :: tail) stack =
    scanSucceeded types body [] := by
  simp only [scanSucceeded, scan, Option.isSome_map]

private theorem scan_trap : scanSucceeded types (.trap :: tail) stack =
    if stack.length + tail.length = 0 then false else true := by
  simp only [scanSucceeded, scan]
  split <;> simp_all

private theorem trap_has_context (nonterminal : values vs ++ [.trap] ++ suffix ≠ [.trap]) :
    vs.length + suffix.length ≠ 0 := by
  intro empty
  have valuesEmpty : vs = [] := List.length_eq_zero_iff.mp (by omega)
  have suffixEmpty : suffix = [] := List.length_eq_zero_iff.mp (by omega)
  apply nonterminal
  simp [valuesEmpty, suffixEmpty, values]

private theorem scan_complete (reduced : ExecStep types code next)
    (stack : List Value) (tail : List AdminInstr) :
    scanSucceeded types (code ++ tail) stack = true := by
  induction reduced generalizing stack tail with
  | primitive h => exact focus_primitive_complete h
  | integer h => exact focus_integer_complete h
  | activation h => exact focus_activation_complete h
  | control h => exact focus_control_complete h
  | @context types code next vs suffix _ ih =>
    simpa only [List.append_assoc, scan_values] using ih (stack ++ vs) (suffix ++ tail)
  | label _ ih =>
    rw [List.singleton_append, scan_label]
    apply label_preserves_progress
    simpa only [List.append_nil] using ih [] []
  | handler _ ih =>
    rw [List.singleton_append, scan_handler]
    simpa only [List.append_nil] using ih [] []
  | frame _ ih =>
    rw [List.singleton_append, scan_frame]
    apply frame_preserves_progress
    simpa only [List.append_nil] using ih [] []
  | localFrame h =>
    rw [List.singleton_append, scan_frame]
    exact frame_local_complete h
  | trap h =>
    have occupied := trap_has_context h
    simp only [List.append_assoc, scan_values, List.cons_append, scan_trap,
      List.length_append]
    split
    · exfalso; exact occupied (by omega)
    · rfl

private def checkedStep (types : TypeContext) (es : List AdminInstr) : CheckedStep types es :=
  scan types es []

/-- One semantic step, including nested labels. `none` means this strategy cannot step. -/
def step (types : TypeContext) (es : List AdminInstr) : Option (List AdminInstr) :=
  (checkedStep types es).map Subtype.val

theorem step_sound (h : step types es = some next) : ExecStep types es next := by
  unfold step at h
  cases hs : checkedStep types es with
  | none => simp [hs] at h
  | some s => simp [hs] at h; subst next; exact s.property

/-- Every semantic pure/control reduction yields a successor, including all evaluation contexts. -/
theorem step_complete (reduced : ExecStep types code next) : (step types code).isSome = true := by
  have success := scan_complete reduced [] []
  rw [List.append_nil] at success
  simpa only [step, checkedStep, Option.isSome_map, scanSucceeded] using success

/-- A failed pure/control step means that its semantics has no successor. -/
theorem step_none_iff : step types code = none ↔ ¬ ∃ next, ExecStep types code next := by
  constructor
  · intro stopped ⟨next, reduced⟩
    have success := step_complete reduced
    simp [stopped] at success
  · intro irreducible
    cases found : step types code with
    | none => rfl
    | some next => exact False.elim (irreducible ⟨next, step_sound found⟩)

#print axioms step_complete
#print axioms step_none_iff

inductive StepOutcome where
  | next (code : List AdminInstr)
  | finished (results : List Value)
  | trapped
  | exception (address : ExnAddr)
  | stuck
  deriving BEq, Repr

/-- Classify terminal states separately from malformed or unbound instructions. -/
def stepOutcome (types : TypeContext) (es : List AdminInstr) : StepOutcome :=
  match step types es with
  | some next => .next next
  | none =>
    let p := splitValues es
    match p.rest with
    | [] => .finished p.stack
    | _ => match es with
      | [.trap] => .trapped
      | [.throwing address] => .exception address
      | _ => .stuck

theorem stepOutcome_finished (h : stepOutcome types es = .finished vs) : es = values vs := by
  cases hs : step types es with
  | some next => simp [stepOutcome, hs] at h
  | none =>
    cases hr : (splitValues es).rest with
    | nil =>
      have hv : (splitValues es).stack = vs := by simpa [stepOutcome, hs, hr] using h
      simpa [hr, hv] using (splitValues es).reconstruct
    | cons x xs =>
      simp only [stepOutcome, hs, hr] at h
      split at h <;> cases h

theorem stepOutcome_trapped (h : stepOutcome types es = .trapped) : es = [.trap] := by
  cases hs : step types es with
  | some next => simp [stepOutcome, hs] at h
  | none =>
    cases hr : (splitValues es).rest with
    | nil => simp [stepOutcome, hs, hr] at h
    | cons x xs =>
      simp only [stepOutcome, hs, hr] at h
      split at h
      · rfl
      · cases h
      · cases h

private def checkedRun (types : TypeContext) : (fuel : Nat) → (es : List AdminInstr) →
    { final : List AdminInstr // ExecSteps types es final }
  | 0, es => ⟨es, .refl⟩
  | fuel + 1, es =>
    match checkedStep types es with
    | none => ⟨es, .refl⟩
    | some next =>
      let result := checkedRun types fuel next.val
      ⟨result.val, .cons next.property result.property⟩

inductive RunStatus where
  | finished (results : List Value)
  | trapped
  | exception (address : ExnAddr)
  | stuck
  | exhausted
  /-- Native execution stopped before exceeding its function activation limit. -/
  | callStackExhausted
  | resourceLimit (limit : ResourceLimit)
  deriving BEq, DecidableEq, Repr

structure RunResult where
  state : List AdminInstr
  status : RunStatus
  deriving BEq, Repr

/-- Execute at most `fuel` semantic steps; exhausted execution preserves its residual state. -/
def run (fuel : Nat) (types : TypeContext) (es : List AdminInstr) : RunResult :=
  let result := checkedRun types fuel es
  let status := match stepOutcome types result.val with
    | .finished vs => RunStatus.finished vs
    | .trapped => .trapped
    | .exception address => .exception address
    | .stuck => .stuck
    | .next _ => .exhausted
  ⟨result.val, status⟩

theorem run_sound : ExecSteps types es (run fuel types es).state :=
  (checkedRun types fuel es).property

theorem run_finished (h : (run fuel types es).status = .finished vs) :
    (run fuel types es).state = values vs := by
  unfold run at h ⊢
  dsimp only at h ⊢
  split at h
  · rename_i hs
    cases h
    exact stepOutcome_finished hs
  · cases h
  · cases h
  · cases h
  · cases h

theorem run_trapped (h : (run fuel types es).status = .trapped) :
    (run fuel types es).state = [.trap] := by
  unfold run at h ⊢
  dsimp only at h ⊢
  split at h
  · cases h
  · rename_i hs
    exact stepOutcome_trapped hs
  · cases h
  · cases h
  · cases h

end Wasm
