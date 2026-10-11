import Wasm.TypeSafety.CoreExecution

namespace Wasm.TypeSafety

/-- Function bodies are checked independently of invocation and store safety. -/
def CoreFunctionTyped (store : Store) (function : FuncInst) : Prop :=
  match function.code with
  | .wasm code => ∃ context,
      CoreModuleTyped store function.module context ∧
      context.locals = function.type.params ++ code.locals ∧
      context.returns = some function.type.results ∧
      function.module.types.func? code.typeIdx = some function.type ∧
      (∀ t ∈ context.locals, t.IsInteger) ∧
      (∀ t ∈ function.type.results, t.IsInteger) ∧
      CoreTyping store context [function.type.results]
        (instructions code.body) [] function.type.results
  | _ => False

/-- Recursive calls share a store invariant; no invocation premise defines well-typedness. -/
def CoreStoreTyped (store : Store) : Prop :=
  ∀ address function, store.func? address = some function → CoreFunctionTyped store function

theorem Typed.integer_type (typed : Typed store v t) (integer : t.IsInteger) : v.type = t := by
  obtain ⟨actual, lookup, matching⟩ := typed
  have actualType : actual = t := by
    cases t <;> simp only [ValType.IsInteger] at integer <;> try contradiction
    all_goals
      generalize ha : Types.embedVal actual = a at matching
      generalize ht : Types.embedVal _ = b at matching
      cases matching <;> cases actual <;>
        simp_all [Types.embedVal, Types.RefType.val]
  subst actual
  cases t <;> simp only [ValType.IsInteger] at integer <;> try contradiction
  all_goals cases v <;> simp_all [Value.type?, Value.type]
  all_goals
    rename_i reference
    cases reference <;>
      simp [RefValue.type?, Option.map_eq_some_iff] at lookup
    all_goals repeat (first | contradiction | split at lookup | simp_all)

theorem Typed.of_integer (integer : v.type.IsInteger) : Typed store v v.type := by
  cases v <;> simp only [Value.type, ValType.IsInteger] at integer <;> try contradiction
  · exact ⟨.i32, rfl, .i32⟩
  · exact ⟨.i64, rfl, .i64⟩

theorem ArgsTyped.integer_types (typed : ArgsTyped store vs ts)
    (integer : ∀ t ∈ ts, t.IsInteger) : vs.map Value.type = ts := by
  induction typed with
  | nil => rfl
  | @cons v t vs ts head _ ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨Typed.integer_type head (integer t (by simp)),
      ih (fun t ht => integer t (by simp [ht]))⟩

theorem ArgsTyped.of_integer_types (types : vs.map Value.type = ts)
    (integer : ∀ t ∈ ts, t.IsInteger) : ArgsTyped store vs ts := by
  subst ts
  induction vs with
  | nil => exact .nil
  | cons v vs ih =>
    exact .cons (Typed.of_integer (integer v.type (by simp)))
      (ih (fun t ht => integer t (by simp [ht])))

theorem CoreFrameTyped.initialize (moduleTyped : CoreModuleTyped store module context)
    (locals : context.locals = params ++ localTypes)
    (integer : ∀ t ∈ context.locals, t.IsInteger)
    (args : vs.map Value.type = params) :
    CoreFrameTyped store (Frame.initialize module vs localTypes) context := by
  refine ⟨moduleTyped, ?_, integer⟩
  rw [Frame.initialize_types, ← List.map_map, locals, args, List.map_append]
  congr 1
  apply List.map_congr_left
  intro t ht
  have hi := integer t (by rw [locals]; simp [ht])
  cases t <;> simp_all [ValType.IsInteger, ValType.defaultable]

/-- The defining module supplies a fresh, typed activation for an invocation. -/
theorem Invokes.core_typed (functionTyped : CoreFunctionTyped store function)
    (invoke : Invokes store function args activation) :
    CoreInstrTyping store callerContext labels activation [] function.type.results := by
  cases invoke with
  | @wasm type args module code signature argTypes =>
    obtain ⟨context, hm, hl, hr, _, hi, _, hb⟩ := functionTyped
    have hp : ∀ t ∈ type.params, t.IsInteger := by
      intro t ht
      apply hi
      rw [hl]; simp [ht]
    have ha := ArgsTyped.integer_types argTypes hp
    have hf := CoreFrameTyped.initialize hm hl hi ha
    apply CoreInstrTyping.frame hf hr
    exact .cons (.label (branch := type.results) hb .nil) .nil

theorem CoreFunctionTyped.params_integer (h : CoreFunctionTyped store function) :
    ∀ t ∈ function.type.params, t.IsInteger := by
  cases function with
  | mk type module code =>
    cases code with
    | wasm code =>
      obtain ⟨context, _, hl, _, _, hi, _, _⟩ := h
      intro t ht
      apply hi
      rw [hl]; simp [ht]
    | host | hostTyped => contradiction

theorem Invokes.args_typed (invoke : Invokes store function args activation) :
    ArgsTyped store args function.type.params := by
  cases invoke with
  | wasm _ args => exact args

theorem CoreFunctionTyped.invokable (h : CoreFunctionTyped store function)
    (types : args.map Value.type = function.type.params) :
    ∃ activation, Invokes store function args activation := by
  have hp := h.params_integer
  cases function with
  | mk type module code =>
    cases code with
    | wasm code =>
      obtain ⟨_, _, _, _, signature, _, _, _⟩ := h
      exact ⟨_, .wasm signature (ArgsTyped.of_integer_types types hp)⟩
    | host | hostTyped => contradiction

end Wasm.TypeSafety
