import Wasm.ExecutableValidation

/-! Success soundness for the ordinary executable integer validator. -/
namespace Wasm.Validation

theorem integerType_sound (h : integerType t = true) : t.IsInteger := by
  cases t <;> simp_all [integerType, ValType.IsInteger]

theorem numberType_sound (h : numberType t = true) : t.IsNumber := by
  cases t <;> simp_all [numberType, ValType.IsNumber]

private theorem pop_eq_some : popOperands types stack = some rest ↔ stack = types ++ rest := by
  induction types generalizing stack with
  | nil => simp [popOperands]
  | cons t types ih =>
    cases stack with
    | nil => simp [popOperands]
    | cons a stack =>
      by_cases h : t = a
      · subst a
        simp [popOperands, ih]
      · simp [popOperands, h, Ne.symm h]

theorem consume_eq_some : consume input stack = some base ↔ stack = base ++ input := by
  simp only [consume, Option.map_eq_some_iff, pop_eq_some]
  constructor
  · rintro ⟨rest, hs, hp⟩
    cases hp
    have := congrArg List.reverse hs
    simpa using this
  · intro h
    refine ⟨base.reverse, ?_, by simp⟩
    simp [h]

theorem castTop_sound (h : castTop context nullable heap = .ok top) :
    (Types.ValType.ref nullable heap).Valid ⟨context.definedTypes, []⟩ ∧
      Types.HeapMatches ⟨context.definedTypes, []⟩ heap top ∧
      top ∈ [Types.HeapType.any, .func, .extern, .exn] := by
  simp only [castTop] at h
  split at h
  · have valid : Types.Algorithm.valValid ⟨context.definedTypes, []⟩
        (.ref nullable heap) = true := by assumption
    split at h
    · cases h
      exact ⟨Types.Algorithm.valValid_sound valid,
        Types.Algorithm.heapMatches_sound (by assumption), by simp⟩
    · split at h
      · cases h
        exact ⟨Types.Algorithm.valValid_sound valid,
          Types.Algorithm.heapMatches_sound (by assumption), by simp⟩
      · split at h
        · cases h
          exact ⟨Types.Algorithm.valValid_sound valid,
            Types.Algorithm.heapMatches_sound (by assumption), by simp⟩
        · split at h
          · cases h
            exact ⟨Types.Algorithm.valValid_sound valid,
              Types.Algorithm.heapMatches_sound (by assumption), by simp⟩
          · contradiction
  · contradiction


private theorem funcHeap_sound (h : functionHeap kind = true) : kind = .func := by
  cases kind <;> simp_all [functionHeap]

private theorem effect_sound (h : effect context i stack = .ok (input, output)) :
    RuntimeInstrTyping context labels i input output := by
  cases i <;> simp only [effect, pure, Except.pure] at h
  all_goals try { cases h }
  case const value =>
    cases value <;> simp at h
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals exact .plain (.plain (.plain (.const (by trivial))))
  case nop => cases h; exact .plain (.plain (.plain .nop))
  case drop =>
    cases hs : stack.getLast? <;> simp [hs] at h
    rcases h with ⟨rfl, rfl⟩
    exact .plain (.plain (.plain .drop))
  case select types =>
    cases types with
    | none =>
      cases hs : stack.reverse[1]? <;> simp [hs] at h
      split at h <;> simp_all
      rcases h with ⟨rfl, rfl⟩
      exact .plain (.plain (.plain (.select (numberType_sound (by assumption)))))
    | some types =>
      cases types with
      | nil => cases h
      | cons t types =>
        cases types with
        | cons _ _ => cases h
        | nil =>
          change (if supportedValueType t then Except.ok ([t, t, .i32], [t])
            else Except.error (Error.unsupported "select value type")) = .ok (input, output) at h
          split at h <;> simp_all
          rcases h with ⟨rfl, rfl⟩
          exact .plain (.plain (.plain .selectTyped))
  case binop t op =>
    split at h <;> simp_all
    rcases h with ⟨rfl, rfl⟩
    exact .plain (.plain (.plain (.binop (integerType_sound (by assumption)))))
  case eqz t =>
    split at h <;> simp_all
    rcases h with ⟨rfl, rfl⟩
    exact .plain (.plain (.plain (.eqz (integerType_sound (by assumption)))))
  case intUnary t op =>
    split at h <;> simp_all
    rcases h with ⟨rfl, rfl⟩
    exact .plain (.plain (.plain (.intUnary (integerType_sound (by assumption)))))
  case intBinary t op =>
    split at h <;> simp_all
    rcases h with ⟨rfl, rfl⟩
    exact .plain (.plain (.plain (.intBinary (integerType_sound (by assumption)))))
  case intRel t op =>
    split at h <;> simp_all
    rcases h with ⟨rfl, rfl⟩
    exact .plain (.plain (.plain (.intRel (integerType_sound (by assumption)))))
  case intConvert op =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact .plain (.plain (.plain .intConvert))
  case floatUnary width op => cases h; exact .plain (.plain (.plain .floatUnary))
  case floatBinary width op => cases h; exact .plain (.plain (.plain .floatBinary))
  case floatRel width op => cases h; exact .plain (.plain (.plain .floatRel))
  case floatConvert op => cases h; exact .plain (.plain (.plain .floatConvert))
  case localGet x =>
    cases hl : context.locals[x]? <;> simp [hl] at h
    rcases h with ⟨rfl, rfl⟩
    exact .plain (.localGet hl)
  case localSet x =>
    cases hl : context.locals[x]? <;> simp [hl] at h
    rcases h with ⟨rfl, rfl⟩
    exact .plain (.localSet hl)
  case localTee x =>
    cases hl : context.locals[x]? <;> simp [hl] at h
    rcases h with ⟨rfl, rfl⟩
    exact .plain (.localTee hl)
  case globalGet x =>
    cases hg : context.globals[x]? <;> simp [hg] at h
    rcases h with ⟨rfl, rfl⟩
    exact .global (.get hg)
  case globalSet x =>
    cases hg : context.globals[x]? <;> simp [hg] at h
    rename_i type
    cases type with
    | mk mutability valType =>
      cases mutability <;> simp at h
      rcases h with ⟨rfl, rfl⟩
      exact .global (.set hg)
  case load op x arg =>
    cases hm : context.mems[x]? <;> simp [hm] at h
    split at h <;> simp_all [throw]
    rcases h with ⟨rfl, rfl⟩
    exact .memory (.load hm (by assumption))
  case store op x arg =>
    cases hm : context.mems[x]? <;> simp [hm] at h
    split at h <;> simp_all [throw]
    rcases h with ⟨rfl, rfl⟩
    exact .memory (.store hm (by assumption))
  case memorySize x =>
    cases hm : context.mems[x]? <;> simp [hm] at h
    rcases h with ⟨rfl, rfl⟩
    exact .memory (.size hm)
  case memoryGrow x =>
    cases hm : context.mems[x]? <;> simp [hm] at h
    rcases h with ⟨rfl, rfl⟩
    exact .memory (.grow hm)
  case memoryFill x =>
    cases hm : context.mems[x]? <;> simp [hm] at h
    rcases h with ⟨rfl, rfl⟩
    exact .bulk (.fill hm)
  case memoryCopy x y =>
    cases hd : context.mems[x]? <;> simp [hd] at h
    cases hs : context.mems[y]? <;> simp [hs] at h
    rcases h with ⟨rfl, rfl⟩
    exact .bulk (.copy hd hs)
  case memoryInit x y =>
    cases hm : context.mems[x]? <;> simp [hm] at h
    split at h <;> simp_all [throw]
    rcases h with ⟨rfl, rfl⟩
    exact .bulk (.init hm (by assumption))
  case dataDrop y =>
    split at h <;> simp_all [throw]
    rcases h with ⟨rfl, rfl⟩
    exact .bulk (.drop (by assumption))
  case call x =>
    cases hf : context.funcs[x]? <;> simp [hf] at h
    rcases h with ⟨rfl, rfl⟩
    exact .call hf
  case callIndirect x y =>
    cases ht : context.tables[x]? <;> simp [ht] at h
    split at h <;> simp_all [throw]
    cases hf : context.types.func? (y) <;> simp [hf] at h
    rcases h with ⟨rfl, rfl⟩
    exact .tables (.indirect ht (funcHeap_sound (by assumption)) hf)
  case vector op =>
    cases hs : vectorSignature? context.mems op <;> simp [hs] at h
    rcases h with ⟨rfl, rfl⟩
    exact .vector (vectorSignature?_sound hs)
  case arrayOp op =>
    cases hs : arraySignature? context.types context.definedTypes context.referenceElemTypes
        context.dataCount op <;> simp [hs] at h
    rcases h with ⟨rfl, rfl⟩
    exact .arrays (arraySignature?_sound hs)
  case structNew x default =>
    cases hs : structSignature? context.types (.structNew x default) <;> simp [hs] at h
    rcases h with ⟨rfl, rfl⟩
    exact .structures (structSignature?_sound hs)
  case structGet x y signed =>
    cases hs : structSignature? context.types (.structGet x y signed) <;> simp [hs] at h
    rcases h with ⟨rfl, rfl⟩
    exact .structures (structSignature?_sound hs)
  case structSet x y =>
    cases hs : structSignature? context.types (.structSet x y) <;> simp [hs] at h
    rcases h with ⟨rfl, rfl⟩
    exact .structures (structSignature?_sound hs)
  case refTest nullable heap =>
    cases ht : castTop context nullable heap <;> simp [ht, bind, Except.bind] at h
    rcases h with ⟨rfl, rfl⟩
    obtain ⟨valid, matched, top⟩ := castTop_sound ht
    exact .refTest valid matched top
  case refCast nullable heap =>
    cases ht : castTop context nullable heap <;> simp [ht, bind, Except.bind] at h
    rcases h with ⟨rfl, rfl⟩
    obtain ⟨valid, matched, top⟩ := castTop_sound ht
    exact .refCast valid matched top
  case gcReference op =>
    cases h
    exact .gcReference
  case refNull kind =>
    cases h
    exact .references .null
  case refFunc x =>
    cases hf : context.funcs[x]? <;> simp [hf] at h
    split at h <;> simp_all
    rcases h with ⟨rfl, rfl⟩
    exact .references (.func hf (by assumption))
  case refIsNull =>
    cases hs : stack.getLast? <;> simp [hs] at h
    rename_i type
    cases type <;> simp at h
    rcases h with ⟨rfl, rfl⟩
    exact .references .isNull
  case tableGet x =>
    cases ht : context.tables[x]? <;> simp [ht] at h
    rcases h with ⟨rfl, rfl⟩
    exact .tables (.get ht)
  case tableSet x =>
    cases ht : context.tables[x]? <;> simp [ht] at h
    rcases h with ⟨rfl, rfl⟩
    exact .tables (.set ht)
  case tableSize x =>
    cases ht : context.tables[x]? <;> simp [ht] at h
    rcases h with ⟨rfl, rfl⟩
    exact .tables (.size ht)
  case tableGrow x =>
    cases ht : context.tables[x]? <;> simp [ht] at h
    rcases h with ⟨rfl, rfl⟩
    exact .tables (.grow ht)
  case tableFill x =>
    cases ht : context.tables[x]? <;> simp [ht] at h
    rcases h with ⟨rfl, rfl⟩
    exact .tables (.fill ht)
  case tableCopy x y =>
    cases hd : context.tables[x]? <;> simp [hd] at h
    cases hs : context.tables[y]? <;> simp [hs] at h
    split at h <;> simp_all [throw]
    rcases h with ⟨rfl, rfl⟩
    exact .tables (.copy hd hs (by simp_all) (by simp_all))
  case tableInit x y =>
    cases ht : context.tables[x]? <;> simp [ht] at h
    cases he : context.elems[y]? <;> simp [he] at h
    split at h <;> simp_all [throw]
    rcases h with ⟨rfl, rfl⟩
    exact .tables (.init ht (by simpa using he) (by simp_all))
  case elemDrop y =>
    cases he : context.elems[y]? <;> simp [he] at h
    rcases h with ⟨rfl, rfl⟩
    exact .tables (.drop he)

private theorem popPolymorphic_sound
    (h : popPolymorphic dead required stack = some (missing, base)) :
    stack ++ missing = required ++ base ∧ (dead = false → missing = []) := by
  induction required generalizing stack with
  | nil =>
    simp only [popPolymorphic, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp
  | cons t required ih =>
    cases stack with
    | nil =>
      simp only [popPolymorphic] at h
      split at h <;> simp_all
    | cons a stack =>
      simp only [popPolymorphic] at h
      split at h <;> simp_all
      subst a
      exact (ih h).2

theorem consumePolymorphic_sound
    (h : consumePolymorphic input stack dead = some (missing, base)) :
    missing ++ stack = base ++ input ∧ (dead = false → missing = []) := by
  simp only [consumePolymorphic, Option.map_eq_some_iff] at h
  obtain ⟨⟨ms, bs⟩, hp, he⟩ := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  obtain ⟨hs, hd⟩ := popPolymorphic_sound hp
  exact ⟨by simpa using congrArg List.reverse hs, fun h => by simp [hd h]⟩

private def CheckedEffect.Typed (context : FunctionContext) (labels : LabelContext)
    (i : Instr) : CheckedEffect → Prop
  | .normal input output => RuntimeInstrTyping context labels i input output
  | .jump input => ∀ base output, RuntimeInstrTyping context labels i (base ++ input) output

private theorem ordinaryEffect_sound
    (h : (do let (input, output) ← effect context i stack
             pure (CheckedEffect.normal input output)) = .ok eff) :
    eff.Typed context labels i := by
  cases he : effect context i stack <;> simp [he, bind, Except.bind, pure, Except.pure] at h
  cases h
  exact effect_sound he

private theorem scopedEffect_sound
    (h : scopedEffect context labels i stack candidate bodyCheck = .ok eff)
    (hb : ∀ ls body input output, bodyCheck ls body input output = true →
      RuntimeSeqTyping context ls body input output) : eff.Typed context labels i := by
  cases i <;> simp only [scopedEffect, pure, Except.pure] at h
  case unreachable =>
    cases h
    intro base output
    exact .plain (.plain (.plain .unreachable))
  case return_ =>
    cases hr : context.returns <;> simp [hr] at h
    cases h
    intro base output
    exact .return_ hr
  case br x =>
    cases hl : labels[x]? <;> simp [hl] at h
    cases h
    intro base output
    exact .plain (.plain (.br hl))
  case brIf x =>
    cases hl : labels[x]? <;> simp [hl] at h
    cases h
    exact .plain (.plain (.brIf hl))
  case brTable targets fallback =>
    cases hl : labels[fallback]? <;> simp [hl] at h
    split at h <;> simp_all
    cases h
    intro base output
    simpa [List.append_assoc] using
      (RuntimeInstrTyping.plain (FunctionInstrTyping.plain
        (ControlInstrTyping.brTable hl (by assumption))) :
        RuntimeInstrTyping context labels (.brTable targets fallback)
          (base ++ _ ++ [.i32]) output)
  case block bt body =>
    cases ht : bt.resolve context.types <;> simp [ht] at h
    split at h <;> simp_all
    cases h
    exact .block ht (hb _ _ _ _ (by assumption))
  case loop bt body =>
    cases ht : bt.resolve context.types <;> simp [ht] at h
    split at h <;> simp_all
    cases h
    exact .loop ht (hb _ _ _ _ (by assumption))
  case if_ bt yes no =>
    cases ht : bt.resolve context.types <;> simp [ht] at h
    split at h <;> simp_all
    cases h
    exact .if_ ht (hb _ _ _ _ (by exact (And.left (by assumption))))
      (hb _ _ _ _ (by exact (And.right (by assumption))))
  case drop =>
    cases h
    exact .plain (.plain (.plain .drop))
  case refIsNull =>
    cases ht : stack.getLast?.getD candidate <;> simp [ht] at h
    cases h
    exact .references .isNull
  case select ts =>
    cases ts with
    | none =>
      change (if numberType (stack.reverse[1]?.getD candidate) then
        Except.ok (CheckedEffect.normal
          [stack.reverse[1]?.getD candidate, stack.reverse[1]?.getD candidate, .i32]
          [stack.reverse[1]?.getD candidate])
        else Except.error (Error.invalid "select requires numeric operands")) = .ok eff at h
      split at h <;> simp_all
      cases h
      exact .plain (.plain (.plain (.select (numberType_sound (by assumption)))))
    | some ts => exact ordinaryEffect_sound h
  all_goals exact ordinaryEffect_sound h

/-- Success constructs a declarative derivation for a suitable polymorphic stack prefix.
The prefix is empty in reachable code. No derivation is built by the executable checker. -/
theorem checkScoped_sound
    (h : checkScoped fuel context labels code stack dead output = true) :
    ∃ padding, (dead = false → padding = []) ∧
      RuntimeSeqTyping context labels code (padding ++ stack) output := by
  induction fuel generalizing context labels code stack dead output with
  | zero => cases h
  | succ fuel ih =>
    cases code with
    | nil =>
      simp only [checkScoped] at h
      cases dead with
      | false =>
        simp at h
        subst output
        exact ⟨[], by simp, .empty⟩
      | true =>
        simp only [↓reduceIte, Option.isSome_iff_exists] at h
        obtain ⟨padding, hp⟩ := h
        rw [consume_eq_some.mp hp]
        exact ⟨padding, by simp, .empty⟩
    | cons i rest =>
      simp only [checkScoped, List.any_eq_true] at h
      obtain ⟨candidate, _, h⟩ := h
      cases he : scopedEffect context labels i stack candidate
          (fun ls body input output => checkScoped fuel context ls body input false output) <;>
        simp [he] at h
      rename_i eff
      have typed := scopedEffect_sound he (fun ls body input output success => by
        obtain ⟨padding, hp, derivation⟩ := ih success
        simpa [hp rfl] using derivation)
      cases eff with
      | normal required produced =>
        cases hc : consumePolymorphic required stack dead <;> simp [hc] at h
        rename_i pair
        rcases pair with ⟨missing, base⟩
        obtain ⟨padding, hp, tail⟩ := ih h
        obtain ⟨hs, hm⟩ := consumePolymorphic_sound hc
        refine ⟨padding ++ missing, fun hd => by simp [hp hd, hm hd], ?_⟩
        have step : RuntimeInstrTyping context labels i
            ((padding ++ missing) ++ stack) (padding ++ (base ++ produced)) := by
          simpa only [List.append_assoc, hs] using
            (RuntimeInstrTyping.weaken (ts₀ := padding ++ base) typed)
        exact .cons step tail
      | jump required =>
        cases hc : consumePolymorphic required stack dead <;> simp [hc] at h
        rename_i pair
        rcases pair with ⟨missing, base⟩
        obtain ⟨padding, _, tail⟩ := ih h
        obtain ⟨hs, hm⟩ := consumePolymorphic_sound hc
        refine ⟨missing, hm, .cons ?_ (by simpa using tail)⟩
        rw [hs]
        exact typed base padding

theorem checkCode_sound
    (h : checkCode context code input output (labels := labels) = .ok ()) :
    RuntimeSeqTyping context labels code input output := by
  unfold checkCode at h
  split at h <;> simp_all
  obtain ⟨padding, hp, derivation⟩ := checkScoped_sound (by assumption)
  simpa [hp rfl] using derivation

private theorem validationType_refl (context : Types.Context) (t : Types.ValType) :
    Types.ValMatches context t t := by
  cases t with
  | i32 => exact .i32
  | i64 => exact .i64
  | f32 => exact .f32
  | f64 => exact .f64
  | v128 => exact .v128
  | bot => exact .bot
  | ref nullable heap => exact .ref (Types.RefMatches.refl context ⟨nullable, heap⟩)

private theorem validationResult_refl (context : Types.Context) (ts : List Types.ValType) :
    Types.ResultMatches context ts ts := by
  induction ts with
  | nil => exact .nil
  | cons t ts ih => exact .cons (validationType_refl context t) ih

private theorem validationResult_append
    (a : Types.ResultMatches context as bs) (b : Types.ResultMatches context cs ds) :
    Types.ResultMatches context (as ++ cs) (bs ++ ds) := by
  induction as generalizing bs with
  | nil => cases a; exact b
  | cons _ _ ih =>
    cases a with
    | cons head tail => exact .cons head (ih tail)

private theorem validationResult_reverse (h : Types.ResultMatches context as bs) :
    Types.ResultMatches context as.reverse bs.reverse := by
  induction as generalizing bs with
  | nil => cases h; exact .nil
  | cons _ _ ih =>
    cases h with
    | cons head tail =>
      simpa using validationResult_append (ih tail) (Types.ResultMatches.cons head .nil)

private theorem popBottom_sound (h : popBottom context dead required stack = some result) :
    stack ++ result.missing = result.actual ++ result.base ∧
      Types.ResultMatches context result.actual required ∧
      (dead = false → result.missing = []) := by
  induction required generalizing stack result with
  | nil =>
    simp only [popBottom, Option.some.injEq] at h
    subst result
    exact ⟨by simp, .nil, by simp⟩
  | cons t types ih =>
    cases stack with
    | nil =>
      cases dead with
      | false => simp [popBottom] at h
      | true =>
        simp only [popBottom, ↓reduceIte, Option.some.injEq] at h
        subst result
        exact ⟨by simp, validationResult_refl _ _, by simp⟩
    | cons a stack =>
      by_cases hmatches :
          Types.Algorithm.valMatches (Types.Algorithm.budget context a t) context a t = true
      · cases hp : popBottom context dead types stack with
        | none => simp [popBottom, hmatches, hp] at h
        | some popped =>
          simp [popBottom, hmatches, hp] at h
          subst result
          obtain ⟨split, typed, missing⟩ := ih hp
          refine ⟨by simpa using congrArg (a :: ·) split, .cons ?_ typed, missing⟩
          exact Types.Algorithm.valMatches_sound hmatches
      · simp [popBottom, hmatches] at h

theorem consumeBottom_sound (h : consumeBottom context required stack dead = some result) :
    result.missing ++ stack = result.base ++ result.actual ∧
      Types.ResultMatches context result.actual required ∧
      (dead = false → result.missing = []) := by
  simp only [consumeBottom, Option.map_eq_some_iff] at h
  obtain ⟨popped, hp, equal⟩ := h
  subst result
  obtain ⟨split, typed, missing⟩ := popBottom_sound (context := context) hp
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg List.reverse split
  · simpa using validationResult_reverse typed
  · intro reachable
    simp [missing reachable]

private theorem bottomNumber_sound (h : bottomNumber t = true) :
    t = .bot ∨ t = .i32 ∨ t = .i64 ∨ t = .f32 ∨ t = .f64 ∨ t = .v128 := by
  cases t <;> simp_all [bottomNumber]

private def BottomEffect.Typed (eff : BottomEffect) (context : FunctionContext)
    (labels : LabelContext) (i : Instr) : Prop := match eff with
  | .normal input output => ValidationInstrTyping context labels i input output
  | .jump input => ∀ base output,
      ValidationInstrTyping context labels i (base ++ input) output

theorem checkCatch_sound (h : checkCatch context labels c = true) :
    CatchTyping context labels c := by
  cases c with
  | tag x d reference =>
    cases ht : context.tags[x]? <;> simp [checkCatch, ht] at h
    cases hl : labels[d]? <;> simp [hl] at h
    exact .tag ht hl (Types.Algorithm.resultMatches_sound (by simpa [tailResultsMatch] using h))
  | all d reference =>
    cases hl : labels[d]? <;> simp [checkCatch, hl] at h
    exact .all hl (Types.Algorithm.resultMatches_sound (by simpa [tailResultsMatch] using h))

private theorem ordinaryBottomEffect_sound
    (h : (do let (input, output) ← effect context i []
             pure (BottomEffect.normal (input.map Types.embedVal)
               (output.map Types.embedVal))) = .ok eff) : eff.Typed context labels i := by
  cases he : effect context i [] <;>
    simp [he, bind, Except.bind, pure, Except.pure] at h
  cases h
  exact .legacy (effect_sound he)

private theorem bottomEffect_sound
    (h : bottomEffect context labels i stack bodyCheck = .ok eff)
    (hb : ∀ ls body input output, bodyCheck ls body input output = true →
      ValidationSeqTyping context ls body input output) :
    eff.Typed context labels i := by
  cases i <;> simp only [bottomEffect, pure, Except.pure] at h
  case brOnCast fail x source target =>
    cases hl : labels[x]? <;> simp [hl] at h
    rename_i ts
    cases hr : ts.reverse <;> simp [hr] at h
    rename_i label rest
    split at h <;> (split at h <;> simp_all)
    all_goals
      cases h
      have typed := ValidationInstrTyping.brOnCast (context := context) (source := source)
        (target := target) (fail := fail) hl
        (Types.Algorithm.valValid_sound (by simp_all))
        (Types.Algorithm.valValid_sound (by simp_all))
        (Types.Algorithm.valMatches_sound
          (fuel := Types.Algorithm.budget ⟨context.definedTypes, []⟩ target.val source.val)
          (by simp_all))
        (Types.Algorithm.valMatches_sound
          (fuel := Types.Algorithm.budget ⟨context.definedTypes, []⟩
            (if fail then (source.difference target).val else target.val)
            (Types.embedVal label)) (by simp_all))
      simpa [BottomEffect.Typed, List.map_reverse, *] using typed
  case gcReference op =>
    cases h
    exact .legacy .gcReference
  case drop => cases h; exact .drop
  case select types =>
    cases types with
    | none =>
      change (if bottomNumber (bottomSelectType stack) then
        Except.ok (BottomEffect.normal
          [bottomSelectType stack, bottomSelectType stack, .i32] [bottomSelectType stack])
        else Except.error (Error.invalid "select requires numeric operands or bottom")) =
        .ok eff at h
      split at h <;> simp_all
      cases h
      exact .select (bottomNumber_sound (by assumption))
    | some types =>
      exact ordinaryBottomEffect_sound h
  case refIsNull =>
    cases ht : stack.getLast?.getD Types.ValType.bot <;> simp [ht] at h
    case bot =>
      cases h
      exact .legacy (.references .isNull)
    case ref nullable heap =>
      cases h
      exact .legacy (.references .isNull)
  case refAsNonNull =>
    cases ht : stack.getLast?.getD Types.ValType.bot <;>
      simp [ht, bind, Except.bind] at h
    all_goals
      cases h
      exact .legacy .refAsNonNull
  case brOnNull x =>
    cases ht : stack.getLast?.getD Types.ValType.bot <;>
      simp [ht, bind, Except.bind] at h
    all_goals
      cases hl : labels[x]? <;> simp [hl] at h
      cases h
      simpa only [BottomEffect.Typed, List.map_append, List.map_cons, List.map_nil,
        Types.embedVal] using
        (ValidationInstrTyping.legacy (RuntimeInstrTyping.brOnNull (context := context) hl))
  case brOnNonNull x =>
    cases hl : labels[x]? <;> simp [hl] at h
    rename_i ts
    cases hr : ts.reverse with
    | nil => simp [hr] at h
    | cons last prefixTypes =>
      cases last <;> simp [hr] at h
      case ref heap =>
        cases h
        have split := congrArg List.reverse hr
        simp only [List.reverse_reverse, List.reverse_cons] at split
        simpa only [BottomEffect.Typed, List.map_append, List.map_cons, List.map_nil,
          ← List.map_reverse, Types.embedVal] using
          (ValidationInstrTyping.legacy
            (RuntimeInstrTyping.brOnNonNull (context := context) (nullable := true)
              (by simpa only [split] using hl)))
      case refNonNull heap =>
        cases h
        have split := congrArg List.reverse hr
        simp only [List.reverse_reverse, List.reverse_cons] at split
        simpa only [BottomEffect.Typed, List.map_append, List.map_cons, List.map_nil,
          ← List.map_reverse, Types.embedVal] using
          (ValidationInstrTyping.legacy
            (RuntimeInstrTyping.brOnNonNull (context := context) (nullable := false)
              (by simpa only [split] using hl)))
  case callRef x =>
    cases ht : context.types.func? (x) <;> simp [ht] at h
    cases h
    simpa only [BottomEffect.Typed, List.map_append, Types.embedVal] using
      (ValidationInstrTyping.legacy (RuntimeInstrTyping.callRef ht))
  case refFunc x =>
    cases hf : context.funcs[x]? <;> simp [hf] at h
    by_cases hd : x ∈ context.declaredRefs
    · simp [hd] at h
      cases ht : context.funcTypeIndices[x]? <;> simp [ht] at h
      · cases h; exact .legacy (.nonNullFunc hf hd)
      · cases h; exact .legacy (.typedFunc hf ht hd)
    · simp [hd] at h
  case callIndirect x y =>
    cases ht : context.tables[x]? <;> simp [ht] at h
    split at h <;> try simp_all
    cases hf : context.types.func? (y) <;> simp [hf] at h
    cases h
    simpa only [BottomEffect.Typed, List.map_append, List.map_cons, List.map_nil] using
      (ValidationInstrTyping.legacy
        (RuntimeInstrTyping.indirectTyped (context := context) (labels := labels) ht
          (Types.Algorithm.heapMatches_sound (by assumption)) hf))
  case tableCopy x y =>
    cases hd : context.tables[x]? <;> simp [hd] at h
    cases hs : context.tables[y]? <;> simp [hs] at h
    split at h <;> simp_all
    cases h
    exact .legacy (.tableCopy hd hs (Types.Algorithm.valMatches_sound (by assumption)))
  case tableInit x y =>
    cases ht : context.tables[x]? <;> simp [ht] at h
    cases he : context.elems[y]? <;> simp [he] at h
    split at h <;> simp_all
    cases h
    rename_i matched
    cases hm : context.elemTypes[y]? with
    | none =>
      exact .legacy (.tableInit ht he
        (Types.Algorithm.valMatches_sound (by simpa [hm] using matched)))
    | some type =>
      exact .legacy (.tableInitTyped ht hm
        (Types.Algorithm.valMatches_sound (by simpa [hm] using matched)))
  case unreachable => cases h; intro base output; exact .unreachable
  case throw_ x =>
    cases ht : context.tags[x]? <;> simp [ht] at h
    cases h
    intro base output
    exact .throw_ ht
  case throwRef =>
    cases h
    intro base output
    exact .throwRef
  case tryTable bt catches body =>
    cases ht : bt.resolve context.types <;> simp [ht] at h
    split at h <;> simp_all
    cases h
    rename_i valid
    exact .tryTable ht (fun c member => checkCatch_sound (valid.1 c member))
      (hb _ _ _ _ valid.2)
  case returnCall x =>
    cases hf : context.funcs[x]? <;> simp [hf] at h
    cases hr : context.returns <;> simp [hr] at h
    split at h <;> simp_all
    cases h
    intro base output
    exact .returnCall hf hr (Types.Algorithm.resultMatches_sound (by
      simpa [tailResultsMatch] using (by assumption :
      tailResultsMatch context _ _ = true)))
  case returnCallRef x =>
    cases hf : context.types.func? (x) <;> simp [hf] at h
    cases hr : context.returns <;> simp [hr] at h
    split at h <;> simp_all
    cases h
    intro base output
    exact .returnCallRef hf hr (Types.Algorithm.resultMatches_sound (by
      simpa [tailResultsMatch] using (by assumption :
      tailResultsMatch context _ _ = true)))
  case returnCallIndirect x y =>
    cases ht : context.tables[x]? <;> simp [ht] at h
    split at h <;> try simp_all
    cases hf : context.types.func? (y) <;> simp [hf] at h
    cases hr : context.returns <;> simp [hr] at h
    split at h <;> simp_all
    cases h
    intro base output
    simpa only [List.map_append, List.map_cons, List.map_nil] using
      (ValidationInstrTyping.returnCallIndirect (input := base) (output := output) ht
        (Types.Algorithm.heapMatches_sound (by assumption)) hf hr
        (Types.Algorithm.resultMatches_sound (by simpa [tailResultsMatch] using
          (by assumption : tailResultsMatch context _ _ = true))))
  case return_ =>
    cases hr : context.returns <;> simp [hr] at h
    cases h
    intro base output
    exact .return_ hr
  case br x =>
    cases hl : labels[x]? <;> simp [hl] at h
    cases h
    intro base output
    exact .br hl
  case brIf x =>
    cases hl : labels[x]? <;> simp [hl] at h
    cases h
    rename_i ts
    simpa only [BottomEffect.Typed, List.map_append] using
      (ValidationInstrTyping.legacy
        (RuntimeInstrTyping.plain (FunctionInstrTyping.plain (ControlInstrTyping.brIf hl))) :
        ValidationInstrTyping context labels (.brIf x)
          ((ts ++ [ValType.i32]).map Types.embedVal) (ts.map Types.embedVal))
  case brTable targets fallback =>
    cases hl : labels[fallback]? <;> simp [hl] at h
    rename_i ts
    split at h <;> simp_all
    rename_i checked
    cases h
    intro base output
    apply ValidationInstrTyping.brTableMatches
    intro x member
    have valid : branchTargetMatches context labels (branchArguments ts.length stack) x = true := by
      rcases List.mem_cons.mp member with rfl | member
      · exact checked.1
      · exact checked.2 x member
    cases hx : labels[x]? <;> simp [branchTargetMatches, hx] at valid
    exact ⟨_, rfl, Types.Algorithm.resultMatches_sound valid⟩
  case block bt body =>
    cases ht : bt.resolve context.types <;> simp [ht] at h
    split at h <;> simp_all
    cases h
    exact .block ht (hb _ _ _ _ (by assumption))
  case loop bt body =>
    cases ht : bt.resolve context.types <;> simp [ht] at h
    split at h <;> simp_all
    cases h
    exact .loop ht (hb _ _ _ _ (by assumption))
  case if_ bt yes no =>
    cases ht : bt.resolve context.types <;> simp [ht] at h
    split at h <;> simp_all
    cases h
    simpa only [BottomEffect.Typed, List.map_append] using
      (ValidationInstrTyping.if_ ht (hb _ _ _ _ (by exact And.left (by assumption)))
        (hb _ _ _ _ (by exact And.right (by assumption))))
  all_goals exact ordinaryBottomEffect_sound h

theorem checkBottomScoped_sound (h :
    checkBottomScoped fuel context labels code stack dead output = true) :
    ∃ padding, (dead = false → padding = []) ∧
      ValidationSeqTyping context labels code (padding ++ stack) output := by
  induction fuel generalizing context labels code stack dead output with
  | zero => cases h
  | succ fuel ih =>
    cases code with
    | nil =>
      simp only [checkBottomScoped] at h
      cases hc : consumeBottom ⟨context.definedTypes, []⟩ output stack dead <;> simp [hc] at h
      rename_i popped
      have base : popped.base = [] := h
      obtain ⟨split, typed, missing⟩ := consumeBottom_sound hc
      refine ⟨popped.missing, missing, ?_⟩
      rw [split, base, List.nil_append]
      exact .subtype .empty (validationResult_refl _ _) typed
    | cons i rest =>
      simp only [checkBottomScoped] at h
      cases he : bottomEffect context labels i stack
          (fun ls body input output => checkBottomScoped fuel context ls body input false output)
          <;> simp [he] at h
      rename_i eff
      have typed := bottomEffect_sound he (fun ls body input output success => by
        obtain ⟨padding, hp, derivation⟩ := ih success
        simpa [hp rfl] using derivation)
      cases eff with
      | normal required produced =>
        cases hc : consumeBottom ⟨context.definedTypes, []⟩ required stack dead <;> simp [hc] at h
        rename_i popped
        obtain ⟨padding, hp, tail⟩ := ih h
        obtain ⟨split, hmatches, missing⟩ := consumeBottom_sound hc
        refine ⟨padding ++ popped.missing, fun hd => by simp [hp hd, missing hd], ?_⟩
        have step : ValidationInstrTyping context labels i
            ((padding ++ popped.missing) ++ stack)
            (padding ++ (popped.base ++ produced)) := by
          have cast := ValidationInstrTyping.subtype typed hmatches
            (validationResult_refl _ produced)
          simpa only [List.append_assoc, split] using
            (ValidationInstrTyping.weaken (base := padding ++ popped.base) cast)
        exact .cons step tail
      | jump required =>
        cases hc : consumeBottom ⟨context.definedTypes, []⟩ required stack dead <;> simp [hc] at h
        rename_i popped
        obtain ⟨padding, _, tail⟩ := ih h
        obtain ⟨split, hmatches, missing⟩ := consumeBottom_sound hc
        refine ⟨popped.missing, missing, .cons ?_ (by simpa using tail)⟩
        rw [split]
        exact .subtype (typed popped.base padding)
          (validationResult_append (validationResult_refl _ popped.base) hmatches)
          (validationResult_refl _ padding)

theorem checkBottomCode_sound (h : checkBottomCode context code input output
    (labels := labels) = true) :
    ValidationSeqTyping context labels code
      (input.map Types.embedVal) (output.map Types.embedVal) := by
  obtain ⟨padding, hp, derivation⟩ := checkBottomScoped_sound h
  simpa [hp rfl] using derivation

private theorem unit_ok (h : (result : Result Unit).isOk = true) : result = .ok () := by
  cases result with
  | error _ => cases h
  | ok value => cases value; rfl

theorem checkSourceCode_sound (h : checkSourceCode context code input output labels = true) :
    RuntimeSeqTyping context labels code input output := by
  simp only [checkSourceCode, Bool.or_eq_true] at h
  rcases h with legacy | bottom
  · exact checkCode_sound (unit_ok legacy)
  · exact .validation (checkBottomCode_sound bottom)

theorem checkFunction_sound (h : checkFunction types context function = true) :
    ∃ ft, FuncTyping types context.funcs context.globals context.mems context.dataCount
      (tables := context.tables) (elems := context.elems)
      (declaredRefs := context.declaredRefs) function ft
      (definedTypes := context.definedTypes) (funcTypeIndices := context.funcTypeIndices)
      (elemTypes := context.elemTypes) (tags := context.tags) := by
  unfold checkFunction at h
  cases ht : types.func? (function.typeIdx) <;> simp [ht] at h
  rcases h.2 with legacy | bottom
  · exact ⟨_, .wasm ht h.1 (checkCode_sound (unit_ok legacy))⟩
  · exact ⟨_, .wasmValidation ht h.1 (checkBottomCode_sound bottom)⟩

private theorem defaultTableInit_sound (h : defaultTableInit kind code = true) :
    code = [.refNull kind] := by
  cases kind <;> cases code with
  | nil => simp [defaultTableInit] at h
  | cons i rest =>
    cases rest with
    | cons j rest => simp [defaultTableInit] at h
    | nil =>
      cases i <;> try { simp [defaultTableInit] at h }
      all_goals rename_i heap
      all_goals cases heap <;> simp_all [defaultTableInit]

theorem checkConstantInstruction_sound
    (h : checkConstantInstruction globals i = true) : ConstantInstr globals i := by
  cases i <;> simp only [checkConstantInstruction] at h
  all_goals try { cases h }
  case const v =>
    cases v <;> simp at h
    all_goals exact .const
  case arrayOp op =>
    cases op <;> simp at h
    · exact .arrayNew
    · exact .arrayNewFixed
  case structNew x default => exact .structNew
  case gcReference op =>
    cases op <;> simp at h
    · exact .i31
    · exact .anyConvertExtern
    · exact .externConvertAny
  case binop type op => exact .binop (integerType_sound h)
  case refNull kind => exact .refNull
  case refFunc x => exact .refFunc
  case globalGet x =>
    cases hg : globals[x]? <;> simp [hg] at h
    rename_i type
    cases type with
    | mk mutability valType =>
      cases mutability <;> simp at h
      exact .global hg

theorem checkTable_sound (h : checkTable context table = true) : TableTyping context table := by
  simp only [checkTable, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨h.1.1, checkSourceCode_sound h.1.2,
    fun i member => checkConstantInstruction_sound (h.2 i member)⟩

private theorem checkElemMode_sound (h : checkElemMode context type mode = true) :
    ElemModeTyping context type mode := by
  cases mode with
  | passive => exact .passive
  | declarative => exact .declarative
  | active x offset =>
    cases ht : context.tables[x]? <;> simp [checkElemMode, ht] at h
    refine .active ht ?_ (checkCode_sound (unit_ok h.1.2))
      (fun i member => checkConstantInstruction_sound (h.2 i member))
    exact Types.Algorithm.valMatches_sound h.1.1

theorem checkElem_sound (h : checkElem context elem = true) : ElemTyping context elem := by
  simp only [checkElem, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨fun code member => checkSourceCode_sound (h.1 code member).1,
    fun code member i hi => checkConstantInstruction_sound ((h.1 code member).2 i hi),
    checkElemMode_sound h.2⟩

theorem checkGlobals_sound (h : checkGlobals context globals = true) :
    GlobalSeqTyping context globals := by
  induction globals generalizing context with
  | nil => exact .empty
  | cons global rest ih =>
    simp only [checkGlobals, Bool.and_eq_true, List.all_eq_true] at h
    exact .cons (checkSourceCode_sound h.1.1)
      (fun i member => checkConstantInstruction_sound (h.1.2 i member)) (ih h.2)

theorem checkData_sound (h : checkData context data = true) : DataTyping context data := by
  cases data with
  | mk bytes mode =>
    cases mode with
    | passive => exact .passive
    | active x offset =>
      cases hm : context.mems[x]? <;> simp [checkData, hm] at h
      exact .active hm (checkCode_sound (unit_ok h.1))
        (fun i member => checkConstantInstruction_sound (h.2 i member))

private theorem checkImports_memories {module : Module}
    (h : module.imports.all (checkImport module.types) = true) :
    ∀ memory ∈ module.importedMemories, memory.Valid := by
  intro memory member
  obtain ⟨entry, member, he⟩ := List.mem_filterMap.mp member
  have hc := List.all_eq_true.mp h entry member
  cases hd : entry.desc <;> simp_all [checkImport]

private theorem checkImports_tables {module : Module}
    (h : module.imports.all (checkImport module.types) = true) :
    ∀ table ∈ module.importedTables, table.Valid := by
  intro table member
  obtain ⟨entry, member, he⟩ := List.mem_filterMap.mp member
  have hc := List.all_eq_true.mp h entry member
  cases hd : entry.desc <;> simp_all [checkImport]

private theorem context_types {module : Module} {context : FunctionContext}
    (h : module.context? = some context) :
    Types.resolveSection? [] module.typeGroups = some context.definedTypes := by
  unfold Module.context? at h
  cases hr : Types.resolveSection? [] module.typeGroups <;> simp [hr] at h
  cases hi : module.importedFuncIndices.mapM (fun x => module.types.func? (x)) <;> simp [hi] at h
  cases hf : module.funcs.mapM (fun function => module.types.func? (function.typeIdx)) <;>
    simp [hf] at h
  cases ht : module.importedTagIndices.mapM
      (tagSignature? module.types) <;> simp [ht] at h
  cases hd : module.tags.mapM (tagSignature? module.types) <;> simp [hd] at h
  cases h
  rfl

private theorem checkTypeGroups_sound (hc : module.context? = some context)
    (h : checkTypeGroups module = true) (nonempty : module.typeGroups ≠ []) :
    Types.TypeSectionValid [] module.typeGroups context.definedTypes ∧
      module.typeGroups.flatten.map Types.SubType.body = module.types.map Types.embedComposite := by
  have notEmpty : module.typeGroups.isEmpty = false := by simp [nonempty]
  simp only [checkTypeGroups, notEmpty, Bool.false_eq_true, ↓reduceIte,
    Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨final, resolution, valid⟩ := Types.Algorithm.typeSection_sound h.1
  have eq := (context_types hc).symm.trans resolution
  cases Option.some.inj eq
  exact ⟨valid, h.2⟩

theorem validate_sound (h : validate module = .ok ()) : module.Valid := by
  unfold validate at h
  split at h <;> try simp_all
  rename_i hs
  cases hc : module.context? <;> simp [hc] at h
  rename_i context
  have checks := h
  have shape := hs
  simp only [supportedModule, Bool.and_eq_true] at shape
  rcases shape with
    ⟨⟨⟨⟨⟨⟨⟨⟨hi, hg⟩, hm⟩, hd⟩, ht⟩, he⟩, hgroups⟩, _⟩, _⟩
  simp only [moduleChecks, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at checks
  rcases checks with ⟨checks, htypes⟩
  rcases checks with ⟨⟨checks, hmems⟩, hdatas⟩
  rcases checks with ⟨checks, hglobals⟩
  rcases checks with
    ⟨⟨⟨⟨⟨⟨⟨himports, hf⟩, hx⟩, hn⟩, hstart⟩, hscope⟩, htables⟩, helems⟩
  refine ⟨context, ⟨hc, ?_, ?_, ?_, ?_, ?_, hx, hn, hstart, ?_, ?_, ?_, ?_, hscope⟩⟩
  · exact checkImports_memories (List.all_eq_true.mpr himports)
  · exact hmems
  · exact checkGlobals_sound hglobals
  · intro function member
    exact checkFunction_sound (hf function member)
  · intro data member
    exact checkData_sound (hdatas data member)
  · exact checkImports_tables (List.all_eq_true.mpr himports)
  · intro table member
    exact checkTable_sound (htables table member)
  · intro elem member
    exact checkElem_sound (helems elem member)
  · exact checkTypeGroups_sound hc htypes

end Wasm.Validation
