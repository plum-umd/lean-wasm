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
    cases hf : context.types[y]? <;> simp [hf] at h
    rcases h with ⟨rfl, rfl⟩
    exact .tables (.indirect ht (funcHeap_sound (by assumption)) hf)
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

private theorem unit_ok (h : (result : Result Unit).isOk = true) : result = .ok () := by
  cases result with
  | error _ => cases h
  | ok value => cases value; rfl

theorem checkFunction_sound (h : checkFunction types context function = true) :
    ∃ ft, FuncTyping types context.funcs context.globals context.mems context.dataCount
      (tables := context.tables) (elems := context.elems)
      (declaredRefs := context.declaredRefs) function ft
      (definedTypes := context.definedTypes) (funcTypeIndices := context.funcTypeIndices)
      (elemTypes := context.elemTypes) := by
  unfold checkFunction at h
  cases ht : types[function.typeIdx]? <;> simp [ht] at h
  exact ⟨_, .wasm ht h.1 (checkCode_sound (unit_ok h.2))⟩

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
  exact ⟨h.1.1, checkCode_sound (unit_ok h.1.2),
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
    rw [h.1.1]
    exact Types.embed_matches _ _

theorem checkElem_sound (h : checkElem context elem = true) : ElemTyping context elem := by
  simp only [checkElem, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨fun code member => checkCode_sound (unit_ok (h.1 code member).1),
    fun code member i hi => checkConstantInstruction_sound ((h.1 code member).2 i hi),
    checkElemMode_sound h.2⟩

theorem checkGlobals_sound (h : checkGlobals context globals = true) :
    GlobalSeqTyping context globals := by
  induction globals generalizing context with
  | nil => exact .empty
  | cons global rest ih =>
    simp only [checkGlobals, Bool.and_eq_true, List.all_eq_true] at h
    exact .cons (checkCode_sound (unit_ok h.1.1))
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

theorem validate_sound (h : validate module = .ok ()) : module.Valid := by
  unfold validate at h
  split at h <;> try simp_all
  rename_i hs
  cases hc : module.context? <;> simp [hc] at h
  rename_i context
  have checks := h
  have shape := hs
  simp only [supportedModule, Bool.and_eq_true, List.isEmpty_iff] at shape
  rcases shape with
    ⟨⟨⟨⟨⟨⟨⟨⟨hi, hg⟩, hm⟩, hd⟩, ht⟩, he⟩, hgroups⟩, _⟩, _⟩
  simp only [moduleChecks, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at checks
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
  · simp [hgroups]

end Wasm.Validation
