import Wasm.TypeSafety.Integers
import Wasm.Control

namespace Wasm.TypeSafety

/-- Administrative typing for the flat fragment. Trap has a polymorphic stack effect. -/
inductive FlatInstrTyping : AdminInstr → List ValType → List ValType → Prop where
  | source : InstrTyping i input output → FlatInstrTyping (.instr i) input output
  | trap : FlatInstrTyping .trap input output

inductive FlatTyping : List AdminInstr → List ValType → List ValType → Prop where
  | nil : FlatTyping [] ts ts
  | cons : FlatInstrTyping i input middle → FlatTyping rest middle output →
      FlatTyping (i :: rest) input output

theorem FlatInstrTyping.weaken {stackBelow : List ValType} (h : FlatInstrTyping i input output) :
    FlatInstrTyping i (stackBelow ++ input) (stackBelow ++ output) := by
  cases h with
  | source h => exact .source (.weaken h)
  | trap => exact .trap

theorem FlatTyping.weaken {stackBelow : List ValType} (h : FlatTyping code input output) :
    FlatTyping code (stackBelow ++ input) (stackBelow ++ output) := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h.weaken ih

theorem FlatTyping.append (h : FlatTyping a input middle) (tail : FlatTyping b middle output) :
    FlatTyping (a ++ b) input output := by
  induction h with
  | nil => exact tail
  | cons h _ ih => exact .cons h (ih tail)

theorem FlatTyping.split (h : FlatTyping (a ++ b) input output) :
    ∃ middle, FlatTyping a input middle ∧ FlatTyping b middle output := by
  induction a generalizing input with
  | nil => exact ⟨input, .nil, h⟩
  | cons i a ih =>
    cases h with
    | cons head tail =>
      obtain ⟨middle, left, right⟩ := ih tail
      exact ⟨middle, .cons head left, right⟩

theorem SeqTyping.toFlatTyping (h : SeqTyping code input output) :
    FlatTyping (instructions code) input output := by
  induction h with
  | empty => exact .nil
  | cons h _ ih => exact .cons (.source h) ih
  | weaken _ ih => exact ih.weaken

@[simp] theorem FlatTyping.nil_iff : FlatTyping [] input output ↔ input = output := by
  constructor
  · intro h; cases h; rfl
  · intro h; subst output; exact .nil

@[simp] theorem FlatTyping.single_iff :
    FlatTyping [.instr i] input output ↔ InstrTyping i input output := by
  constructor
  · intro h
    cases h with
    | cons head tail =>
      cases tail
      cases head with
      | source h => exact h
  · intro h; exact .cons (.source h) .nil

theorem const_shape (h : InstrTyping (.const v) input output) :
    output = input ++ [v.type] ∧ v.type.IsNumber := by
  generalize hi : Instr.const v = i at h
  induction h with
  | const hn => cases hi; exact ⟨rfl, hn⟩
  | weaken _ ih =>
    obtain ⟨shape, hn⟩ := ih hi
    exact ⟨by simp [shape, List.append_assoc], hn⟩
  | _ => cases hi

@[simp] theorem FlatTyping.const_cons_iff :
    FlatTyping (.instr (.const v) :: rest) input output ↔
      v.type.IsNumber ∧ FlatTyping rest (input ++ [v.type]) output := by
  constructor
  · intro h
    cases h with
    | cons head tail =>
      cases head with
      | source h =>
        obtain ⟨shape, hn⟩ := const_shape h
        exact ⟨hn, shape ▸ tail⟩
  · rintro ⟨hn, tail⟩
    exact .cons (.source (by simpa using InstrTyping.weaken (ts₀ := input) (.const hn))) tail

theorem FlatTyping.values_typed (hn : ∀ v ∈ vs, v.type.IsNumber) :
    FlatTyping (values vs) input (input ++ vs.map Value.type) := by
  induction vs generalizing input with
  | nil => simp [values]
  | cons v vs ih =>
    simp only [values, List.map_cons, FlatTyping.const_cons_iff]
    refine ⟨hn v (by simp), ?_⟩
    simpa [values, List.append_assoc] using
      ih (input := input ++ [v.type]) (fun w hw => hn w (by simp [hw]))

/-- Exact stack effects for fixed-signature instructions; parametric instructions are separate. -/
def fixedSignature : Instr → Option FuncType
  | .const v => some ⟨[], [v.type]⟩
  | .nop => some ⟨[], []⟩
  | .binop t _ | .intBinary t _ => some ⟨[t, t], [t]⟩
  | .eqz t => some ⟨[t], [.i32]⟩
  | .intRel t _ => some ⟨[t, t], [.i32]⟩
  | .intUnary t _ => some ⟨[t], [t]⟩
  | .intConvert op => some ⟨[op.inputType], [op.outputType]⟩
  | _ => none

theorem fixed_shape (h : InstrTyping i input output) (hs : fixedSignature i = some ft) :
    ∃ stackBelow, input = stackBelow ++ ft.params ∧ output = stackBelow ++ ft.results := by
  induction h with
  | @weaken i input output ts₀ _ ih =>
    obtain ⟨stackBelow, hi, ho⟩ := ih hs
    exact ⟨ts₀ ++ stackBelow, by simp [hi, List.append_assoc],
      by simp [ho, List.append_assoc]⟩
  | _ => simp only [fixedSignature, Option.some.injEq] at hs <;> cases hs <;>
         exact ⟨[], rfl, rfl⟩

theorem fixed_output (h : InstrTyping i (stackBelow ++ args) output)
    (hs : fixedSignature i = some ft) (ha : args.length = ft.params.length) :
    args = ft.params ∧ output = stackBelow ++ ft.results := by
  obtain ⟨other, hi, ho⟩ := fixed_shape h hs
  have hl := congrArg List.length hi
  simp only [List.length_append] at hl
  have he : stackBelow.length = other.length := by omega
  obtain ⟨hpre, hargs⟩ := List.append_inj hi he
  exact ⟨hargs, hpre ▸ ho⟩

theorem drop_shape (h : InstrTyping .drop input output) : ∃ t, input = output ++ [t] := by
  generalize hi : Instr.drop = i at h
  induction h with
  | drop => cases hi; exact ⟨_, rfl⟩
  | weaken _ ih =>
    obtain ⟨t, shape⟩ := ih hi
    exact ⟨t, by simp [shape, List.append_assoc]⟩
  | _ => cases hi

theorem select_shape (h : InstrTyping (.select types) input output) :
    ∃ stackBelow t, input = stackBelow ++ [t, t, .i32] ∧ output = stackBelow ++ [t] := by
  generalize hi : Instr.select types = i at h
  induction h with
  | select | selectTyped => cases hi; exact ⟨[], _, rfl, rfl⟩
  | @weaken i input output ts₀ _ ih =>
    obtain ⟨stackBelow, t, ha, ho⟩ := ih hi
    exact ⟨ts₀ ++ stackBelow, t, by simp [ha, List.append_assoc],
      by simp [ho, List.append_assoc]⟩
  | _ => cases hi

theorem FlatTyping.trapped : FlatTyping [.trap] input output := .cons .trap .nil

theorem typed_value (hn : v.type.IsNumber) : FlatTyping (values [v]) input (input ++ [v.type]) :=
  FlatTyping.values_typed (by simpa)

end Wasm.TypeSafety
