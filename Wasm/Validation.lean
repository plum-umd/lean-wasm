import Wasm.Syntax

/-!
Instruction typing for the implemented fragment. These are declarative judgments;
they are not yet a module validator or a proof of type safety.
Source: https://webassembly.github.io/spec/core/valid/instructions.html
-/

namespace Wasm

/-- Stack types are in specification order, with the top at the right. -/
inductive InstrTyping : Instr → List ValType → List ValType → Prop where
  | const (ht : v.type.IsNumber := by trivial) : InstrTyping (.const v) [] [v.type]
  | nop : InstrTyping .nop [] []
  | unreachable : InstrTyping .unreachable input output
  | drop : InstrTyping .drop [t] []
  | select (ht : t.IsNumber := by trivial) : InstrTyping (.select none) [t, t, .i32] [t]
  | selectTyped : InstrTyping (.select (some [t])) [t, t, .i32] [t]
  | binop (ht : t.IsInteger := by trivial) : InstrTyping (.binop t op) [t, t] [t]
  | eqz (ht : t.IsInteger := by trivial) : InstrTyping (.eqz t) [t] [.i32]
  | intUnary (ht : t.IsInteger := by trivial) : InstrTyping (.intUnary t op) [t] [t]
  | intBinary (ht : t.IsInteger := by trivial) : InstrTyping (.intBinary t op) [t, t] [t]
  | intRel (ht : t.IsInteger := by trivial) : InstrTyping (.intRel t op) [t, t] [.i32]
  | intConvert : InstrTyping (.intConvert op) [op.inputType] [op.outputType]
  | floatUnary : InstrTyping (.floatUnary width op) [width.floatType] [width.floatType]
  | floatBinary : InstrTyping (.floatBinary width op)
      [width.floatType, width.floatType] [width.floatType]
  | floatRel : InstrTyping (.floatRel width op) [width.floatType, width.floatType] [.i32]
  | floatConvert : InstrTyping (.floatConvert op) [op.inputType] [op.outputType]
  | weaken : InstrTyping i input output →
      InstrTyping i (ts₀ ++ input) (ts₀ ++ output)

/-- Composition and stack weakening follow the specification's sequence judgments. -/
inductive SeqTyping : List Instr → List ValType → List ValType → Prop where
  | empty : SeqTyping [] ts ts
  | cons : InstrTyping i input middle → SeqTyping rest middle output →
      SeqTyping (i :: rest) input output
  | weaken : SeqTyping code input output →
      SeqTyping code (ts₀ ++ input) (ts₀ ++ output)

end Wasm
