import Wasm.TypeSyntax
namespace Wasm.Types
mutual
  def heapEq : (a b : HeapType) → Decidable (a = b)
    | .func , .func  => isTrue rfl
    | .func , .nofunc  => isFalse (by intro h; cases h)
    | .func , .extern  => isFalse (by intro h; cases h)
    | .func , .noextern  => isFalse (by intro h; cases h)
    | .func , .bot  => isFalse (by intro h; cases h)
    | .func , .typeIdx b0 => isFalse (by intro h; cases h)
    | .func , .recIdx b0 => isFalse (by intro h; cases h)
    | .func , .defined b0 b1 => isFalse (by intro h; cases h)
    | .nofunc , .func  => isFalse (by intro h; cases h)
    | .nofunc , .nofunc  => isTrue rfl
    | .nofunc , .extern  => isFalse (by intro h; cases h)
    | .nofunc , .noextern  => isFalse (by intro h; cases h)
    | .nofunc , .bot  => isFalse (by intro h; cases h)
    | .nofunc , .typeIdx b0 => isFalse (by intro h; cases h)
    | .nofunc , .recIdx b0 => isFalse (by intro h; cases h)
    | .nofunc , .defined b0 b1 => isFalse (by intro h; cases h)
    | .extern , .func  => isFalse (by intro h; cases h)
    | .extern , .nofunc  => isFalse (by intro h; cases h)
    | .extern , .extern  => isTrue rfl
    | .extern , .noextern  => isFalse (by intro h; cases h)
    | .extern , .bot  => isFalse (by intro h; cases h)
    | .extern , .typeIdx b0 => isFalse (by intro h; cases h)
    | .extern , .recIdx b0 => isFalse (by intro h; cases h)
    | .extern , .defined b0 b1 => isFalse (by intro h; cases h)
    | .noextern , .func  => isFalse (by intro h; cases h)
    | .noextern , .nofunc  => isFalse (by intro h; cases h)
    | .noextern , .extern  => isFalse (by intro h; cases h)
    | .noextern , .noextern  => isTrue rfl
    | .noextern , .bot  => isFalse (by intro h; cases h)
    | .noextern , .typeIdx b0 => isFalse (by intro h; cases h)
    | .noextern , .recIdx b0 => isFalse (by intro h; cases h)
    | .noextern , .defined b0 b1 => isFalse (by intro h; cases h)
    | .bot , .func  => isFalse (by intro h; cases h)
    | .bot , .nofunc  => isFalse (by intro h; cases h)
    | .bot , .extern  => isFalse (by intro h; cases h)
    | .bot , .noextern  => isFalse (by intro h; cases h)
    | .bot , .bot  => isTrue rfl
    | .bot , .typeIdx b0 => isFalse (by intro h; cases h)
    | .bot , .recIdx b0 => isFalse (by intro h; cases h)
    | .bot , .defined b0 b1 => isFalse (by intro h; cases h)
    | .typeIdx a0, .func  => isFalse (by intro h; cases h)
    | .typeIdx a0, .nofunc  => isFalse (by intro h; cases h)
    | .typeIdx a0, .extern  => isFalse (by intro h; cases h)
    | .typeIdx a0, .noextern  => isFalse (by intro h; cases h)
    | .typeIdx a0, .bot  => isFalse (by intro h; cases h)
    | .typeIdx a0, .typeIdx b0 => by
      exact decidable_of_iff (a0 = b0) (by simp)
    | .typeIdx a0, .recIdx b0 => isFalse (by intro h; cases h)
    | .typeIdx a0, .defined b0 b1 => isFalse (by intro h; cases h)
    | .recIdx a0, .func  => isFalse (by intro h; cases h)
    | .recIdx a0, .nofunc  => isFalse (by intro h; cases h)
    | .recIdx a0, .extern  => isFalse (by intro h; cases h)
    | .recIdx a0, .noextern  => isFalse (by intro h; cases h)
    | .recIdx a0, .bot  => isFalse (by intro h; cases h)
    | .recIdx a0, .typeIdx b0 => isFalse (by intro h; cases h)
    | .recIdx a0, .recIdx b0 => by
      exact decidable_of_iff (a0 = b0) (by simp)
    | .recIdx a0, .defined b0 b1 => isFalse (by intro h; cases h)
    | .defined a0 a1, .func  => isFalse (by intro h; cases h)
    | .defined a0 a1, .nofunc  => isFalse (by intro h; cases h)
    | .defined a0 a1, .extern  => isFalse (by intro h; cases h)
    | .defined a0 a1, .noextern  => isFalse (by intro h; cases h)
    | .defined a0 a1, .bot  => isFalse (by intro h; cases h)
    | .defined a0 a1, .typeIdx b0 => isFalse (by intro h; cases h)
    | .defined a0 a1, .recIdx b0 => isFalse (by intro h; cases h)
    | .defined a0 a1, .defined b0 b1 => by
      letI : Decidable (a0 = b0) := subListEq a0 b0
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  def valEq : (a b : ValType) → Decidable (a = b)
    | .i32, .f32 => isFalse (by intro h; cases h)
    | .i32, .f64 => isFalse (by intro h; cases h)
    | .i64, .f32 => isFalse (by intro h; cases h)
    | .i64, .f64 => isFalse (by intro h; cases h)
    | .f32, .i32 => isFalse (by intro h; cases h)
    | .f32, .i64 => isFalse (by intro h; cases h)
    | .f32, .f32 => isTrue rfl
    | .f32, .f64 => isFalse (by intro h; cases h)
    | .f32, .bot => isFalse (by intro h; cases h)
    | .f32, .ref _ _ => isFalse (by intro h; cases h)
    | .f64, .i32 => isFalse (by intro h; cases h)
    | .f64, .i64 => isFalse (by intro h; cases h)
    | .f64, .f32 => isFalse (by intro h; cases h)
    | .f64, .f64 => isTrue rfl
    | .f64, .bot => isFalse (by intro h; cases h)
    | .f64, .ref _ _ => isFalse (by intro h; cases h)
    | .bot, .f32 => isFalse (by intro h; cases h)
    | .bot, .f64 => isFalse (by intro h; cases h)
    | .ref _ _, .f32 => isFalse (by intro h; cases h)
    | .ref _ _, .f64 => isFalse (by intro h; cases h)
    | .i32 , .i32  => isTrue rfl
    | .i32 , .i64  => isFalse (by intro h; cases h)
    | .i32 , .bot  => isFalse (by intro h; cases h)
    | .i32 , .ref b0 b1 => isFalse (by intro h; cases h)
    | .i64 , .i32  => isFalse (by intro h; cases h)
    | .i64 , .i64  => isTrue rfl
    | .i64 , .bot  => isFalse (by intro h; cases h)
    | .i64 , .ref b0 b1 => isFalse (by intro h; cases h)
    | .bot , .i32  => isFalse (by intro h; cases h)
    | .bot , .i64  => isFalse (by intro h; cases h)
    | .bot , .bot  => isTrue rfl
    | .bot , .ref b0 b1 => isFalse (by intro h; cases h)
    | .ref a0 a1, .i32  => isFalse (by intro h; cases h)
    | .ref a0 a1, .i64  => isFalse (by intro h; cases h)
    | .ref a0 a1, .bot  => isFalse (by intro h; cases h)
    | .ref a0 a1, .ref b0 b1 => by
      letI : Decidable (a1 = b1) := heapEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  def subEq : (a b : SubType) → Decidable (a = b)
    | .func a0 a1 a2 a3, .func b0 b1 b2 b3 => by
      letI : Decidable (a1 = b1) := heapListEq a1 b1
      letI : Decidable (a2 = b2) := valListEq a2 b2
      letI : Decidable (a3 = b3) := valListEq a3 b3
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp)
  def subListEq : (a b : List SubType) → Decidable (a = b)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | a :: as, b :: bs => by
      letI : Decidable (a = b) := subEq a b
      letI : Decidable (as = bs) := subListEq as bs
      exact decidable_of_iff (a = b ∧ as = bs) (by simp)
  def heapListEq : (a b : List HeapType) → Decidable (a = b)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | a :: as, b :: bs => by
      letI : Decidable (a = b) := heapEq a b
      letI : Decidable (as = bs) := heapListEq as bs
      exact decidable_of_iff (a = b ∧ as = bs) (by simp)
  def valListEq : (a b : List ValType) → Decidable (a = b)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
    | a :: as, b :: bs => by
      letI : Decidable (a = b) := valEq a b
      letI : Decidable (as = bs) := valListEq as bs
      exact decidable_of_iff (a = b ∧ as = bs) (by simp)
end
instance : DecidableEq HeapType := heapEq
instance : DecidableEq ValType := valEq
instance : DecidableEq SubType := subEq
deriving instance DecidableEq for RefType, FuncType, DefinedType
end Wasm.Types
