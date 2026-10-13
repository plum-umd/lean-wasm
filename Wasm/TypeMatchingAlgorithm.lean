import Wasm.TypeChecking
import Wasm.TypeEquality

namespace Wasm.Types.Algorithm

/-- Ordinary boolean matching. Successful checks are justified in a separate theorem. -/
def heapMatches : Nat → Context → HeapType → HeapType → Bool
  | 0, _, _, _ => false
  | fuel + 1, ctx, a, b =>
    if a = b then true else match a, b with
    | .bot, _ => true
    | .typeIdx x, b => match ctx.types[x]? with
      | some type => heapMatches fuel ctx type.heap b
      | none => false
    | a, .typeIdx x => match ctx.types[x]? with
      | some type => heapMatches fuel ctx a type.heap
      | none => false
    | .defined group index, .func => (DefinedType.mk group index).expand?.isSome
    | .defined group index, .defined target j =>
      let src : DefinedType := ⟨group, index⟩
      let dst : DefinedType := ⟨target, j⟩
      match src.close? ctx.types, dst.close? ctx.types with
      | some left, some right =>
        if left = right then true else match src.unroll? with
        | some sub => sub.supers.any (fun parent => heapMatches fuel ctx parent dst.heap)
        | none => false
      | _, _ => false
    | .defined group index, b => match (DefinedType.mk group index).expandComposite? with
      | some comp => heapMatches fuel ctx comp.heap b
      | none => false
    | .eq, .any | .i31, .eq | .i31, .any | .struct_, .eq | .struct_, .any
      | .array, .eq | .array, .any => true
    | .none, b => decide (b ≠ .bot) && heapMatches fuel ctx b .any
    | .nofunc, b => decide (b ≠ .bot) && heapMatches fuel ctx b .func
    | .noextern, b => decide (b ≠ .bot) && heapMatches fuel ctx b .extern
    | .noexn, b => decide (b ≠ .bot) && heapMatches fuel ctx b .exn
    | .recIdx i, b@(.func) | .recIdx i, b@(.struct_) | .recIdx i, b@(.array)
      | .recIdx i, b@(.eq) | .recIdx i, b@(.any) => match ctx.recs[i]? with
      | some sub => heapMatches fuel ctx sub.body.heap b
      | none => false
    | .recIdx i, b => match ctx.recs[i]? with
      | none => false
      | some sub => sub.supers.any fun parent =>
        if parent = b then true else
          (checkHeapValid fuel ctx parent).isSome &&
            heapMatches fuel ctx parent b
    | _, _ => false

def valMatches (fuel : Nat) (ctx : Context) (a b : ValType) : Bool :=
  match a, b with
  | .i32, .i32 | .i64, .i64 | .f32, .f32 | .f64, .f64 | .v128, .v128 | .bot, _ => true
  | .ref na ha, .ref nb hb =>
    decide (na = true → nb = true) && heapMatches fuel ctx ha hb
  | _, _ => false

def resultMatches (fuel : Nat) (ctx : Context) : List ValType → List ValType → Bool
  | [], [] => true
  | a :: as, b :: bs => valMatches fuel ctx a b && resultMatches fuel ctx as bs
  | _, _ => false

def budget (ctx : Context) (a b : ValType) : Nat :=
  let contextWeight := (ctx.types.map (fun t => t.heap.weight)).foldl (· + ·) 0 +
    (ctx.recs.map SubType.weight).foldl (· + ·) 0
  (contextWeight + a.weight + b.weight + 1)^2

theorem heapMatches_sound (h : heapMatches fuel ctx a b = true) : HeapMatches ctx a b := by
  induction fuel generalizing a b with
  | zero => cases h
  | succ fuel ih =>
    unfold heapMatches at h
    split at h
    · subst b; exact .refl
    · cases a <;> cases b <;> simp only [Bool.false_eq_true, Bool.and_eq_true] at h
      all_goals try contradiction
      all_goals try exact .bot
      all_goals try {
        split at h <;> try contradiction
        exact .indexLeft (by assumption) (ih h) }
      all_goals try {
        split at h <;> try contradiction
        exact .indexRight (by assumption) (ih h) }
      case defined.func group index =>
        obtain ⟨body, expanded⟩ := Option.isSome_iff_exists.mp h
        exact .definedFunc expanded
      case defined.defined group index target j =>
        split at h <;> try contradiction
        rename_i left right ca cb
        split at h
        · rename_i same
          exact .defined (.same ca (same.symm ▸ cb))
        · split at h <;> try contradiction
          rename_i sub expanded
          obtain ⟨parent, member, matched⟩ := List.any_eq_true.mp h
          exact .defined (.super expanded member (ih matched))
      case eq.any => exact .eqAny
      case i31.eq => exact .i31Eq
      case struct_.eq => exact .structEq
      case array.eq => exact .arrayEq
      case i31.any => exact .trans (middle := .eq) (.abstract (by simp)) .i31Eq .eqAny
      case struct_.any =>
        exact .trans (middle := .eq) (.abstract (by simp)) .structEq .eqAny
      case array.any =>
        exact .trans (middle := .eq) (.abstract (by simp)) .arrayEq .eqAny
      case nofunc.func | nofunc.extern | nofunc.noextern | nofunc.exn |
          nofunc.noexn | nofunc.bot | nofunc.any | nofunc.eq |
          nofunc.i31 | nofunc.struct_ | nofunc.array | nofunc.none |
          nofunc.recIdx | nofunc.defined =>
        exact .nofunc (ih h.2) (by simp_all)
      case noextern.func | noextern.nofunc | noextern.extern | noextern.exn |
          noextern.noexn | noextern.bot | noextern.any | noextern.eq |
          noextern.i31 | noextern.struct_ | noextern.array | noextern.none |
          noextern.recIdx | noextern.defined =>
        exact .noextern (ih h.2) (by simp_all)
      case noexn.func | noexn.nofunc | noexn.extern | noexn.noextern |
          noexn.exn | noexn.bot | noexn.any | noexn.eq |
          noexn.i31 | noexn.struct_ | noexn.array | noexn.none |
          noexn.recIdx | noexn.defined =>
        exact .noexn (ih h.2) (by simp_all)
      case none.func | none.nofunc | none.extern | none.noextern |
          none.exn | none.noexn | none.bot | none.any |
          none.eq | none.i31 | none.struct_ | none.array |
          none.recIdx | none.defined =>
        exact .none (ih h.2) (by simp_all)
      case defined.struct_ group index =>
        split at h <;> try contradiction
        exact .definedComp (by assumption) (ih h)
      case defined.array group index =>
        split at h <;> try contradiction
        exact .definedComp (by assumption) (ih h)
      case defined.eq group index =>
        split at h <;> try contradiction
        exact .definedComp (by assumption) (ih h)
      case defined.any group index =>
        split at h <;> try contradiction
        exact .definedComp (by assumption) (ih h)
      case defined.nofunc group index =>
        split at h <;> try contradiction
        exact .definedComp (by assumption) (ih h)
      case defined.extern group index =>
        split at h <;> try contradiction
        exact .definedComp (by assumption) (ih h)
      case defined.noextern group index =>
        split at h <;> try contradiction
        exact .definedComp (by assumption) (ih h)
      case defined.exn group index =>
        split at h <;> try contradiction
        exact .definedComp (by assumption) (ih h)
      case defined.noexn group index =>
        split at h <;> try contradiction
        exact .definedComp (by assumption) (ih h)
      case defined.bot group index =>
        split at h <;> try contradiction
        exact .definedComp (by assumption) (ih h)
      case defined.i31 group index =>
        split at h <;> try contradiction
        exact .definedComp (by assumption) (ih h)
      case defined.none group index =>
        split at h <;> try contradiction
        exact .definedComp (by assumption) (ih h)
      case defined.recIdx group index =>
        split at h <;> try contradiction
        exact .definedComp (by assumption) (ih h)
      case recIdx.func index =>
        split at h <;> try contradiction
        exact .recComp (by assumption) (ih h)
      case recIdx.struct_ index =>
        split at h <;> try contradiction
        exact .recComp (by assumption) (ih h)
      case recIdx.array index =>
        split at h <;> try contradiction
        exact .recComp (by assumption) (ih h)
      case recIdx.eq index =>
        split at h <;> try contradiction
        exact .recComp (by assumption) (ih h)
      case recIdx.any index =>
        split at h <;> try contradiction
        exact .recComp (by assumption) (ih h)
      all_goals
        split at h <;> try contradiction
        rename_i sub lookup
        obtain ⟨parent, member, matched⟩ := List.any_eq_true.mp h
        split at matched
        · rename_i same
          exact .recSuper lookup (same ▸ member)
        · simp only [Bool.and_eq_true] at matched
          obtain ⟨valid, success⟩ := matched
          exact .trans (checkHeapValid_sound valid) (.recSuper lookup member) (ih success)

theorem valMatches_sound (h : valMatches fuel ctx a b = true) : ValMatches ctx a b := by
  cases a <;> cases b <;> simp only [valMatches, Bool.and_eq_true, Bool.false_eq_true] at h
  all_goals try contradiction
  all_goals try exact .bot
  all_goals try exact .i32
  all_goals try exact .i64
  all_goals try exact .f32
  all_goals try exact .f64
  all_goals try exact .v128
  case ref.ref na ha nb hb =>
    exact .ref (a := ⟨na, ha⟩) (b := ⟨nb, hb⟩)
      ⟨of_decide_eq_true h.1, heapMatches_sound h.2⟩

theorem resultMatches_sound (h : resultMatches fuel ctx as bs = true) :
    ResultMatches ctx as bs := by
  induction as generalizing bs with
  | nil =>
    cases bs with
    | nil => exact .nil
    | cons _ _ => cases h
  | cons a as ih =>
    cases bs with
    | nil => cases h
    | cons b bs =>
      simp only [resultMatches, Bool.and_eq_true] at h
      exact .cons (valMatches_sound h.1) (ih h.2)

end Wasm.Types.Algorithm
