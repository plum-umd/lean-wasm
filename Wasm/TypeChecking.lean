import Wasm.TypeMatching
import Wasm.TypeEquality

namespace Wasm.Types

abbrev Checked (p : Prop) := Option (PLift p)

/-- Rejection and exhausted search are distinct; successful search carries a derivation. -/
inductive Search (p : Prop) where
  | found (proof : PLift p)
  | rejected
  | inconclusive

def Search.map (f : PLift p → PLift q) : Search p → Search q
  | .found proof => .found (f proof)
  | .rejected => .rejected
  | .inconclusive => .inconclusive

def Search.toOption : Search p → Checked p
  | .found proof => some proof
  | _ => none

def Search.isRejected : Search p → Bool
  | .rejected => true
  | _ => false

private def findSearch (f : α → Search p) : List α → Search p
  | [] => .rejected
  | x :: xs => match f x with
    | .found proof => .found proof
    | .rejected => findSearch f xs
    | .inconclusive => match findSearch f xs with
      | .found proof => .found proof
      | _ => .inconclusive

/-- A successful branch is retained even when other branches exhaust their search. -/
private theorem findSearch_complete {f : α → Search p} {xs : List α}
    (success : ∃ x ∈ xs, (f x).toOption.isSome = true) :
    (findSearch f xs).toOption.isSome = true := by
  induction xs with
  | nil => simp at success
  | cons x xs ih =>
    obtain ⟨chosen, member, found⟩ := success
    rcases List.mem_cons.mp member with same | member
    · subst chosen
      cases result : f x <;> simp [result, Search.toOption] at found
      simp [findSearch, result, Search.toOption]
    · have tail := ih ⟨chosen, member, found⟩
      cases result : f x
      · simp [findSearch, result, Search.toOption]
      · simpa [findSearch, result] using tail
      · cases rest : findSearch f xs <;> simp [rest, Search.toOption] at tail
        simp [findSearch, result, rest, Search.toOption]

mutual
  def HeapType.weight : HeapType → Nat
    | .defined group index => 1 + index + (group.map SubType.weight).foldl (· + ·) 0
    | _ => 1
  def ValType.weight : ValType → Nat
    | .ref _ heap => 1 + heap.weight
    | _ => 1
  def StorageType.weight : StorageType → Nat
    | .val type => 1 + type.weight
    | _ => 1
  def FieldType.weight : FieldType → Nat
    | .mk type _ => 1 + type.weight
  def SubType.weight : SubType → Nat
    | .func _ supers params results => 1 +
      (supers.map HeapType.weight).foldl (· + ·) 0 +
      (params.map ValType.weight).foldl (· + ·) 0 +
      (results.map ValType.weight).foldl (· + ·) 0
    | .struct_ _ supers fields => 1 +
      (supers.map HeapType.weight).foldl (· + ·) 0 +
      (fields.map FieldType.weight).foldl (· + ·) 0
    | .array _ supers field => 1 +
      (supers.map HeapType.weight).foldl (· + ·) 0 + field.weight
end

/-- A size-derived search budget for closed runtime types; not a completeness theorem. -/
def matchingBudget (a b : HeapType) : Nat := (a.weight + b.weight + 1) ^ 2

/-- Certify every member without treating failed bounded search as a proof of invalidity. -/
private def checkAll {p : α → Prop} (check : (a : α) → Checked (p a)) :
    (xs : List α) → Checked (∀ a ∈ xs, p a)
  | [] => some ⟨by simp⟩
  | x :: xs => do
    let head ← check x
    let tail ← checkAll check xs
    return ⟨by intro a member; cases member with
      | head => exact head.down
      | tail _ member => exact tail.down a member⟩

private def checkValWith (heap : (a b : HeapType) → Checked (HeapMatches ctx a b))
    (a b : ValType) : Checked (ValMatches ctx a b) := by
  match a, b with
  | .i32, .i32 => exact some ⟨.i32⟩
  | .i64, .i64 => exact some ⟨.i64⟩
  | .f32, .f32 => exact some ⟨.f32⟩
  | .f64, .f64 => exact some ⟨.f64⟩
  | .v128, .v128 => exact some ⟨.v128⟩
  | .bot, _ => exact some ⟨.bot⟩
  | .ref na ha, .ref nb hb =>
    if nullable : na = true → nb = true then
      exact (heap ha hb).map fun h =>
        ⟨.ref (a := ⟨na, ha⟩) (b := ⟨nb, hb⟩) ⟨nullable, h.down⟩⟩
    else exact none
  | _, _ => exact none

private def checkResultsWith (val : (a b : ValType) → Checked (ValMatches ctx a b)) :
    (as bs : List ValType) → Checked (ResultMatches ctx as bs)
  | [], [] => some ⟨.nil⟩
  | a :: as, b :: bs => do
    let head ← val a b
    let tail ← checkResultsWith val as bs
    return ⟨.cons head.down tail.down⟩
  | _, _ => none

private def checkStorageWith (val : (a b : ValType) → Checked (ValMatches ctx a b))
    (a b : StorageType) : Checked (StorageMatches ctx a b) :=
  match a, b with
  | .i8, .i8 => some ⟨.i8⟩
  | .i16, .i16 => some ⟨.i16⟩
  | .val a, .val b => (val a b).map fun h => ⟨.val h.down⟩
  | _, _ => none

private def checkFieldWith (val : (a b : ValType) → Checked (ValMatches ctx a b))
    (a b : FieldType) : Checked (FieldMatches ctx a b) := do
  if same : a.mutable = b.mutable then
    let covariant ← checkStorageWith val a.storage b.storage
    if mutable : a.mutable = true then
      let invariant ← checkStorageWith val b.storage a.storage
      return ⟨⟨same, covariant.down, fun _ => invariant.down⟩⟩
    else return ⟨⟨same, covariant.down, fun h => False.elim (mutable h)⟩⟩
  else none

private def checkFieldsWith (val : (a b : ValType) → Checked (ValMatches ctx a b)) :
    (as bs : List FieldType) → Checked (FieldsMatches ctx as bs)
  | _, [] => some ⟨.nil⟩
  | a :: as, b :: bs => do
    let head ← checkFieldWith val a b
    let tail ← checkFieldsWith val as bs
    return ⟨.cons head.down tail.down⟩
  | _, _ => none

private def checkCompWith (heap : (a b : HeapType) → Checked (HeapMatches ctx a b))
    (a b : CompType) : Checked (CompMatches ctx a b) := do
  let val := checkValWith heap
  match a, b with
  | .func a, .func b =>
    let params ← checkResultsWith val b.params a.params
    let results ← checkResultsWith val a.results b.results
    return ⟨.func ⟨params.down, results.down⟩⟩
  | .struct_ a, .struct_ b =>
    let fields ← checkFieldsWith val a b
    return ⟨.struct_ fields.down⟩
  | .array a, .array b =>
    let field ← checkFieldWith val a b
    return ⟨.array field.down⟩
  | _, _ => none

mutual
/-- Search follows identity and declared edges; exhausted branches remain inconclusive. -/
def searchHeap : Nat → (ctx : Context) → (a b : HeapType) → Search (HeapMatches ctx a b)
  | 0, _, _, _ => .inconclusive
  | fuel + 1, ctx, a, b => by
    if same : a = b then
      subst b
      exact Search.found ⟨.refl⟩
    else
      match a, b with
      | .bot, _ => exact Search.found ⟨.bot⟩
      | .typeIdx x, b =>
        match lookup : ctx.types[x]? with
        | none => exact .rejected
        | some type =>
          exact (searchHeap fuel ctx type.heap b).map fun h => ⟨.indexLeft lookup h.down⟩
      | a, .typeIdx x =>
        match lookup : ctx.types[x]? with
        | none => exact .rejected
        | some type =>
          exact (searchHeap fuel ctx a type.heap).map fun h => ⟨.indexRight lookup h.down⟩
      | .defined group index, .func =>
        match expanded : (DefinedType.mk group index).expand? with
        | none => exact .rejected
        | some body => exact Search.found ⟨.definedFunc expanded⟩
      | .defined group index, .defined target j =>
        let src : DefinedType := ⟨group, index⟩
        let dst : DefinedType := ⟨target, j⟩
        match ca : src.close? ctx.types, cb : dst.close? ctx.types with
        | some left, some right =>
          if eq : left = right then
            exact Search.found ⟨.defined (a := src) (b := dst) (.same ca (eq.symm ▸ cb))⟩
          else
            match expanded : src.unroll? with
            | none => exact .rejected
            | some sub =>
              exact findSearch (fun parent =>
                (searchHeap fuel ctx parent.val dst.heap).map fun h =>
                  ⟨.defined (.super expanded parent.property h.down)⟩) sub.supers.attach
        | _, _ => exact .rejected
      | .defined group index, b =>
        match expanded : (DefinedType.mk group index).expandComposite? with
        | none => exact .rejected
        | some comp => exact (searchHeap fuel ctx comp.heap b).map fun h =>
            ⟨.definedComp expanded h.down⟩
      | .eq, .any => exact .found ⟨.eqAny⟩
      | .i31, .eq => exact .found ⟨.i31Eq⟩
      | .struct_, .eq => exact .found ⟨.structEq⟩
      | .array, .eq => exact .found ⟨.arrayEq⟩
      | .i31, .any => exact .found ⟨.trans (middle := .eq) (.abstract (by simp)) .i31Eq .eqAny⟩
      | .struct_, .any =>
        exact .found ⟨.trans (middle := .eq) (.abstract (by simp)) .structEq .eqAny⟩
      | .array, .any => exact .found ⟨.trans (middle := .eq) (.abstract (by simp)) .arrayEq .eqAny⟩
      | .none, b =>
        if bottom : b = .bot then exact .rejected
        else exact (searchHeap fuel ctx b .any).map fun h => ⟨.none h.down bottom⟩
      | .nofunc, b =>
        if bottom : b = .bot then exact .rejected
        else exact (searchHeap fuel ctx b .func).map fun h => ⟨.nofunc h.down bottom⟩
      | .noextern, b =>
        if bottom : b = .bot then exact .rejected
        else exact (searchHeap fuel ctx b .extern).map fun h => ⟨.noextern h.down bottom⟩
      | .noexn, b =>
        if bottom : b = .bot then exact .rejected
        else exact (searchHeap fuel ctx b .exn).map fun h => ⟨.noexn h.down bottom⟩
      | .recIdx i, .func =>
        match lookup : ctx.recs[i]? with
        | none => exact .rejected
        | some sub => exact (searchHeap fuel ctx sub.body.heap .func).map fun h =>
            ⟨.recComp lookup h.down⟩
      | .recIdx i, .struct_ =>
        match lookup : ctx.recs[i]? with
        | none => exact .rejected
        | some sub => exact (searchHeap fuel ctx sub.body.heap .struct_).map fun h =>
            ⟨.recComp lookup h.down⟩
      | .recIdx i, .array =>
        match lookup : ctx.recs[i]? with
        | none => exact .rejected
        | some sub => exact (searchHeap fuel ctx sub.body.heap .array).map fun h =>
            ⟨.recComp lookup h.down⟩
      | .recIdx i, .eq =>
        match lookup : ctx.recs[i]? with
        | none => exact .rejected
        | some sub => exact (searchHeap fuel ctx sub.body.heap .eq).map fun h =>
            ⟨.recComp lookup h.down⟩
      | .recIdx i, .any =>
        match lookup : ctx.recs[i]? with
        | none => exact .rejected
        | some sub => exact (searchHeap fuel ctx sub.body.heap .any).map fun h =>
            ⟨.recComp lookup h.down⟩
      | .recIdx i, b =>
        match lookup : ctx.recs[i]? with
        | none => exact .rejected
        | some sub =>
          exact findSearch (fun parent =>
            if eq : parent.val = b then
              Search.found ⟨.recSuper lookup (eq ▸ parent.property)⟩
            else
              match checkHeapValid fuel ctx parent.val with
              | some valid => (searchHeap fuel ctx parent.val b).map fun h =>
                  ⟨.trans valid.down (.recSuper lookup parent.property) h.down⟩
              | none => .inconclusive) sub.supers.attach
      | _, _ => exact .rejected

/-- Bounded certification of runtime heap validity; `none` may mean insufficient fuel. -/
def checkHeapValid : Nat → (ctx : Context) → (heap : HeapType) → Checked (HeapValid ctx heap)
  | 0, _, _ => none
  | fuel + 1, ctx, heap => by
    match heap with
    | .typeIdx i =>
      match h : ctx.types[i]? with
      | none => exact none
      | some type => exact some ⟨.index h⟩
    | .recIdx i =>
      match h : ctx.recs[i]? with
      | none => exact none
      | some sub => exact some ⟨.recIndex h⟩
    | .defined group i =>
      if bound : i < group.length then
        let extended := {ctx with recs := group ++ ctx.recs}
        exact (checkAll (fun entry : SubType × Nat =>
          checkRuntimeSubValid fuel extended entry.2 entry.1) group.zipIdx).map fun h =>
            ⟨.defined ⟨h.down⟩ bound⟩
      else exact none
    | .func => exact some ⟨.abstract (by simp)⟩
    | .nofunc => exact some ⟨.abstract (by simp)⟩
    | .extern => exact some ⟨.abstract (by simp)⟩
    | .noextern => exact some ⟨.abstract (by simp)⟩
    | .exn => exact some ⟨.abstract (by simp)⟩
    | .noexn => exact some ⟨.abstract (by simp)⟩
    | .bot => exact some ⟨.abstract (by simp)⟩
    | .any => exact some ⟨.abstract (by simp)⟩
    | .eq => exact some ⟨.abstract (by simp)⟩
    | .i31 => exact some ⟨.abstract (by simp)⟩
    | .struct_ => exact some ⟨.abstract (by simp)⟩
    | .array => exact some ⟨.abstract (by simp)⟩
    | .none => exact some ⟨.abstract (by simp)⟩

def checkRuntimeSubValid : Nat → (ctx : Context) → (index : Nat) → (sub : SubType) →
    Checked (RuntimeSubValid ctx index sub)
  | 0, _, _, _ => none
  | fuel + 1, ctx, index, sub => do
    if count : sub.supers.length ≤ 1 then
      let values ← checkAll (fun type => match type with
        | .ref _ heap => (checkHeapValid fuel ctx heap).map fun h => ⟨RuntimeValValid.ref h.down⟩
        | .i32 => some ⟨RuntimeValValid.number (type := .i32) (by simp)⟩
        | .i64 => some ⟨RuntimeValValid.number (type := .i64) (by simp)⟩
        | .f32 => some ⟨RuntimeValValid.number (type := .f32) (by simp)⟩
        | .f64 => some ⟨RuntimeValValid.number (type := .f64) (by simp)⟩
        | .v128 => some ⟨RuntimeValValid.number (type := .v128) (by simp)⟩
        | .bot => some ⟨RuntimeValValid.number (type := .bot) (by simp)⟩) sub.body.valTypes
      let supers ← checkAll (fun parent => do
        let valid ← checkHeapValid fuel ctx parent
        letI : Decidable (parent.Precedes index) := by
          unfold HeapType.Precedes; cases parent <;> infer_instance
        if prior : parent.Precedes index then
          match unfolded : parent.unrollIn? ctx with
          | none => none
          | some type => do
            if nonfinal : type.isFinal = false then
              let matched ← checkCompWith
                (fun a b => (searchHeap fuel ctx a b).toOption) sub.body type.body
              return ⟨RuntimeSuperValid.mk valid.down prior unfolded nonfinal matched.down⟩
            else none
        else none) sub.supers
      return ⟨.mk count values.down supers.down⟩
    else none
end

theorem checkHeapValid_sound (h : (checkHeapValid fuel ctx heap).isSome = true) :
    HeapValid ctx heap := by
  cases result : checkHeapValid fuel ctx heap with
  | none => simp [result] at h
  | some proof => exact proof.down

def searchVal (fuel : Nat) (ctx : Context) (a b : ValType) : Search (ValMatches ctx a b) := by
  match a, b with
  | .i32, .i32 => exact Search.found ⟨.i32⟩
  | .i64, .i64 => exact Search.found ⟨.i64⟩
  | .f32, .f32 => exact Search.found ⟨.f32⟩
  | .f64, .f64 => exact Search.found ⟨.f64⟩
  | .v128, .v128 => exact Search.found ⟨.v128⟩
  | .bot, _ => exact Search.found ⟨.bot⟩
  | .ref na ha, .ref nb hb =>
    if nullable : na = true → nb = true then
      exact (searchHeap fuel ctx ha hb).map fun h =>
        ⟨.ref (a := ⟨na, ha⟩) (b := ⟨nb, hb⟩) ⟨nullable, h.down⟩⟩
    else exact .rejected
  | _, _ => exact .rejected

def checkHeap (fuel : Nat) (ctx : Context) (a b : HeapType) : Checked (HeapMatches ctx a b) :=
  (searchHeap fuel ctx a b).toOption

/-- A declared-supertype edge consumes one unit of fuel before searching its parent. -/
theorem checkHeap_defined_super_complete {ctx : Context} {fuel : Nat}
    {a b : DefinedType} {left right : DefinedType} {sub : SubType} {parent : HeapType}
    (closedLeft : a.close? ctx.types = some left)
    (closedRight : b.close? ctx.types = some right)
    (unrolled : a.unroll? = some sub) (member : parent ∈ sub.supers)
    (success : (checkHeap fuel ctx parent b.heap).isSome = true) :
    (checkHeap (fuel + 1) ctx a.heap b.heap).isSome = true := by
  cases a with
  | mk group index =>
    cases b with
    | mk target j =>
      simp only [DefinedType.heap, checkHeap, searchHeap]
      split
      · rename_i same
        cases same
        rfl
      · split <;> simp_all
        all_goals subst_vars
        split
        · rfl
        · split <;> simp_all
          all_goals subst_vars
          apply findSearch_complete
          refine ⟨⟨parent, member⟩, by simp, ?_⟩
          cases found : searchHeap fuel ctx parent (.defined target j) <;>
            simp [checkHeap, DefinedType.heap, found, Search.toOption] at success
          simp [Search.map, Search.toOption]

def checkVal (fuel : Nat) (ctx : Context) (a b : ValType) : Checked (ValMatches ctx a b) :=
  (searchVal fuel ctx a b).toOption

def checkResults (fuel : Nat) (ctx : Context) :
    (a b : List ValType) → Checked (ResultMatches ctx a b)
  | [], [] => some ⟨.nil⟩
  | a :: as, b :: bs => do
    let head ← checkVal fuel ctx a b
    let tail ← checkResults fuel ctx as bs
    return ⟨.cons head.down tail.down⟩
  | _, _ => none

end Wasm.Types
