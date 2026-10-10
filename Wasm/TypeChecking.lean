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

mutual
  def HeapType.weight : HeapType → Nat
    | .defined group index => 1 + index + (group.map SubType.weight).foldl (· + ·) 0
    | _ => 1
  def ValType.weight : ValType → Nat
    | .ref _ heap => 1 + heap.weight
    | _ => 1
  def SubType.weight : SubType → Nat
    | .func _ supers params results => 1 +
      (supers.map HeapType.weight).foldl (· + ·) 0 +
      (params.map ValType.weight).foldl (· + ·) 0 +
      (results.map ValType.weight).foldl (· + ·) 0
end

/-- A size-derived search budget for closed runtime types; not a completeness theorem. -/
def matchingBudget (a b : HeapType) : Nat := (a.weight + b.weight + 1) ^ 2

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
      | .nofunc, b =>
        if bottom : b = .bot then exact .rejected
        else exact (searchHeap fuel ctx b .func).map fun h => ⟨.nofunc h.down bottom⟩
      | .noextern, b =>
        if bottom : b = .bot then exact .rejected
        else exact (searchHeap fuel ctx b .extern).map fun h => ⟨.noextern h.down bottom⟩
      | .recIdx i, .func =>
        match lookup : ctx.recs[i]? with
        | none => exact .rejected
        | some sub => exact Search.found ⟨.recFunc lookup⟩
      | .recIdx i, b =>
        match lookup : ctx.recs[i]? with
        | none => exact .rejected
        | some sub =>
          exact findSearch (fun parent =>
            if eq : parent.val = b then
              Search.found ⟨.recSuper lookup (eq ▸ parent.property)⟩
            else
              let bound := matchingBudget parent.val b
              if scope : parent.val.scopedFuel bound ctx.types.length ctx.recs.length = true then
                (searchHeap fuel ctx parent.val b).map fun h =>
                  ⟨.trans ⟨bound, scope⟩ (.recSuper lookup parent.property) h.down⟩
              else .inconclusive) sub.supers.attach
      | _, _ => exact .rejected

def searchVal (fuel : Nat) (ctx : Context) (a b : ValType) : Search (ValMatches ctx a b) := by
  match a, b with
  | .i32, .i32 => exact Search.found ⟨.i32⟩
  | .i64, .i64 => exact Search.found ⟨.i64⟩
  | .f32, .f32 => exact Search.found ⟨.f32⟩
  | .f64, .f64 => exact Search.found ⟨.f64⟩
  | .bot, _ => exact Search.found ⟨.bot⟩
  | .ref na ha, .ref nb hb =>
    if nullable : na = true → nb = true then
      exact (searchHeap fuel ctx ha hb).map fun h =>
        ⟨.ref (a := ⟨na, ha⟩) (b := ⟨nb, hb⟩) ⟨nullable, h.down⟩⟩
    else exact .rejected
  | _, _ => exact .rejected

def checkHeap (fuel : Nat) (ctx : Context) (a b : HeapType) : Checked (HeapMatches ctx a b) :=
  (searchHeap fuel ctx a b).toOption

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
