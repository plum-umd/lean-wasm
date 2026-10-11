import Wasm.TypeMatchingAlgorithm
import Wasm.TypeValidation

namespace Wasm.Types.Algorithm

def valValid (ctx : Context) : ValType → Bool
  | .ref _ heap => heap.scopedFuel (matchingBudget heap heap) ctx.types.length ctx.recs.length
  | _ => true

def funcMatches (ctx : Context) (a b : FuncType) : Bool :=
  let weight := (a.params ++ a.results ++ b.params ++ b.results).map ValType.weight
  let fuel := budget ctx .bot .bot + (weight.foldl (· + ·) 0 + 1)^2
  resultMatches fuel ctx b.params a.params && resultMatches fuel ctx a.results b.results

def storageMatches (ctx : Context) : StorageType → StorageType → Bool
  | .val a, .val b => valMatches (budget ctx a b) ctx a b
  | .i8, .i8 | .i16, .i16 => true
  | _, _ => false

def fieldMatches (ctx : Context) (a b : FieldType) : Bool :=
  decide (a.mutable = b.mutable) && storageMatches ctx a.storage b.storage &&
    (!a.mutable || storageMatches ctx b.storage a.storage)

def fieldsMatches (ctx : Context) : List FieldType → List FieldType → Bool
  | _, [] => true
  | a :: as, b :: bs => fieldMatches ctx a b && fieldsMatches ctx as bs
  | [], _ :: _ => false

def compMatches (ctx : Context) : CompType → CompType → Bool
  | .func a, .func b => funcMatches ctx a b
  | .struct_ as, .struct_ bs => fieldsMatches ctx as bs
  | .array a, .array b => fieldMatches ctx a b
  | _, _ => false

def superValid (ctx : Context) (index : Nat) (body : CompType) : HeapType → Bool
  | .typeIdx x =>
    if x < index then match ctx.types[x]? with
    | none => false
    | some defined => match defined.unroll? with
      | none => false
      | some unfolded => !unfolded.isFinal && compMatches ctx body unfolded.body
    else false
  | _ => false

def subValid (ctx : Context) (index : Nat) (sub : SubType) : Bool :=
  sub.isSource && decide (sub.supers.length ≤ 1) &&
    sub.body.valTypes.all (valValid ctx) &&
    sub.supers.all (superValid ctx index sub.body)

def groupValid (ctx : Context) : Nat → RecType → Bool
  | _, [] => true
  | index, sub :: rest => subValid ctx index sub && groupValid ctx (index + 1) rest

def closed (type : DefinedType) : Bool :=
  type.heap.scopedFuel (matchingBudget type.heap type.heap) 0 0

def typeSection (previous : List DefinedType) : List RecType → Bool
  | [] => true
  | group :: rest => match group.resolve? previous with
    | none => false
    | some resolved => resolved.all closed &&
      groupValid ⟨previous ++ resolved, []⟩ previous.length group &&
      typeSection (previous ++ resolved) rest

theorem valValid_sound (h : valValid ctx type = true) : type.Valid ctx := by
  cases type <;> simp only [valValid, ValType.Valid] at *
  all_goals try trivial
  exact ⟨_, h⟩

theorem funcMatches_sound (h : funcMatches ctx a b = true) : FuncMatches ctx a b := by
  simp only [funcMatches, Bool.and_eq_true] at h
  exact ⟨resultMatches_sound h.1, resultMatches_sound h.2⟩

theorem storageMatches_sound (h : storageMatches ctx a b = true) : StorageMatches ctx a b := by
  cases a <;> cases b <;> simp only [storageMatches, Bool.false_eq_true] at h
  all_goals try contradiction
  all_goals try exact .i8
  all_goals try exact .i16
  exact .val (valMatches_sound h)

theorem fieldMatches_sound (h : fieldMatches ctx a b = true) : FieldMatches ctx a b := by
  simp only [fieldMatches, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h
  refine ⟨h.1.1, storageMatches_sound h.1.2, ?_⟩
  intro mutable
  rcases h.2 with immutable | invariant
  · simp [mutable] at immutable
  · exact storageMatches_sound invariant

theorem fieldsMatches_sound (h : fieldsMatches ctx as bs = true) : FieldsMatches ctx as bs := by
  induction bs generalizing as with
  | nil => exact .nil
  | cons b bs ih =>
    cases as with
    | nil => cases h
    | cons a as =>
      simp only [fieldsMatches, Bool.and_eq_true] at h
      exact .cons (fieldMatches_sound h.1) (ih h.2)

theorem compMatches_sound (h : compMatches ctx a b = true) : CompMatches ctx a b := by
  cases a <;> cases b <;> simp only [compMatches, Bool.false_eq_true] at h
  all_goals try contradiction
  · exact .func (funcMatches_sound h)
  · exact .struct_ (fieldsMatches_sound h)
  · exact .array (fieldMatches_sound h)

theorem superValid_sound (h : superValid ctx index body parent = true) :
    ∃ x defined unfolded, parent = .typeIdx x ∧ x < index ∧
      ctx.types[x]? = some defined ∧ defined.unroll? = some unfolded ∧
      unfolded.isFinal = false ∧ CompMatches ctx body unfolded.body := by
  cases parent <;> simp only [superValid, Bool.false_eq_true] at h
  all_goals try contradiction
  case typeIdx x =>
    split at h <;> try contradiction
    rename_i prior
    cases lookup : ctx.types[x]? <;> simp [lookup] at h
    rename_i defined
    cases unfolded : defined.unroll? <;> simp [unfolded] at h
    exact ⟨x, defined, _, rfl, prior, lookup, unfolded, h.1, compMatches_sound h.2⟩

theorem subValid_sound (h : subValid ctx index sub = true) : sub.Valid ctx index := by
  simp only [subValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2,
    fun type member => valValid_sound (h.1.2 type member),
    fun parent member => superValid_sound (h.2 parent member)⟩

theorem groupValid_sound (h : groupValid ctx base group = true) : group.Valid ctx base := by
  induction group generalizing base with
  | nil => intro i sub lookup; simp at lookup
  | cons sub rest ih =>
    simp only [groupValid, Bool.and_eq_true] at h
    intro i value lookup
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
      subst value
      simpa using subValid_sound h.1
    | succ i =>
      simp only [List.getElem?_cons_succ] at lookup
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih h.2 i value lookup

theorem typeSection_sound (h : typeSection previous groups = true) :
    ∃ final, resolveSection? previous groups = some final ∧
      TypeSectionValid previous groups final := by
  induction groups generalizing previous with
  | nil => exact ⟨previous, rfl, .nil⟩
  | cons group rest ih =>
    cases resolved : group.resolve? previous <;> simp [typeSection, resolved] at h
    obtain ⟨final, resolution, valid⟩ := ih h.2
    refine ⟨final, ?_, .cons resolved ?_ (groupValid_sound h.1.2) valid⟩
    · simp [resolveSection?, resolved, resolution]
    · intro type member
      exact ⟨_, h.1.1 type member⟩

end Wasm.Types.Algorithm
