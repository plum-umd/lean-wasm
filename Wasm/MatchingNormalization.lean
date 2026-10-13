import Wasm.TypeMatching

/-!
Transitivity elimination for declarative heap matching. A normalized path has primitive
edges and explicitly valid junctions. Matching premises inside primitive rules are themselves
normalized, including declared parents and the reverse premises of hierarchy-bottom rules.
This is independent of executable checks and search fuel.
-/
namespace Wasm.Types

mutual
  /-- A flat sequence of primitive matching edges with valid internal junctions. -/
  inductive HeapMatchPath : Context → HeapType → HeapType → Prop where
    | refl : HeapMatchPath ctx a a
    | edge : HeapMatchEdge ctx a b → HeapMatchPath ctx a b
    | cons : HeapMatchEdge ctx a middle → HeapValid ctx middle →
        HeapMatchPath ctx middle b → HeapMatchPath ctx a b

  /-- Declarative heap rules with transitivity removed and nested matches normalized. -/
  inductive HeapMatchEdge : Context → HeapType → HeapType → Prop where
    | defined : DefinedMatchNormal ctx a b → HeapMatchEdge ctx a.heap b.heap
    | definedFunc {a : DefinedType} {body : FuncType} : a.expand? = some body → HeapMatchEdge ctx a.heap .func
    | indexLeft : ctx.types[x]? = some a → HeapMatchPath ctx a.heap b →
        HeapMatchEdge ctx (.typeIdx x) b
    | indexRight : ctx.types[x]? = some b → HeapMatchPath ctx a b.heap →
        HeapMatchEdge ctx a (.typeIdx x)
    | recFunc : ctx.recs[i]? = some sub → sub.body = .func ft →
        HeapMatchEdge ctx (.recIdx i) .func
    | definedComp {a : DefinedType} {comp : CompType} : a.expandComposite? = some comp → HeapMatchPath ctx comp.heap b →
        HeapMatchEdge ctx a.heap b
    | recComp : ctx.recs[i]? = some sub → HeapMatchPath ctx sub.body.heap b →
        HeapMatchEdge ctx (.recIdx i) b
    | eqAny : HeapMatchEdge ctx .eq .any
    | i31Eq : HeapMatchEdge ctx .i31 .eq
    | structEq : HeapMatchEdge ctx .struct_ .eq
    | arrayEq : HeapMatchEdge ctx .array .eq
    | none : HeapMatchPath ctx a .any → a ≠ .bot → HeapMatchEdge ctx .none a
    | recSuper : ctx.recs[i]? = some sub → parent ∈ sub.supers →
        HeapMatchEdge ctx (.recIdx i) parent
    | nofunc : HeapMatchPath ctx a .func → a ≠ .bot → HeapMatchEdge ctx .nofunc a
    | noextern : HeapMatchPath ctx a .extern → a ≠ .bot → HeapMatchEdge ctx .noextern a
    | noexn : HeapMatchPath ctx a .exn → a ≠ .bot → HeapMatchEdge ctx .noexn a
    | bot : HeapMatchEdge ctx .bot a

  /-- Closing equality and declared parents remain distinct in the normal form. -/
  inductive DefinedMatchNormal : Context → DefinedType → DefinedType → Prop where
    | same : a.close? ctx.types = some closed → b.close? ctx.types = some closed →
        DefinedMatchNormal ctx a b
    | super : a.unroll? = some sub → parent ∈ sub.supers →
        HeapMatchPath ctx parent b.heap → DefinedMatchNormal ctx a b
end

/-- Concatenation flattens paths rather than inserting another transitivity node. -/
theorem HeapMatchPath.append {ctx : Context} {a middle b : HeapType}
    (left : HeapMatchPath ctx a middle) (valid : HeapValid ctx middle)
    (right : HeapMatchPath ctx middle b) : HeapMatchPath ctx a b := by
  have joined : ∀ b, HeapValid ctx middle → HeapMatchPath ctx middle b →
      HeapMatchPath ctx a b := HeapMatchPath.rec
    (motive_1 := fun ctx a middle _ => ∀ b, HeapValid ctx middle →
      HeapMatchPath ctx middle b → HeapMatchPath ctx a b)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (fun _ _ right => right)
    (fun edge _ _ valid right => .cons edge valid right)
    (fun edge junction _ _ ih _ valid right => .cons edge junction (ih _ valid right))
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    left
  exact joined b valid right

/-- Every declarative heap derivation has a flat primitive-edge path. -/
theorem HeapMatches.normalize {ctx : Context} {a b : HeapType}
    (matched : HeapMatches ctx a b) : HeapMatchPath ctx a b := by
  exact HeapMatches.rec
    (motive_1 := fun _ _ _ => True)
    (motive_2 := fun _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ => True)
    (motive_8 := fun _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ => True)
    (motive_13 := fun _ _ _ _ => True)
    (motive_14 := fun _ _ _ _ => True)
    (motive_15 := fun _ _ _ _ => True)
    (motive_6 := fun ctx a b _ => HeapMatchPath ctx a b)
    (motive_7 := fun ctx a b _ => DefinedMatchNormal ctx a b)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (HeapMatchPath.refl)
    (fun valid _ _ _ left right => left.append valid right)
    (fun _ normalized => .edge (.defined normalized))
    (fun expanded => .edge (.definedFunc expanded))
    (fun lookup _ normalized => .edge (.indexLeft lookup normalized))
    (fun lookup _ normalized => .edge (.indexRight lookup normalized))
    (fun lookup body => .edge (.recFunc lookup body))
    (fun expanded _ normalized => .edge (.definedComp expanded normalized))
    (fun lookup _ normalized => .edge (.recComp lookup normalized))
    (HeapMatchPath.edge HeapMatchEdge.eqAny)
    (HeapMatchPath.edge HeapMatchEdge.i31Eq)
    (HeapMatchPath.edge HeapMatchEdge.structEq)
    (HeapMatchPath.edge HeapMatchEdge.arrayEq)
    (fun _ notBottom normalized => .edge (.none normalized notBottom))
    (fun lookup member => .edge (.recSuper lookup member))
    (fun _ notBottom normalized => .edge (.nofunc normalized notBottom))
    (fun _ notBottom normalized => .edge (.noextern normalized notBottom))
    (fun _ notBottom normalized => .edge (.noexn normalized notBottom))
    (HeapMatchPath.edge HeapMatchEdge.bot)
    (DefinedMatchNormal.same)
    (fun unrolled member _ normalized => .super unrolled member normalized)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    matched

theorem DefinedMatches.normalize {ctx : Context} {a b : DefinedType}
    (matched : DefinedMatches ctx a b) : DefinedMatchNormal ctx a b := by
  cases matched with
  | same left right => exact .same left right
  | super unrolled member matched => exact .super unrolled member matched.normalize

/-- A normalized path reconstructs a declarative derivation. -/
theorem HeapMatchPath.sound {ctx : Context} {a b : HeapType}
    (path : HeapMatchPath ctx a b) : HeapMatches ctx a b := by
  exact HeapMatchPath.rec
    (motive_1 := fun ctx a b _ => HeapMatches ctx a b)
    (motive_2 := fun ctx a b _ => HeapMatches ctx a b)
    (motive_3 := fun ctx a b _ => DefinedMatches ctx a b)
    (HeapMatches.refl)
    (fun _ sound => sound)
    (fun _ valid _ edge tail => .trans valid edge tail)
    (fun _ sound => .defined sound)
    (HeapMatches.definedFunc)
    (fun lookup _ sound => .indexLeft lookup sound)
    (fun lookup _ sound => .indexRight lookup sound)
    (HeapMatches.recFunc)
    (fun expanded _ sound => .definedComp expanded sound)
    (fun lookup _ sound => .recComp lookup sound)
    (HeapMatches.eqAny)
    (HeapMatches.i31Eq)
    (HeapMatches.structEq)
    (HeapMatches.arrayEq)
    (fun _ notBottom sound => .none sound notBottom)
    (HeapMatches.recSuper)
    (fun _ notBottom sound => .nofunc sound notBottom)
    (fun _ notBottom sound => .noextern sound notBottom)
    (fun _ notBottom sound => .noexn sound notBottom)
    (HeapMatches.bot)
    (DefinedMatches.same)
    (fun unrolled member _ sound => .super unrolled member sound)
    path

theorem DefinedMatchNormal.sound {ctx : Context} {a b : DefinedType}
    (matched : DefinedMatchNormal ctx a b) : DefinedMatches ctx a b := by
  cases matched with
  | same left right => exact .same left right
  | super unrolled member path => exact .super unrolled member path.sound

/-- Flattening neither loses nor introduces declarative heap matches. -/
theorem heapMatches_iff_path {ctx : Context} {a b : HeapType} :
    HeapMatches ctx a b ↔ HeapMatchPath ctx a b := ⟨HeapMatches.normalize, HeapMatchPath.sound⟩

theorem definedMatches_iff_normal {ctx : Context} {a b : DefinedType} :
    DefinedMatches ctx a b ↔ DefinedMatchNormal ctx a b :=
  ⟨DefinedMatches.normalize, DefinedMatchNormal.sound⟩

#print axioms HeapMatches.normalize
#print axioms heapMatches_iff_path
#print axioms definedMatches_iff_normal

end Wasm.Types
