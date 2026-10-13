import Wasm.TypeMatching

/-! In the empty runtime context, successful closing is identity even before scope checking. -/
namespace Wasm.Types

private theorem mapM_cons_identity {f : α → Option α} {head : α} {tail : List α}
    (headFixed : ∀ result, f head = some result → head = result)
    (tailFixed : ∀ result, tail.mapM f = some result → tail = result)
    {result : List α} (found : (head :: tail).mapM f = some result) :
    head :: tail = result := by
  cases hc : f head with
  | none => simp [List.mapM_cons, hc] at found
  | some first =>
    cases tc : tail.mapM f with
    | none => simp [List.mapM_cons, hc, tc] at found
    | some rest =>
      have h := headFixed first hc
      have t := tailFixed rest tc
      subst first
      subst rest
      simpa [List.mapM_cons, hc, tc] using found

/-- Empty-context closing can reject a type, but cannot change a successful result. -/
theorem HeapType.eq_of_close_empty {heap result : HeapType}
    (found : heap.close? [] = some result) : heap = result := by
  have fixed : ∀ result, heap.close? [] = some result → heap = result := HeapType.rec
    (motive_1 := fun heap => ∀ result, heap.close? [] = some result → heap = result)
    (motive_2 := fun type => ∀ result, type.close? [] = some result → type = result)
    (motive_3 := fun type => ∀ result, type.close? [] = some result → type = result)
    (motive_4 := fun type => ∀ result, type.close? [] = some result → type = result)
    (motive_5 := fun type => ∀ result, type.close? [] = some result → type = result)
    (motive_6 := fun types => ∀ result,
      types.mapM (SubType.close? []) = some result → types = result)
    (motive_7 := fun types => ∀ result,
      types.mapM (HeapType.close? []) = some result → types = result)
    (motive_8 := fun types => ∀ result,
      types.mapM (ValType.close? []) = some result → types = result)
    (motive_9 := fun types => ∀ result,
      types.mapM (FieldType.close? []) = some result → types = result)
    (by intro result found; simpa [HeapType.close?] using found)
    (by intro result found; simpa [HeapType.close?] using found)
    (by intro result found; simpa [HeapType.close?] using found)
    (by intro result found; simpa [HeapType.close?] using found)
    (by intro result found; simpa [HeapType.close?] using found)
    (by intro result found; simpa [HeapType.close?] using found)
    (by intro result found; simpa [HeapType.close?] using found)
    (by intro result found; simpa [HeapType.close?] using found)
    (by intro result found; simpa [HeapType.close?] using found)
    (by intro result found; simpa [HeapType.close?] using found)
    (by intro result found; simpa [HeapType.close?] using found)
    (by intro result found; simpa [HeapType.close?] using found)
    (by intro result found; simpa [HeapType.close?] using found)
    (by intro index result found; simp [HeapType.close?] at found)
    (by intro index result found; simpa [HeapType.close?] using found)
    (by
      intro group index ih result found
      cases hclosed : group.mapM (SubType.close? []) with
      | none => simp [HeapType.close?, hclosed] at found
      | some closed =>
        have same := ih closed hclosed
        subst closed
        simpa [HeapType.close?, hclosed] using found)
    (by intro result found; simpa [ValType.close?] using found)
    (by intro result found; simpa [ValType.close?] using found)
    (by intro result found; simpa [ValType.close?] using found)
    (by intro result found; simpa [ValType.close?] using found)
    (by intro result found; simpa [ValType.close?] using found)
    (by intro result found; simpa [ValType.close?] using found)
    (by
      intro nullable heap ih result found
      cases hclosed : heap.close? [] with
      | none => simp [ValType.close?, hclosed] at found
      | some closed =>
        have same := ih closed hclosed
        subst closed
        simpa [ValType.close?, hclosed] using found)
    (by
      intro type ih result found
      cases hclosed : type.close? [] with
      | none => simp [StorageType.close?, hclosed] at found
      | some closed =>
        have same := ih closed hclosed
        subst closed
        simpa [StorageType.close?, hclosed] using found)
    (by intro result found; simpa [StorageType.close?] using found)
    (by intro result found; simpa [StorageType.close?] using found)
    (by
      intro storage mutable ih result found
      cases hclosed : storage.close? [] with
      | none => simp [FieldType.close?, hclosed] at found
      | some closed =>
        have same := ih closed hclosed
        subst closed
        simpa [FieldType.close?, hclosed] using found)
    (by
      intro final supers params results si pi ri result found
      cases hss : supers.mapM (HeapType.close? []) with
      | none => simp [SubType.close?, hss] at found
      | some ss =>
        have same := si ss hss
        subst ss
        cases hps : params.mapM (ValType.close? []) with
        | none => simp [SubType.close?, hps, hss] at found
        | some ps =>
          have same := pi ps hps
          subst ps
          cases hrs : results.mapM (ValType.close? []) with
          | none => simp [SubType.close?, hrs, hss, hps] at found
          | some rs =>
            have same := ri rs hrs
            subst rs
            simpa [SubType.close?, hss, hps, hrs] using found)
    (by
      intro final supers fields si fi result found
      cases hss : supers.mapM (HeapType.close? []) with
      | none => simp [SubType.close?, hss] at found
      | some ss =>
        have same := si ss hss
        subst ss
        cases hfs : fields.mapM (FieldType.close? []) with
        | none => simp [SubType.close?, hfs, hss] at found
        | some fs =>
          have same := fi fs hfs
          subst fs
          simpa [SubType.close?, hss, hfs] using found)
    (by
      intro final supers field si fi result found
      cases hss : supers.mapM (HeapType.close? []) with
      | none => simp [SubType.close?, hss] at found
      | some ss =>
        have same := si ss hss
        subst ss
        cases hfs : field.close? [] with
        | none => simp [SubType.close?, hfs, hss] at found
        | some fs =>
          have same := fi fs hfs
          subst fs
          simpa [SubType.close?, hss, hfs] using found)
    (by intro result found; simpa using found)
    (fun _ _ head tail _ found => mapM_cons_identity head tail found)
    (by intro result found; simpa using found)
    (fun _ _ head tail _ found => mapM_cons_identity head tail found)
    (by intro result found; simpa using found)
    (fun _ _ head tail _ found => mapM_cons_identity head tail found)
    (by intro result found; simpa using found)
    (fun _ _ head tail _ found => mapM_cons_identity head tail found)
    heap
  exact fixed result found

/-- Closing equality in the empty context cannot identify distinct runtime definitions. -/
theorem DefinedType.eq_of_close_empty {type result : DefinedType}
    (found : type.close? [] = some result) : type = result := by
  have heapFound : type.heap.close? [] = some result.heap := by
    cases type with
    | mk group index =>
      cases result with
      | mk target j =>
        simp only [DefinedType.close?] at found
        cases closed : group.mapM (SubType.close? []) <;> simp [closed] at found
        rcases found with ⟨rfl, rfl⟩
        simp [DefinedType.heap, HeapType.close?, closed]
  have same := HeapType.eq_of_close_empty heapFound
  cases type
  cases result
  simpa [DefinedType.heap] using same

#print axioms DefinedType.eq_of_close_empty

end Wasm.Types
