import Wasm.TypeSafety.NativeContexts
import Wasm.TypeSafety.NativeSource

namespace Wasm.TypeSafety

/-- Primitive source effects, with recursive control bodies in administrative typing. -/
inductive NativeSourceTyping (store : Store) (context : FunctionContext) (labels : LabelContext) :
    Instr → List Wasm.Types.ValType → List Wasm.Types.ValType → Prop where
  | exact (typed : CoreInstrTyping store context labels (.instr i) input output) :
      NativeSourceTyping store context labels i
        (input.map Wasm.Types.embedVal) (output.map Wasm.Types.embedVal)
  | drop : NativeSourceTyping store context labels .drop [t] []
  | select (ht : t = .bot ∨ t = .i32 ∨ t = .i64 ∨ t = .f32 ∨ t = .f64 ∨ t = .v128) :
      NativeSourceTyping store context labels (.select none) [t, t, .i32] [t]
  | unreachable : NativeSourceTyping store context labels .unreachable input output
  | br (ht : labels[x]? = some ts) :
      NativeSourceTyping store context labels (.br x) (input ++ ts.map Wasm.Types.embedVal) output
  | brTable (ht : ∀ x ∈ fallback :: targets, ∃ ts, labels[x]? = some ts ∧
      Wasm.Types.ResultMatches ⟨context.definedTypes, []⟩ arguments (ts.map Wasm.Types.embedVal)) :
      NativeSourceTyping store context labels (.brTable targets fallback)
        (input ++ (arguments ++ [.i32])) output
  | return_ (ht : context.returns = some results) :
      NativeSourceTyping store context labels .return_
        (input ++ results.map Wasm.Types.embedVal) output
  | block (ht : bt.resolve context.types = some ft)
      (hb : NativeCoreTyping store context (ft.results :: labels) (instructions body)
        (ft.params.map Wasm.Types.embedVal) (ft.results.map Wasm.Types.embedVal)) :
      NativeSourceTyping store context labels (.block bt body)
        (ft.params.map Wasm.Types.embedVal) (ft.results.map Wasm.Types.embedVal)
  | loop (ht : bt.resolve context.types = some ft)
      (hb : NativeCoreTyping store context (ft.params :: labels) (instructions body)
        (ft.params.map Wasm.Types.embedVal) (ft.results.map Wasm.Types.embedVal)) :
      NativeSourceTyping store context labels (.loop bt body)
        (ft.params.map Wasm.Types.embedVal) (ft.results.map Wasm.Types.embedVal)
  | if_ (ht : bt.resolve context.types = some ft)
      (hy : NativeCoreTyping store context (ft.results :: labels) (instructions yes)
        (ft.params.map Wasm.Types.embedVal) (ft.results.map Wasm.Types.embedVal))
      (hn : NativeCoreTyping store context (ft.results :: labels) (instructions no)
        (ft.params.map Wasm.Types.embedVal) (ft.results.map Wasm.Types.embedVal)) :
      NativeSourceTyping store context labels (.if_ bt yes no)
        ((ft.params ++ [ValType.i32]).map Wasm.Types.embedVal) (ft.results.map Wasm.Types.embedVal)
  | weaken : NativeSourceTyping store context labels i input output →
      NativeSourceTyping store context labels i (stackBelow ++ input) (stackBelow ++ output)
  | subtype : NativeSourceTyping store context labels i input output →
      Wasm.Types.ResultMatches ⟨context.definedTypes, []⟩ input' input →
      Wasm.Types.ResultMatches ⟨context.definedTypes, []⟩ output output' →
      NativeSourceTyping store context labels i input' output'

private theorem GlobalInstrTyping.not_core (h : GlobalInstrTyping globals i input output)
    (hs : CoreSource i) : False := by
  induction h with
  | weaken _ ih => exact ih hs
  | _ => cases hs <;> contradiction

private theorem MemoryInstrTyping.not_core (h : MemoryInstrTyping mems i input output)
    (hs : CoreSource i) : False := by
  induction h with
  | weaken _ ih => exact ih hs
  | _ => cases hs <;> contradiction

private theorem BulkInstrTyping.not_core (h : BulkInstrTyping mems count i input output)
    (hs : CoreSource i) : False := by
  induction h with
  | weaken _ ih => exact ih hs
  | _ => cases hs <;> contradiction

private theorem StructInstrTyping.not_core (h : StructInstrTyping types i input output)
    (hs : CoreSource i) : False := by
  cases h <;> cases hs <;> contradiction

private theorem ReferenceInstrTyping.not_core
    (h : ReferenceInstrTyping funcs declared i input output) (hs : CoreSource i) : False := by
  cases h <;> cases hs <;> contradiction

private theorem TableInstrTyping.not_core
    (h : TableInstrTyping types tables elems i input output) (hs : CoreSource i) : False := by
  cases h <;> cases hs <;> contradiction

private theorem block_support (h : CoreSource (.block bt body)) : ∀ i ∈ body, CoreSource i := by
  cases h with
  | block hs => exact hs
  | scalar hs => contradiction

private theorem loop_support (h : CoreSource (.loop bt body)) : ∀ i ∈ body, CoreSource i := by
  cases h with
  | loop hs => exact hs
  | scalar hs => contradiction

private theorem if_support (h : CoreSource (.if_ bt yes no)) :
    (∀ i ∈ yes, CoreSource i) ∧ (∀ i ∈ no, CoreSource i) := by
  cases h with
  | if_ hy hn => exact ⟨hy, hn⟩
  | scalar hs => contradiction

theorem RuntimeInstrTyping.native_source
    (typed : RuntimeInstrTyping context labels i input output) (supported : CoreSource i) :
    NativeSourceTyping store context labels i
      (input.map Wasm.Types.embedVal) (output.map Wasm.Types.embedVal) := by
  revert supported
  apply RuntimeInstrTyping.rec
    (motive_1 := fun labels i input output _ => CoreSource i →
      NativeSourceTyping store context labels i
        (input.map Wasm.Types.embedVal) (output.map Wasm.Types.embedVal))
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun labels i input output _ => CoreSource i →
      NativeSourceTyping store context labels i input output)
    (motive_4 := fun _ _ _ _ _ => True) (t := typed)
  all_goals dsimp only
  all_goals try (intros; trivial)
  all_goals try (intros; rename_i hs; cases hs <;> contradiction)
  all_goals try
    intros
    first
    | exact False.elim (GlobalInstrTyping.not_core (by assumption) (by assumption))
    | exact False.elim (MemoryInstrTyping.not_core (by assumption) (by assumption))
    | exact False.elim (BulkInstrTyping.not_core (by assumption) (by assumption))
    | exact False.elim (StructInstrTyping.not_core (by assumption) (by assumption))
    | exact False.elim (ReferenceInstrTyping.not_core (by assumption) (by assumption))
    | exact False.elim (TableInstrTyping.not_core (by assumption) (by assumption))
  · intro labels i input output h hs; exact .exact (FunctionInstrTyping.toCoreTyping h hs)
  · intro x ft labels ht hs; exact .exact (.call ht)
  · intro results labels input output ht hs; exact .exact (.return_ ht)
  · intro ft labels body bt ht hb ih hs
    exact .block ht (RuntimeSeqTyping.toNativeCoreTyping hb (block_support hs))
  · intro ft labels body bt ht hb ih hs
    exact .loop ht (RuntimeSeqTyping.toNativeCoreTyping hb (loop_support hs))
  · intro ft labels yes no bt ht hy hn ihy ihn hs
    exact .if_ ht (RuntimeSeqTyping.toNativeCoreTyping hy (if_support hs).1)
      (RuntimeSeqTyping.toNativeCoreTyping hn (if_support hs).2)
  · intro labels i input output below h ih hs
    simpa only [List.map_append] using (ih hs).weaken
  · intro labels i input output input' output' h hin hout ih hs
    exact .subtype (ih hs) hin hout
  · intro labels i input output h ih hs; exact ih hs
  · intro labels t hs; exact .drop
  · intro t labels ht hs; exact .select ht
  · intro labels input output hs; exact .unreachable
  · intro labels x ts input output ht hs; exact .br ht
  · intro labels fallback ts targets input output hd ht hs
    simp only [List.map_append, List.map_cons, List.map_nil, Wasm.Types.embedVal]
    apply NativeSourceTyping.brTable (arguments := ts.map Wasm.Types.embedVal)
    intro x hx
    refine ⟨ts, ?_, native_matches_refl _ _⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hd
    · exact ht x hx
  · intro fallback targets labels arguments input output ht hs; exact .brTable ht
  · intro results labels input output ht hs; exact .return_ ht
  · intro ft labels body bt ht hb ih hs
    exact .block ht (ValidationSeqTyping.toNativeCoreTyping hb (block_support hs))
  · intro ft labels body bt ht hb ih hs
    exact .loop ht (ValidationSeqTyping.toNativeCoreTyping hb (loop_support hs))
  · intro ft labels yes no bt ht hy hn ihy ihn hs
    exact .if_ ht (ValidationSeqTyping.toNativeCoreTyping hy (if_support hs).1)
      (ValidationSeqTyping.toNativeCoreTyping hn (if_support hs).2)
  · intro labels i input output below h ih hs; exact (ih hs).weaken
  · intro labels i input output input' output' h hin hout ih hs
    exact .subtype (ih hs) hin hout

theorem ValidationInstrTyping.native_source
    (typed : ValidationInstrTyping context labels i input output) (supported : CoreSource i) :
    NativeSourceTyping store context labels i input output := by
  revert supported
  apply ValidationInstrTyping.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun labels i input output _ => CoreSource i →
      NativeSourceTyping store context labels i input output)
    (motive_4 := fun _ _ _ _ _ => True) (t := typed)
  all_goals dsimp only
  all_goals try (intros; trivial)
  all_goals try (intros; rename_i hs; cases hs <;> contradiction)
  · intro labels i input output h ih hs; exact RuntimeInstrTyping.native_source h hs
  · intro labels t hs; exact .drop
  · intro t labels ht hs; exact .select ht
  · intro labels input output hs; exact .unreachable
  · intro labels x ts input output ht hs; exact .br ht
  · intro labels fallback ts targets input output hd ht hs
    simp only [List.map_append, List.map_cons, List.map_nil, Wasm.Types.embedVal]
    apply NativeSourceTyping.brTable (arguments := ts.map Wasm.Types.embedVal)
    intro x hx
    refine ⟨ts, ?_, native_matches_refl _ _⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hd
    · exact ht x hx
  · intro fallback targets labels arguments input output ht hs; exact .brTable ht
  · intro results labels input output ht hs; exact .return_ ht
  · intro ft labels body bt ht hb ih hs
    exact .block ht (ValidationSeqTyping.toNativeCoreTyping hb (block_support hs))
  · intro ft labels body bt ht hb ih hs
    exact .loop ht (ValidationSeqTyping.toNativeCoreTyping hb (loop_support hs))
  · intro ft labels yes no bt ht hy hn ihy ihn hs
    exact .if_ ht (ValidationSeqTyping.toNativeCoreTyping hy (if_support hs).1)
      (ValidationSeqTyping.toNativeCoreTyping hn (if_support hs).2)
  · intro labels i input output below h ih hs; exact (ih hs).weaken
  · intro labels i input output input' output' h hin hout ih hs
    exact .subtype (ih hs) hin hout

theorem NativeSourceTyping.toNativeCoreInstrTyping
    (typed : NativeSourceTyping store context labels i input output) :
    NativeCoreInstrTyping store context labels (.instr i) input output := by
  induction typed with
  | exact h =>
    exact NativeCoreTyping.single_iff.mp ((CoreTyping.cons h .nil).toNativeCoreTyping)
  | drop => exact .source .drop (.scalar (by trivial))
  | select ht => exact .source (.select ht) (.scalar (by trivial))
  | unreachable => exact .source .unreachable (.scalar (by trivial))
  | br ht => exact .source (.br ht) .br
  | brTable ht => exact .source (.brTableMatches ht) .brTable
  | return_ ht => exact .source (.return_ ht) .return_
  | block ht hb => exact .block ht hb
  | loop ht hb => exact .loop ht hb
  | if_ ht hy hn => exact .if_ ht hy hn
  | weaken _ ih => exact .weaken ih
  | subtype _ hin hout ih => exact .subtype ih hin hout

/-- Eliminate the mutually recursive source wrappers before inspecting an instruction. -/
theorem NativeCoreInstrTyping.source_effect
    (typed : NativeCoreInstrTyping store context labels (.instr i) input output) :
    NativeSourceTyping store context labels i input output := by
  generalize hi : AdminInstr.instr i = admin at typed
  induction typed using NativeCoreInstrTyping.rec (motive_2 := fun _ _ _ _ _ _ => True) with
  | source h hs => cases hi; exact ValidationInstrTyping.native_source h hs
  | block ht hb ih => cases hi; exact .block ht hb
  | loop ht hb ih => cases hi; exact .loop ht hb
  | if_ ht hy hn ihy ihn => cases hi; exact .if_ ht hy hn
  | weaken _ ih => exact .weaken (ih hi)
  | subtype _ hin hout ih => exact .subtype (ih hi) hin hout
  | _ => first | trivial | cases hi

end Wasm.TypeSafety
