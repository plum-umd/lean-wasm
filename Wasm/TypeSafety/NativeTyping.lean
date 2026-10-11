import Wasm.TypeSafety.CoreSource

namespace Wasm.TypeSafety

mutual
  /-- Administrative typing retains the validator's bottom types and matching evidence. -/
  inductive NativeCoreInstrTyping (store : Store) : FunctionContext → LabelContext →
      AdminInstr → List Types.ValType → List Types.ValType → Prop where
    | source (typed : ValidationInstrTyping context labels i input output)
        (supported : CoreSource i) :
        NativeCoreInstrTyping store context labels (.instr i) input output
    | trap : NativeCoreInstrTyping store context labels .trap input output
    | block (ht : bt.resolve context.types = some ft)
        (bodyTyped : NativeCoreTyping store context (ft.results :: labels)
          (instructions body) (ft.params.map Types.embedVal) (ft.results.map Types.embedVal)) :
        NativeCoreInstrTyping store context labels (.instr (.block bt body))
          (ft.params.map Types.embedVal) (ft.results.map Types.embedVal)
    | loop (ht : bt.resolve context.types = some ft)
        (bodyTyped : NativeCoreTyping store context (ft.params :: labels)
          (instructions body) (ft.params.map Types.embedVal) (ft.results.map Types.embedVal)) :
        NativeCoreInstrTyping store context labels (.instr (.loop bt body))
          (ft.params.map Types.embedVal) (ft.results.map Types.embedVal)
    | if_ (ht : bt.resolve context.types = some ft)
        (yesTyped : NativeCoreTyping store context (ft.results :: labels)
          (instructions yes) (ft.params.map Types.embedVal) (ft.results.map Types.embedVal))
        (noTyped : NativeCoreTyping store context (ft.results :: labels)
          (instructions no) (ft.params.map Types.embedVal) (ft.results.map Types.embedVal)) :
        NativeCoreInstrTyping store context labels (.instr (.if_ bt yes no))
          ((ft.params ++ [ValType.i32]).map Types.embedVal) (ft.results.map Types.embedVal)
    | invoke (hf : store.func? address = some function) :
        NativeCoreInstrTyping store context labels (.invoke address function.type)
          (function.type.params.map Types.embedVal) (function.type.results.map Types.embedVal)
    | label {results : List ValType}
        (bodyTyped : NativeCoreTyping store context (branch :: labels) body []
          (results.map Types.embedVal))
        (continuationTyped : NativeCoreTyping store context labels
          (instructions continuation) (branch.map Types.embedVal) (results.map Types.embedVal)) :
        NativeCoreInstrTyping store context labels (.label branch.length continuation body)
          [] (results.map Types.embedVal)
    | frame (frameTyped : CoreFrameTyped store state innerContext)
        (returns : innerContext.returns = some results)
        (bodyTyped : NativeCoreTyping store innerContext [] body [] (results.map Types.embedVal)) :
        NativeCoreInstrTyping store context labels (.frame results.length state body)
          [] (results.map Types.embedVal)
    | weaken : NativeCoreInstrTyping store context labels i input output →
        NativeCoreInstrTyping store context labels i (stackBelow ++ input) (stackBelow ++ output)
    | subtype : NativeCoreInstrTyping store context labels i input output →
        Types.ResultMatches ⟨context.definedTypes, []⟩ input' input →
        Types.ResultMatches ⟨context.definedTypes, []⟩ output output' →
        NativeCoreInstrTyping store context labels i input' output'

  inductive NativeCoreTyping (store : Store) : FunctionContext → LabelContext →
      List AdminInstr → List Types.ValType → List Types.ValType → Prop where
    | nil : NativeCoreTyping store context labels [] ts ts
    | cons : NativeCoreInstrTyping store context labels i input middle →
        NativeCoreTyping store context labels rest middle output →
        NativeCoreTyping store context labels (i :: rest) input output
    | weaken : NativeCoreTyping store context labels code input output →
        NativeCoreTyping store context labels code (stackBelow ++ input) (stackBelow ++ output)
    | subtype : NativeCoreTyping store context labels code input output →
        Types.ResultMatches ⟨context.definedTypes, []⟩ input' input →
        Types.ResultMatches ⟨context.definedTypes, []⟩ output output' →
        NativeCoreTyping store context labels code input' output'
end

/-- Exact administrative typing remains a special case of native stack typing. -/
theorem CoreTyping.toNativeCoreTyping (typed : CoreTyping store context labels code input output) :
    NativeCoreTyping store context labels code
      (input.map Types.embedVal) (output.map Types.embedVal) := by
  induction typed using CoreTyping.rec
    (motive_1 := fun context labels i input output _ =>
      NativeCoreInstrTyping store context labels i
        (input.map Types.embedVal) (output.map Types.embedVal)) with
  | plain h hs => exact .source (.legacy (.plain (.plain (.plain h)))) (.scalar hs)
  | trap => exact .trap
  | block ht _ ih => exact .block ht ih
  | loop ht _ ih => exact .loop ht ih
  | if_ ht _ _ ihy ihn => exact .if_ ht ihy ihn
  | br ht =>
      simpa using NativeCoreInstrTyping.source
        (.legacy (.plain (.plain (.br ht)))) .br
  | brIf ht =>
      exact .source (.legacy (.plain (.plain (.brIf ht)))) .brIf
  | brTable hd ht =>
      simpa [List.append_assoc] using NativeCoreInstrTyping.source
        (.legacy (.plain (.plain (.brTable hd ht)))) .brTable
  | localGet ht => exact .source (.legacy (.plain (.localGet ht))) .localGet
  | localSet ht => exact .source (.legacy (.plain (.localSet ht))) .localSet
  | localTee ht => exact .source (.legacy (.plain (.localTee ht))) .localTee
  | call ht => exact .source (.legacy (.call ht)) .call
  | return_ ht => exact .source (.legacy (.return_ ht)) .return_
  | invoke ht => exact .invoke ht
  | label _ _ ihb ihc => exact .label ihb ihc
  | frame hf hr _ ih => exact .frame hf hr ih
  | weaken _ ih => simpa only [List.map_append] using ih.weaken
  | nil => exact .nil
  | cons _ _ ihhead ihtail => exact .cons ihhead ihtail

end Wasm.TypeSafety
