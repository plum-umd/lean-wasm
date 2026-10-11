import Wasm.TypeSafety.CoreConfiguration

namespace Wasm.TypeSafety

/-- Closure of the existing configuration relation under a flat evaluation context. -/
theorem ConfigStep.in_core_context
    (step : ConfigStep ⟨store, state, code⟩ ⟨nextStore, nextState, next⟩) :
    ConfigStep ⟨store, state, values vs ++ code ++ tail⟩
      ⟨nextStore, nextState, values vs ++ next ++ tail⟩ := by
  cases step <;> first
    | exact .pure (.context (by assumption))
    | exact .locals (.context (by assumption))
    | exact .call (.context (by assumption))
    | exact .globals (.context (by assumption))
    | exact .memory (.context (by assumption))
    | exact .references (.context (by assumption))
    | exact .tables (.context (by assumption))
    | exact .bulk (.context (by assumption))
    | exact .structures (.context (by assumption))
    | exact .arrays (.context (by assumption))
    | exact .vectors (.context (by assumption))
    | exact .exceptions (.context (by assumption))

theorem ConfigStep.in_core_label
    (step : ConfigStep ⟨store, state, body⟩ ⟨nextStore, nextState, next⟩) :
    ConfigStep ⟨store, state, [.label n continuation body]⟩
      ⟨nextStore, nextState, [.label n continuation next]⟩ := by
  cases step <;> first
    | exact .pure (.label (by assumption))
    | exact .locals (.label (by assumption))
    | exact .call (.label (by assumption))
    | exact .globals (.label (by assumption))
    | exact .memory (.label (by assumption))
    | exact .references (.label (by assumption))
    | exact .tables (.label (by assumption))
    | exact .bulk (.label (by assumption))
    | exact .structures (.label (by assumption))
    | exact .arrays (.label (by assumption))
    | exact .vectors (.label (by assumption))
    | exact .exceptions (.label (by assumption))

theorem ConfigStep.in_core_frame
    (step : ConfigStep ⟨store, inner, body⟩ ⟨nextStore, nextInner, next⟩) :
    ConfigStep ⟨store, outer, [.frame n inner body]⟩
      ⟨nextStore, outer, [.frame n nextInner next]⟩ := by
  cases step <;> first
    | exact .pure (.frame (by assumption))
    | exact .pure (.localFrame (by assumption))
    | exact .call (.frame (by assumption))
    | exact .globals (.frame (by assumption))
    | exact .memory (.frame (by assumption))
    | exact .references (.frame (by assumption))
    | exact .tables (.frame (by assumption))
    | exact .bulk (.frame (by assumption))
    | exact .structures (.frame (by assumption))
    | exact .arrays (.frame (by assumption))
    | exact .vectors (.frame (by assumption))
    | exact .exceptions (.frame (by assumption))

end Wasm.TypeSafety
