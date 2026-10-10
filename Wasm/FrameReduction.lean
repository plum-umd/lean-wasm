import Wasm.Runtime

namespace Wasm

/-- Activation completion checks return arity; locals are discarded on exit. -/
inductive FrameReduces : List AdminInstr → List AdminInstr → Prop where
  | done (h : vs.length = n) :
      FrameReduces [.frame n state (values vs)] (values vs)
  | trap : FrameReduces [.frame n state [.trap]] [.trap]
  | return_ (h : results.length = n) :
      FrameReduces [.frame n state
        (values discarded ++ values results ++ [.instr .return_] ++ tail)] (values results)

end Wasm
