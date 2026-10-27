import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 99503, payload cursor 49750, depth 5, 1 tokens. -/
theorem chunk2965 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 56 99503 49750 (pathBox rootBox [(true, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99504, 49751) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
