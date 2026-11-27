import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 99408, payload cursor 49702, depth 6, 95 tokens. -/
theorem chunk2964 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 55 99408 49702 (pathBox rootBox [(true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99503, 49750) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
