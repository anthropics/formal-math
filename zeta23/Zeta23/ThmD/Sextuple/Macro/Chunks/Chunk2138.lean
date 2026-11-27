import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 70226, payload cursor 35108, depth 14, 43 tokens. -/
theorem chunk2138 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 47 70226 35108 (pathBox rootBox [(true, 0), (true, 3), (true, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (70269, 35130) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
