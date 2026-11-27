import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 80144, payload cursor 40066, depth 15, 85 tokens. -/
theorem chunk2477 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 80144 40066 (pathBox rootBox [(true, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (80229, 40109) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
