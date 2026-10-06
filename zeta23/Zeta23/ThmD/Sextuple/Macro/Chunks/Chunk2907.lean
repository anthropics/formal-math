import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 96270, payload cursor 48130, depth 12, 83 tokens. -/
theorem chunk2907 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 96270 48130 (pathBox rootBox [(true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96353, 48172) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
