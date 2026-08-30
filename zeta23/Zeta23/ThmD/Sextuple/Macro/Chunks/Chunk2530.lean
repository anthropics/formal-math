import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 81817, payload cursor 40902, depth 17, 39 tokens. -/
theorem chunk2530 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 81817 40902 (pathBox rootBox [(true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (81856, 40922) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
