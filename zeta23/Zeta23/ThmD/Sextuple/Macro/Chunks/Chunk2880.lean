import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 94525, payload cursor 47256, depth 16, 69 tokens. -/
theorem chunk2880 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 94525 47256 (pathBox rootBox [(true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (94594, 47291) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
