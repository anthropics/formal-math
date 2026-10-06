import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 71141, payload cursor 35564, depth 16, 9 tokens. -/
theorem chunk2170 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 71141 35564 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (71150, 35569) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
