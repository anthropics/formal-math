import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 75510, payload cursor 37749, depth 18, 25 tokens. -/
theorem chunk2326 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 75510 37749 (pathBox rootBox [(true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (75535, 37762) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
