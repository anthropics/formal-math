import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 87682, payload cursor 43834, depth 21, 15 tokens. -/
theorem chunk2695 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 87682 43834 (pathBox rootBox [(true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (87697, 43842) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
