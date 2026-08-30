import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 67386, payload cursor 33687, depth 16, 99 tokens. -/
theorem chunk2034 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 67386 33687 (pathBox rootBox [(true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (67485, 33737) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
