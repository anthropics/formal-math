import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 75535, payload cursor 37762, depth 15, 29 tokens. -/
theorem chunk2327 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 75535 37762 (pathBox rootBox [(true, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (75564, 37777) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
