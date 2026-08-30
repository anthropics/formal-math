import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 93048, payload cursor 46520, depth 12, 45 tokens. -/
theorem chunk2857 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 93048 46520 (pathBox rootBox [(true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (93093, 46543) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
