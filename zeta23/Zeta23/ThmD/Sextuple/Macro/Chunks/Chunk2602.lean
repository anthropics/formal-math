import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 84983, payload cursor 42486, depth 14, 47 tokens. -/
theorem chunk2602 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 47 84983 42486 (pathBox rootBox [(true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (85030, 42510) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
