import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 90098, payload cursor 45042, depth 17, 91 tokens. -/
theorem chunk2779 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 90098 45042 (pathBox rootBox [(true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (90189, 45088) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
