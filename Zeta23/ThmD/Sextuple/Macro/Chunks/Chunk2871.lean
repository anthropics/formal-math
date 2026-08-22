import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 93908, payload cursor 46949, depth 13, 91 tokens. -/
theorem chunk2871 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 93908 46949 (pathBox rootBox [(true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (93999, 46995) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
