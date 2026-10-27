import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 67708, payload cursor 33848, depth 19, 99 tokens. -/
theorem chunk2044 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 67708 33848 (pathBox rootBox [(true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (67807, 33898) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
