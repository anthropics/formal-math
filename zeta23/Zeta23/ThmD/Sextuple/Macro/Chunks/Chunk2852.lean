import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 92760, payload cursor 46375, depth 13, 69 tokens. -/
theorem chunk2852 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 92760 46375 (pathBox rootBox [(true, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (92829, 46410) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
