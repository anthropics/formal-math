import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 94000, payload cursor 46995, depth 13, 89 tokens. -/
theorem chunk2872 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 94000 46995 (pathBox rootBox [(false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (94089, 47040) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
