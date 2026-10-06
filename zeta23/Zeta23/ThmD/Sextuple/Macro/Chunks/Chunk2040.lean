import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 67687, payload cursor 33837, depth 16, 9 tokens. -/
theorem chunk2040 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 67687 33837 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (67696, 33842) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
