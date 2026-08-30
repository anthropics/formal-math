import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 77543, payload cursor 38766, depth 14, 49 tokens. -/
theorem chunk2379 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 47 77543 38766 (pathBox rootBox [(true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (77592, 38791) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
