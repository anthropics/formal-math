import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 1503, payload cursor 744, depth 16, 1 tokens. -/
theorem chunk0029 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 1503 744 (pathBox rootBox [(false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (1504, 745) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
