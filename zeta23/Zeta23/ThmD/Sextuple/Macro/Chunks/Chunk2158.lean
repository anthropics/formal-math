import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 70693, payload cursor 35340, depth 21, 19 tokens. -/
theorem chunk2158 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 70693 35340 (pathBox rootBox [(true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (70712, 35350) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
