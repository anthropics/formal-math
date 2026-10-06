import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 5337, payload cursor 2661, depth 16, 1 tokens. -/
theorem chunk0140 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 5337 2661 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (5338, 2662) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
