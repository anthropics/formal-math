import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 82274, payload cursor 41130, depth 17, 77 tokens. -/
theorem chunk2540 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 82274 41130 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (82351, 41169) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
