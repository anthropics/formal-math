import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 90206, payload cursor 45096, depth 18, 1 tokens. -/
theorem chunk2781 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 90206 45096 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (90207, 45097) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
