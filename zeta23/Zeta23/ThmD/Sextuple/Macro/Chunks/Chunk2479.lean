import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 80234, payload cursor 40110, depth 17, 97 tokens. -/
theorem chunk2479 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 80234 40110 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (80331, 40159) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
