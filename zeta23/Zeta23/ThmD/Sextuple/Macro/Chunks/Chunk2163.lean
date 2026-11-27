import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 70947, payload cursor 35467, depth 16, 9 tokens. -/
theorem chunk2163 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 70947 35467 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (70956, 35472) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
