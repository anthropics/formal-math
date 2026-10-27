import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 83777, payload cursor 41884, depth 13, 79 tokens. -/
theorem chunk2582 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 83777 41884 (pathBox rootBox [(true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (83856, 41924) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
