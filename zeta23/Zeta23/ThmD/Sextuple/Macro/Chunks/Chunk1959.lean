import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 65467, payload cursor 32727, depth 20, 29 tokens. -/
theorem chunk1959 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 41 65467 32727 (pathBox rootBox [(true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (65496, 32742) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
