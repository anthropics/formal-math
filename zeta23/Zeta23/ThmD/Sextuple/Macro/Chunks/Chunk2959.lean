import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 99062, payload cursor 49527, depth 10, 77 tokens. -/
theorem chunk2959 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 51 99062 49527 (pathBox rootBox [(true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99139, 49566) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
