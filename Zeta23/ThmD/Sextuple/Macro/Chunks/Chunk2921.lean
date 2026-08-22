import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 97213, payload cursor 48602, depth 12, 35 tokens. -/
theorem chunk2921 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 97213 48602 (pathBox rootBox [(true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97248, 48620) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
