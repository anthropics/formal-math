import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 97116, payload cursor 48553, depth 12, 97 tokens. -/
theorem chunk2920 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 97116 48553 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97213, 48602) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
