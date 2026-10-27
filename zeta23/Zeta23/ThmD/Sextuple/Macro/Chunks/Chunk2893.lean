import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 95349, payload cursor 47672, depth 8, 93 tokens. -/
theorem chunk2893 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 53 95349 47672 (pathBox rootBox [(true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (95442, 47719) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
