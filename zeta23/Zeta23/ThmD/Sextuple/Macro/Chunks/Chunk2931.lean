import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 97759, payload cursor 48874, depth 13, 71 tokens. -/
theorem chunk2931 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 97759 48874 (pathBox rootBox [(true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (97830, 48910) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
