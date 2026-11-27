import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 89921, payload cursor 44954, depth 16, 35 tokens. -/
theorem chunk2775 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 89921 44954 (pathBox rootBox [(false, 2), (false, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (89956, 44972) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
