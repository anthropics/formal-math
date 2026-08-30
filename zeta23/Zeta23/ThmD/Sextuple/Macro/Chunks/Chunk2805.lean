import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 90943, payload cursor 45465, depth 21, 17 tokens. -/
theorem chunk2805 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 90943 45465 (pathBox rootBox [(true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (90960, 45474) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
