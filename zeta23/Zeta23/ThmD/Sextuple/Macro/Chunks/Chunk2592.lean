import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 84407, payload cursor 42198, depth 14, 53 tokens. -/
theorem chunk2592 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 47 84407 42198 (pathBox rootBox [(true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (84460, 42225) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
