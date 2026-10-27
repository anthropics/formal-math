import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 82240, payload cursor 41113, depth 16, 33 tokens. -/
theorem chunk2539 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 82240 41113 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (82273, 41130) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
