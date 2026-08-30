import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 65358, payload cursor 32672, depth 16, 1 tokens. -/
theorem chunk1953 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 65358 32672 (pathBox rootBox [(false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (65359, 32673) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
