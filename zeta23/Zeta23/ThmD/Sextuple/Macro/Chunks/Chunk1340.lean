import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 44329, payload cursor 22158, depth 16, 17 tokens. -/
theorem chunk1340 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 44329 22158 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (44346, 22167) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
