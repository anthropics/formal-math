import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 65368, payload cursor 32677, depth 21, 99 tokens. -/
theorem chunk1958 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 65368 32677 (pathBox rootBox [(true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (65467, 32727) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
