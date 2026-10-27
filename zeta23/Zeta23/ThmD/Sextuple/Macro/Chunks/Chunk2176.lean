import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 71341, payload cursor 35666, depth 13, 65 tokens. -/
theorem chunk2176 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 71341 35666 (pathBox rootBox [(true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (71406, 35699) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
