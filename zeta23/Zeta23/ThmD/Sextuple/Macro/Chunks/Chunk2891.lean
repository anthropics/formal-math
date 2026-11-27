import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 95173, payload cursor 47583, depth 10, 87 tokens. -/
theorem chunk2891 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 51 95173 47583 (pathBox rootBox [(true, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (95260, 47627) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
