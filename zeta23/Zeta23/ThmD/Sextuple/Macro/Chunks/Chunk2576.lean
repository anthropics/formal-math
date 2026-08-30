import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 83516, payload cursor 41753, depth 14, 49 tokens. -/
theorem chunk2576 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 47 83516 41753 (pathBox rootBox [(true, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (83565, 41778) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
