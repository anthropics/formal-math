import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 83151, payload cursor 41569, depth 16, 13 tokens. -/
theorem chunk2567 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 83151 41569 (pathBox rootBox [(false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (83164, 41576) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
