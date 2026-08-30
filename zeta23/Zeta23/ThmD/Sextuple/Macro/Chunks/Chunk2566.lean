import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 83064, payload cursor 41526, depth 17, 85 tokens. -/
theorem chunk2566 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 83064 41526 (pathBox rootBox [(true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (83149, 41569) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
