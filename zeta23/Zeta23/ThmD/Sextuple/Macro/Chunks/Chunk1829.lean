import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 60852, payload cursor 30420, depth 17, 7 tokens. -/
theorem chunk1829 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 60852 30420 (pathBox rootBox [(false, 1), (true, 2), (true, 4), (true, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (60859, 30424) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
