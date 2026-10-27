import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 52426, payload cursor 26206, depth 16, 41 tokens. -/
theorem chunk1584 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 52426 26206 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (52467, 26227) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
