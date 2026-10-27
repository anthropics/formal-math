import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 90190, payload cursor 45088, depth 17, 15 tokens. -/
theorem chunk2780 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 90190 45088 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (90205, 45096) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
