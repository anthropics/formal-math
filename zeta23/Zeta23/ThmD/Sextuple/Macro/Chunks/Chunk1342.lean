import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 44349, payload cursor 22168, depth 18, 1 tokens. -/
theorem chunk1342 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 44349 22168 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (44350, 22169) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
