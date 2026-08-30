import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 83381, payload cursor 41684, depth 18, 5 tokens. -/
theorem chunk2573 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 83381 41684 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (83386, 41687) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
