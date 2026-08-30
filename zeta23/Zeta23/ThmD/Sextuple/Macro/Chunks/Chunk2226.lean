import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 72869, payload cursor 36427, depth 28, 7 tokens. -/
theorem chunk2226 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 33 72869 36427 (pathBox rootBox [(true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (72876, 36431) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
