import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 81217, payload cursor 40600, depth 32, 93 tokens. -/
theorem chunk2508 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 29 81217 40600 (pathBox rootBox [(true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (false, 1), (true, 2), (true, 4), (true, 0), (false, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (81310, 40647) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
