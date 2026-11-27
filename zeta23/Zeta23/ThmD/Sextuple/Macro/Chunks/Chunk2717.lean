import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 88271, payload cursor 44129, depth 21, 7 tokens. -/
theorem chunk2717 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 88271 44129 (pathBox rootBox [(true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (88278, 44133) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
