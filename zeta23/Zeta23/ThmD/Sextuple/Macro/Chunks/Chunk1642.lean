import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 54213, payload cursor 27097, depth 36, 51 tokens. -/
theorem chunk1642 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 25 54213 27097 (pathBox rootBox [(true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (54264, 27123) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
