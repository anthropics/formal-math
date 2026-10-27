import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 15105, payload cursor 7543, depth 37, 23 tokens. -/
theorem chunk0501 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 24 15105 7543 (pathBox rootBox [(true, 1), (false, 2), (true, 4), (false, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (false, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (15128, 7555) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
