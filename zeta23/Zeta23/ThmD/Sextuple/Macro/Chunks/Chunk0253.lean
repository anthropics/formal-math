import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 8258, payload cursor 4121, depth 31, 3 tokens. -/
theorem chunk0253 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 30 8258 4121 (pathBox rootBox [(true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (8261, 4123) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
