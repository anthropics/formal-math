import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 7081, payload cursor 3531, depth 36, 7 tokens. -/
theorem chunk0204 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 25 7081 3531 (pathBox rootBox [(true, 2), (false, 4), (true, 0), (true, 3), (false, 1), (false, 2), (true, 4), (false, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (7088, 3535) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
