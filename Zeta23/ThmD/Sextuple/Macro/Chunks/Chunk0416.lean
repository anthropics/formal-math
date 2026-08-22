import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 12946, payload cursor 6464, depth 34, 7 tokens. -/
theorem chunk0416 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 27 12946 6464 (pathBox rootBox [(true, 0), (true, 3), (false, 1), (false, 2), (true, 4), (true, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (12953, 6468) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
