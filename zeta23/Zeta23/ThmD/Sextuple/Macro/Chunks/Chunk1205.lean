import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 39912, payload cursor 19947, depth 36, 27 tokens. -/
theorem chunk1205 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 25 39912 19947 (pathBox rootBox [(true, 2), (true, 4), (true, 0), (false, 3), (false, 1), (true, 2), (true, 4), (false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (39939, 19961) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
