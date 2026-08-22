import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 39939, payload cursor 19961, depth 33, 1 tokens. -/
theorem chunk1206 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 28 39939 19961 (pathBox rootBox [(true, 3), (false, 1), (true, 2), (true, 4), (false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (39940, 19962) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
