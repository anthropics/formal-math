import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 76533, payload cursor 38260, depth 16, 15 tokens. -/
theorem chunk2360 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 76533 38260 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (76548, 38268) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
