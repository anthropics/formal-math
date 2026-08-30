import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 85558, payload cursor 42771, depth 21, 17 tokens. -/
theorem chunk2615 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 85558 42771 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (85575, 42780) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
