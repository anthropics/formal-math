import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 85238, payload cursor 42614, depth 13, 85 tokens. -/
theorem chunk2606 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 85238 42614 (pathBox rootBox [(false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (85323, 42657) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
