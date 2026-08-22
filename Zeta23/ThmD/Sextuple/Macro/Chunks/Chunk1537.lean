import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 50873, payload cursor 25430, depth 18, 17 tokens. -/
theorem chunk1537 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 50873 25430 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (50890, 25439) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
