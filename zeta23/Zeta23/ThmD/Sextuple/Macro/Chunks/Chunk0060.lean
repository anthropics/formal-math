import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 2895, payload cursor 1440, depth 18, 1 tokens. -/
theorem chunk0060 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 2895 1440 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (2896, 1441) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
