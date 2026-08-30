import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 1505, payload cursor 745, depth 17, 1 tokens. -/
theorem chunk0030 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 1505 745 (pathBox rootBox [(false, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (1506, 746) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
