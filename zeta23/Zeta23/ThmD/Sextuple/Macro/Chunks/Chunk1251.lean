import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 41427, payload cursor 20706, depth 22, 1 tokens. -/
theorem chunk1251 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 39 41427 20706 (pathBox rootBox [(false, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (41428, 20707) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
