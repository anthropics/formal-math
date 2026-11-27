import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 82136, payload cursor 41062, depth 17, 29 tokens. -/
theorem chunk2536 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 82136 41062 (pathBox rootBox [(true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (82165, 41077) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
