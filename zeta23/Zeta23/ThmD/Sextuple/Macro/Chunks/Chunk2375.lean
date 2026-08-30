import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 77313, payload cursor 38652, depth 12, 87 tokens. -/
theorem chunk2375 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 77313 38652 (pathBox rootBox [(false, 1), (true, 2), (true, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (77400, 38696) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
