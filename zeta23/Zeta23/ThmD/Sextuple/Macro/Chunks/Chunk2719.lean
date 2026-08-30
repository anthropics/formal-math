import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 88380, payload cursor 44183, depth 17, 1 tokens. -/
theorem chunk2719 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 88380 44183 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (88381, 44184) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
