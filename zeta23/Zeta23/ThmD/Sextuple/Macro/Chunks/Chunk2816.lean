import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 91325, payload cursor 45656, depth 21, 91 tokens. -/
theorem chunk2816 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 91325 45656 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (91416, 45702) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
