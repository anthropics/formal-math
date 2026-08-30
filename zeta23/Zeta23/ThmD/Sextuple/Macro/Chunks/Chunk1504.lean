import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 49987, payload cursor 24987, depth 16, 19 tokens. -/
theorem chunk1504 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 49987 24987 (pathBox rootBox [(false, 2), (true, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (50006, 24997) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
