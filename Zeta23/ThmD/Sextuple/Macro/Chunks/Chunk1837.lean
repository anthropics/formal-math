import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 61045, payload cursor 30516, depth 18, 23 tokens. -/
theorem chunk1837 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 61045 30516 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (61068, 30528) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
