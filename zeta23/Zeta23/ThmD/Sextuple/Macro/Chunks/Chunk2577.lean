import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 83569, payload cursor 41778, depth 16, 17 tokens. -/
theorem chunk2577 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 83569 41778 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (83586, 41787) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
