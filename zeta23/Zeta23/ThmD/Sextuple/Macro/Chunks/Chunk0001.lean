import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 18, payload cursor 1, depth 17, 1 tokens. -/
theorem chunk0001 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 18 1 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (19, 2) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
