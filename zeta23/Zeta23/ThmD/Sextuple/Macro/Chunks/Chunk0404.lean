import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 12599, payload cursor 6290, depth 32, 75 tokens. -/
theorem chunk0404 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 29 12599 6290 (pathBox rootBox [(false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (12674, 6328) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
