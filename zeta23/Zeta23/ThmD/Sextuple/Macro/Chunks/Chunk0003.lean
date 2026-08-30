import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 22, payload cursor 3, depth 19, 1 tokens. -/
theorem chunk0003 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 22 3 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (23, 4) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
