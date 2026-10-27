import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 9040, payload cursor 4513, depth 21, 1 tokens. -/
theorem chunk0279 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 9040 4513 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (9041, 4514) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
