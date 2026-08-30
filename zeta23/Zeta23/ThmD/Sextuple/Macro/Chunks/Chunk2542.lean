import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 82354, payload cursor 41170, depth 19, 1 tokens. -/
theorem chunk2542 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 82354 41170 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (82355, 41171) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
