import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 90081, payload cursor 45033, depth 17, 17 tokens. -/
theorem chunk2778 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 90081 45033 (pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (90098, 45042) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
