import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 98511, payload cursor 49252, depth 10, 1 tokens. -/
theorem chunk2943 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 51 98511 49252 (pathBox rootBox [(true, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98512, 49253) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
