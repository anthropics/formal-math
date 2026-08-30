import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 98512, payload cursor 49253, depth 9, 1 tokens. -/
theorem chunk2944 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 52 98512 49253 (pathBox rootBox [(true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98513, 49254) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
