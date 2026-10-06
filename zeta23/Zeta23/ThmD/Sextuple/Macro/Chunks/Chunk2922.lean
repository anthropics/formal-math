import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 97248, payload cursor 48620, depth 10, 61 tokens. -/
theorem chunk2922 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 51 97248 48620 (pathBox rootBox [(true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97309, 48651) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
