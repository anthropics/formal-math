import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 97309, payload cursor 48651, depth 9, 65 tokens. -/
theorem chunk2923 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 52 97309 48651 (pathBox rootBox [(true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97374, 48684) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
