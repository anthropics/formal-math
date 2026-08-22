import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 97022, payload cursor 48506, depth 12, 93 tokens. -/
theorem chunk2919 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 97022 48506 (pathBox rootBox [(true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97115, 48553) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
