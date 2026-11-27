import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 65716, payload cursor 32852, depth 15, 57 tokens. -/
theorem chunk1972 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 65716 32852 (pathBox rootBox [(true, 4), (true, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (65773, 32881) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
