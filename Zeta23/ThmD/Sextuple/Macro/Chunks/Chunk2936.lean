import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 98047, payload cursor 49019, depth 12, 45 tokens. -/
theorem chunk2936 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 98047 49019 (pathBox rootBox [(true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98092, 49042) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
