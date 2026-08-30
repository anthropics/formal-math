import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 98016, payload cursor 49003, depth 13, 31 tokens. -/
theorem chunk2935 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 98016 49003 (pathBox rootBox [(true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98047, 49019) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
