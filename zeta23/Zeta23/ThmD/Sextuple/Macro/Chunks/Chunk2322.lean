import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 75397, payload cursor 37693, depth 15, 21 tokens. -/
theorem chunk2322 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 75397 37693 (pathBox rootBox [(true, 4), (true, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (75418, 37704) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
