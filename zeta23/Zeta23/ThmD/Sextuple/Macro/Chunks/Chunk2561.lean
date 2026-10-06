import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 82949, payload cursor 41467, depth 27, 11 tokens. -/
theorem chunk2561 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 34 82949 41467 (pathBox rootBox [(true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (82960, 41473) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
