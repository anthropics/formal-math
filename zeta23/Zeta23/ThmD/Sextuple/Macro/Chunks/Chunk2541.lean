import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 82352, payload cursor 41169, depth 18, 1 tokens. -/
theorem chunk2541 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 82352 41169 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (82353, 41170) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
