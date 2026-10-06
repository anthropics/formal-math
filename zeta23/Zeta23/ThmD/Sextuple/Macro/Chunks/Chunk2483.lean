import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 80350, payload cursor 40168, depth 21, 1 tokens. -/
theorem chunk2483 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 80350 40168 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (80351, 40169) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
