import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 75435, payload cursor 37711, depth 18, 75 tokens. -/
theorem chunk2325 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 75435 37711 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (75510, 37749) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
