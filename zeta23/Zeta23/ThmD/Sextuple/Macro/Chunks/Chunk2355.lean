import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 76367, payload cursor 38177, depth 16, 11 tokens. -/
theorem chunk2355 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 76367 38177 (pathBox rootBox [(false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (76378, 38183) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
