import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 82051, payload cursor 41019, depth 17, 85 tokens. -/
theorem chunk2535 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 82051 41019 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (82136, 41062) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
