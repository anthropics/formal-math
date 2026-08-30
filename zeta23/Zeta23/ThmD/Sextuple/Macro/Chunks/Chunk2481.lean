import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 80346, payload cursor 40166, depth 19, 1 tokens. -/
theorem chunk2481 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 80346 40166 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (80347, 40167) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
