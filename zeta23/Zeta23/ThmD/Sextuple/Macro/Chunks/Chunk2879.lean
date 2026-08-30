import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 94478, payload cursor 47232, depth 16, 47 tokens. -/
theorem chunk2879 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 94478 47232 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (94525, 47256) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
