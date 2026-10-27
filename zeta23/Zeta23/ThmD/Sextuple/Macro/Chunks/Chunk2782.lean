import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 90208, payload cursor 45097, depth 19, 1 tokens. -/
theorem chunk2782 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 90208 45097 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (90209, 45098) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
