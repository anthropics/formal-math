import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 64540, payload cursor 32264, depth 18, 5 tokens. -/
theorem chunk1924 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 64540 32264 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (64545, 32267) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
