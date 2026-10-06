import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 90223, payload cursor 45103, depth 28, 77 tokens. -/
theorem chunk2788 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 33 90223 45103 (pathBox rootBox [(false, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (false, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (90300, 45142) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
