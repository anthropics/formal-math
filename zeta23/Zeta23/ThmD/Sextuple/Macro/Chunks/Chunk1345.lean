import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 44374, payload cursor 22180, depth 22, 1 tokens. -/
theorem chunk1345 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 39 44374 22180 (pathBox rootBox [(false, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (44375, 22181) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
