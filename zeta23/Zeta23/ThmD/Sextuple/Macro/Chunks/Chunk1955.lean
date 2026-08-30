import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 65362, payload cursor 32674, depth 18, 1 tokens. -/
theorem chunk1955 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 65362 32674 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (65363, 32675) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
