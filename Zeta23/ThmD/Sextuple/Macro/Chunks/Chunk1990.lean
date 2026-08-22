import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 66194, payload cursor 33090, depth 17, 15 tokens. -/
theorem chunk1990 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 66194 33090 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (66209, 33098) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
