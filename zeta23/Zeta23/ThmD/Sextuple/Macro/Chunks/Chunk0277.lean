import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 9012, payload cursor 4499, depth 19, 25 tokens. -/
theorem chunk0277 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 9012 4499 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (9037, 4512) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
