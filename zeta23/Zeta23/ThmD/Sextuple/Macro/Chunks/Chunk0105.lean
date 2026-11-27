import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 4374, payload cursor 2180, depth 18, 1 tokens. -/
theorem chunk0105 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 4374 2180 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (4375, 2181) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
