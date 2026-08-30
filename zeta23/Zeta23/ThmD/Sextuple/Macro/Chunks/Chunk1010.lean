import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 34430, payload cursor 17206, depth 29, 83 tokens. -/
theorem chunk1010 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 32 34430 17206 (pathBox rootBox [(false, 0), (false, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (34513, 17248) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
