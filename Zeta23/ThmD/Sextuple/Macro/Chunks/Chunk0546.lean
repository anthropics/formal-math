import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 16420, payload cursor 8203, depth 21, 1 tokens. -/
theorem chunk0546 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 16420 8203 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (16421, 8204) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
