import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 91323, payload cursor 45655, depth 20, 1 tokens. -/
theorem chunk2815 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 41 91323 45655 (pathBox rootBox [(false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (91324, 45656) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
