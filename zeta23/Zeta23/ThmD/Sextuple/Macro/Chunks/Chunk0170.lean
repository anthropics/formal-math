import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 6020, payload cursor 3000, depth 36, 1 tokens. -/
theorem chunk0170 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 25 6020 3000 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (6021, 3001) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
