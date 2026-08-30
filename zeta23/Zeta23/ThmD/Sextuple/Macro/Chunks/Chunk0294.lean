import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 9422, payload cursor 4703, depth 32, 1 tokens. -/
theorem chunk0294 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 29 9422 4703 (pathBox rootBox [(true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (false, 2), (true, 4), (false, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (9423, 4704) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
