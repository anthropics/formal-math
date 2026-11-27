import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 75190, payload cursor 37589, depth 17, 95 tokens. -/
theorem chunk2318 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 75190 37589 (pathBox rootBox [(true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (75285, 37637) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
