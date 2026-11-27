import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 84740, payload cursor 42366, depth 12, 45 tokens. -/
theorem chunk2598 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 84740 42366 (pathBox rootBox [(true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (84785, 42389) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
