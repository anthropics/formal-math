import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 84258, payload cursor 42125, depth 12, 43 tokens. -/
theorem chunk2589 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 84258 42125 (pathBox rootBox [(true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (84301, 42147) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
