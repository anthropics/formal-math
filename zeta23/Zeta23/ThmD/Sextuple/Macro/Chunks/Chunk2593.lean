import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 84460, payload cursor 42225, depth 13, 65 tokens. -/
theorem chunk2593 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 84460 42225 (pathBox rootBox [(true, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (84525, 42258) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
