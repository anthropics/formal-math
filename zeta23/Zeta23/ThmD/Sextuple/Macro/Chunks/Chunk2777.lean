import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 90051, payload cursor 45020, depth 15, 25 tokens. -/
theorem chunk2777 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 90051 45020 (pathBox rootBox [(true, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (90076, 45033) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
