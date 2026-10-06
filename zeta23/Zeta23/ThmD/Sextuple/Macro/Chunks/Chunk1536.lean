import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 50871, payload cursor 25429, depth 17, 1 tokens. -/
theorem chunk1536 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 50871 25429 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (true, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (50872, 25430) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
