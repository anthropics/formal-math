import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 88280, payload cursor 44133, depth 16, 99 tokens. -/
theorem chunk2718 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 88280 44133 (pathBox rootBox [(false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (88379, 44183) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
