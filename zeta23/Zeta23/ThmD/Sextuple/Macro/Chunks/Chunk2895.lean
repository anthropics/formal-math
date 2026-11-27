import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 95539, payload cursor 47764, depth 13, 45 tokens. -/
theorem chunk2895 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 95539 47764 (pathBox rootBox [(true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (95584, 47787) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
