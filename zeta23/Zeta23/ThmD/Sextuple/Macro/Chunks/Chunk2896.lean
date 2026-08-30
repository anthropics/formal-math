import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 95584, payload cursor 47787, depth 12, 73 tokens. -/
theorem chunk2896 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 95584 47787 (pathBox rootBox [(true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (95657, 47824) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
