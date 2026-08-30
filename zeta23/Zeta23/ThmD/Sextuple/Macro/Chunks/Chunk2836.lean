import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 91829, payload cursor 45908, depth 16, 39 tokens. -/
theorem chunk2836 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 91829 45908 (pathBox rootBox [(true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (91868, 45928) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
