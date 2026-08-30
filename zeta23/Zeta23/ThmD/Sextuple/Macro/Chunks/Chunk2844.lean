import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 92293, payload cursor 46140, depth 16, 89 tokens. -/
theorem chunk2844 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 92293 46140 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (92382, 46185) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
