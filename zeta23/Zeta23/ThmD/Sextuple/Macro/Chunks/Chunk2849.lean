import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 92595, payload cursor 46291, depth 15, 85 tokens. -/
theorem chunk2849 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 92595 46291 (pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (92680, 46334) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
