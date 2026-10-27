import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 87698, payload cursor 43842, depth 16, 89 tokens. -/
theorem chunk2696 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 87698 43842 (pathBox rootBox [(false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (87787, 43887) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
