import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 83165, payload cursor 41576, depth 17, 39 tokens. -/
theorem chunk2568 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 83165 41576 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (83204, 41596) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
