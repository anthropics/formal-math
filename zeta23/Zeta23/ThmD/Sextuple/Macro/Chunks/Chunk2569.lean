import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 83204, payload cursor 41596, depth 17, 81 tokens. -/
theorem chunk2569 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 83204 41596 (pathBox rootBox [(true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (83285, 41637) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
