import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 83027, payload cursor 41507, depth 17, 37 tokens. -/
theorem chunk2565 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 83027 41507 (pathBox rootBox [(false, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (83064, 41526) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
