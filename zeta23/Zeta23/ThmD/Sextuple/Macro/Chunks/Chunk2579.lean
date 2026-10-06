import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 83658, payload cursor 41823, depth 17, 33 tokens. -/
theorem chunk2579 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 83658 41823 (pathBox rootBox [(true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (83691, 41840) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
