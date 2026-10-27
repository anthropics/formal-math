import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 60959, payload cursor 30474, depth 21, 33 tokens. -/
theorem chunk1834 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 60959 30474 (pathBox rootBox [(true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (60992, 30491) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
