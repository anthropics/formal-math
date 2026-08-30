import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 64770, payload cursor 32377, depth 23, 1 tokens. -/
theorem chunk1937 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 38 64770 32377 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (64771, 32378) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
