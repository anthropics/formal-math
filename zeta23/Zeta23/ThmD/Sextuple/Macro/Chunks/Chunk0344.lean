import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 10921, payload cursor 5454, depth 20, 13 tokens. -/
theorem chunk0344 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 41 10921 5454 (pathBox rootBox [(false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (10934, 5461) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
