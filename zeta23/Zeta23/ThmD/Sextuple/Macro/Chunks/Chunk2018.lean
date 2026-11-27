import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 66932, payload cursor 33459, depth 19, 1 tokens. -/
theorem chunk2018 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 66932 33459 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (66933, 33460) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
