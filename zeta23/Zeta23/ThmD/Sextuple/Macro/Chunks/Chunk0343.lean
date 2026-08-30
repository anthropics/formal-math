import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 10913, payload cursor 5450, depth 19, 7 tokens. -/
theorem chunk0343 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 10913 5450 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (10920, 5454) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
