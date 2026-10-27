import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 10903, payload cursor 5445, depth 18, 9 tokens. -/
theorem chunk0342 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 10903 5445 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (10912, 5450) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
