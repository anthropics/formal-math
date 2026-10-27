import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 68614, payload cursor 34300, depth 17, 1 tokens. -/
theorem chunk2071 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 68614 34300 (pathBox rootBox [(false, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (68615, 34301) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
