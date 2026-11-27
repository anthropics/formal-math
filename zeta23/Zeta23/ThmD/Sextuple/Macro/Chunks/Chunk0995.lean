import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 34220, payload cursor 17104, depth 19, 3 tokens. -/
theorem chunk0995 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 34220 17104 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (34223, 17106) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
