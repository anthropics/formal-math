import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 9803, payload cursor 4892, depth 34, 27 tokens. -/
theorem chunk0309 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 27 9803 4892 (pathBox rootBox [(false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (9830, 4906) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
