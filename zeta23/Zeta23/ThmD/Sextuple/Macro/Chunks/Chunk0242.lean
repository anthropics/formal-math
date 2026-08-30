import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 7895, payload cursor 3939, depth 28, 1 tokens. -/
theorem chunk0242 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 33 7895 3939 (pathBox rootBox [(false, 3), (true, 1), (false, 2), (false, 4), (true, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (7896, 3940) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
