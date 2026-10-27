import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 4416, payload cursor 2201, depth 21, 1 tokens. -/
theorem chunk0108 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 4416 2201 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (4417, 2202) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
