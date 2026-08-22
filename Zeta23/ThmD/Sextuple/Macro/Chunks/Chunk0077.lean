import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 3271, payload cursor 1627, depth 32, 3 tokens. -/
theorem chunk0077 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 29 3271 1627 (pathBox rootBox [(true, 1), (true, 2), (true, 4), (true, 0), (false, 3), (true, 1), (false, 2), (true, 4), (false, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (3274, 1629) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
