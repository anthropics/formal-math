import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 8389, payload cursor 4186, depth 32, 1 tokens. -/
theorem chunk0258 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 29 8389 4186 (pathBox rootBox [(true, 1), (false, 2), (true, 4), (false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (8390, 4187) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
