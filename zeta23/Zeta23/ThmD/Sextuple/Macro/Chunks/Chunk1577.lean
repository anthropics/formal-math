import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 52278, payload cursor 26133, depth 16, 9 tokens. -/
theorem chunk1577 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 52278 26133 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (52287, 26138) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
