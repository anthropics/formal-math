import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 77592, payload cursor 38791, depth 13, 65 tokens. -/
theorem chunk2380 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 77592 38791 (pathBox rootBox [(true, 3), (false, 1), (false, 2), (false, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (77657, 38824) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
