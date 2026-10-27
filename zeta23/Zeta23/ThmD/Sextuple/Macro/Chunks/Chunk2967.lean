import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 99505, payload cursor 49752, depth 3, 1 tokens. -/
theorem chunk2967 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 58 99505 49752 (pathBox rootBox [(true, 3), (false, 1), (true, 2)]) =
      some (99506, 49753) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
