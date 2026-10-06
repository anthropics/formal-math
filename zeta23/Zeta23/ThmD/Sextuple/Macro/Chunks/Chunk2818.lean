import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 91425, payload cursor 45707, depth 15, 31 tokens. -/
theorem chunk2818 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 46 91425 45707 (pathBox rootBox [(true, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (91456, 45723) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
