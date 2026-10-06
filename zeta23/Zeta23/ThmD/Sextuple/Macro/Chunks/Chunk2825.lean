import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 91551, payload cursor 45768, depth 22, 1 tokens. -/
theorem chunk2825 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 39 91551 45768 (pathBox rootBox [(false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (91552, 45769) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
