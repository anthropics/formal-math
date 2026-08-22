import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 65120, payload cursor 32552, depth 28, 75 tokens. -/
theorem chunk1949 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 33 65120 32552 (pathBox rootBox [(true, 3), (false, 1), (true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (65195, 32590) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
