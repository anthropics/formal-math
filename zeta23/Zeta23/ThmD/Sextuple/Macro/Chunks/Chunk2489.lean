import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 80469, payload cursor 40226, depth 30, 45 tokens. -/
theorem chunk2489 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 31 80469 40226 (pathBox rootBox [(false, 4), (true, 0), (true, 3), (false, 1), (true, 2), (true, 4), (true, 0), (false, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (80514, 40249) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
