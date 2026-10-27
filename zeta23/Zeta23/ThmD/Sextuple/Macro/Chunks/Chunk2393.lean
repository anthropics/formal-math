import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 77980, payload cursor 38982, depth 25, 1 tokens. -/
theorem chunk2393 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 36 77980 38982 (pathBox rootBox [(false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (77981, 38983) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
