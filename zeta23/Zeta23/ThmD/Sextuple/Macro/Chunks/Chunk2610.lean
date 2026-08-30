import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 85470, payload cursor 42732, depth 9, 69 tokens. -/
theorem chunk2610 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 52 85470 42732 (pathBox rootBox [(true, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (85539, 42767) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
