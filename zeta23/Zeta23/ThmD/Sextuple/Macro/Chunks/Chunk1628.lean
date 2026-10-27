import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 53750, payload cursor 26865, depth 37, 95 tokens. -/
theorem chunk1628 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 24 53750 26865 (pathBox rootBox [(false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (true, 1), (true, 2), (true, 4), (false, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (53845, 26913) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
