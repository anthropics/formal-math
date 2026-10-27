import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 64673, payload cursor 32331, depth 21, 47 tokens. -/
theorem chunk1929 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 64673 32331 (pathBox rootBox [(true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (64720, 32355) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
