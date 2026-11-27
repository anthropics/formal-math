import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 95768, payload cursor 47880, depth 10, 59 tokens. -/
theorem chunk2899 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 51 95768 47880 (pathBox rootBox [(true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (95827, 47910) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
