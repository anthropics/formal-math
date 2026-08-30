import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 88186, payload cursor 44085, depth 31, 29 tokens. -/
theorem chunk2714 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 30 88186 44085 (pathBox rootBox [(true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (false, 2), (false, 4), (true, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (88215, 44100) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
