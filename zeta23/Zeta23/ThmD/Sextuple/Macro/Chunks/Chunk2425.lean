import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 79085, payload cursor 39532, depth 36, 3 tokens. -/
theorem chunk2425 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 25 79085 39532 (pathBox rootBox [(true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (true, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (79088, 39534) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
