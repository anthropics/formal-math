import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 37027, payload cursor 18504, depth 36, 31 tokens. -/
theorem chunk1101 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 25 37027 18504 (pathBox rootBox [(true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (true, 4), (false, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (37058, 18520) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
