import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 52744, payload cursor 26362, depth 36, 1 tokens. -/
theorem chunk1600 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 25 52744 26362 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (52745, 26363) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
