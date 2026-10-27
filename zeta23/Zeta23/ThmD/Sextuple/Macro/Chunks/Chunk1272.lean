import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 42020, payload cursor 21001, depth 34, 81 tokens. -/
theorem chunk1272 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 27 42020 21001 (pathBox rootBox [(false, 0), (true, 3), (false, 1), (true, 2), (true, 4), (true, 0), (false, 3), (true, 1), (true, 2), (true, 4), (false, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (42101, 21042) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
