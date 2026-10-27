import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 20025, payload cursor 10003, depth 33, 31 tokens. -/
theorem chunk0671 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 28 20025 10003 (pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (false, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (20056, 10019) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
