import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 50910, payload cursor 25448, depth 22, 1 tokens. -/
theorem chunk1540 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 39 50910 25448 (pathBox rootBox [(false, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (50911, 25449) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
