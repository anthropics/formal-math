import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 64772, payload cursor 32378, depth 24, 1 tokens. -/
theorem chunk1938 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 37 64772 32378 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (64773, 32379) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
