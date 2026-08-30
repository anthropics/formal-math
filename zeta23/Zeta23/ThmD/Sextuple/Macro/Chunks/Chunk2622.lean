import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 85636, payload cursor 42810, depth 28, 29 tokens. -/
theorem chunk2622 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 33 85636 42810 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (85665, 42825) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
