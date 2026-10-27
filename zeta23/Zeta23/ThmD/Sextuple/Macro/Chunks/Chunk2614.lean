import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 85556, payload cursor 42770, depth 20, 1 tokens. -/
theorem chunk2614 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 41 85556 42770 (pathBox rootBox [(false, 4), (true, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (85557, 42771) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
