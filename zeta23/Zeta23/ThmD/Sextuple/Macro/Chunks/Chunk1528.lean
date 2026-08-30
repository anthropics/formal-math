import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 50541, payload cursor 25263, depth 27, 19 tokens. -/
theorem chunk1528 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 34 50541 25263 (pathBox rootBox [(false, 1), (true, 2), (true, 4), (true, 0), (false, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (50560, 25273) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
