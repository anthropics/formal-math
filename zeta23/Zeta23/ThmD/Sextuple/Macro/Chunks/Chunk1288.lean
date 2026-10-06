import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 42501, payload cursor 21241, depth 34, 71 tokens. -/
theorem chunk1288 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 27 42501 21241 (pathBox rootBox [(false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (42572, 21277) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
