import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 45335, payload cursor 22659, depth 30, 83 tokens. -/
theorem chunk1380 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 31 45335 22659 (pathBox rootBox [(false, 4), (true, 0), (true, 3), (false, 1), (true, 2), (true, 4), (true, 0), (false, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (45418, 22701) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
