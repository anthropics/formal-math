import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 87790, payload cursor 43888, depth 18, 1 tokens. -/
theorem chunk2698 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 43 87790 43888 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (87791, 43889) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
