import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 64360, payload cursor 32174, depth 17, 7 tokens. -/
theorem chunk1915 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 64360 32174 (pathBox rootBox [(false, 1), (true, 2), (true, 4), (false, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (64367, 32178) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
