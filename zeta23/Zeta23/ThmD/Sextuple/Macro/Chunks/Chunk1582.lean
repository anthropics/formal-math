import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 52302, payload cursor 26145, depth 21, 93 tokens. -/
theorem chunk1582 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 40 52302 26145 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (52395, 26192) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
