import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 31985, payload cursor 15986, depth 19, 1 tokens. -/
theorem chunk0920 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 31985 15986 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (31986, 15987) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
