import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 8986, payload cursor 4486, depth 17, 1 tokens. -/
theorem chunk0275 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 8986 4486 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (8987, 4487) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
