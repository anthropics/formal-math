import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 10899, payload cursor 5443, depth 16, 1 tokens. -/
theorem chunk0340 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 10899 5443 (pathBox rootBox [(false, 2), (true, 4), (true, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (10900, 5444) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
