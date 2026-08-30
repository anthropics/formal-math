import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 64757, payload cursor 32371, depth 16, 1 tokens. -/
theorem chunk1931 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 64757 32371 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (64758, 32372) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
