import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 75612, payload cursor 37799, depth 16, 25 tokens. -/
theorem chunk2329 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 45 75612 37799 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (75637, 37812) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
