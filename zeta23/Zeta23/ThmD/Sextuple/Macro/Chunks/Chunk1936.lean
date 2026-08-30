import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 64768, payload cursor 32376, depth 22, 1 tokens. -/
theorem chunk1936 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 39 64768 32376 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (64769, 32377) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
