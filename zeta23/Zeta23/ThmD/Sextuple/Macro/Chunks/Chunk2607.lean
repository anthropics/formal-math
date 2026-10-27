import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 85323, payload cursor 42657, depth 13, 31 tokens. -/
theorem chunk2607 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 85323 42657 (pathBox rootBox [(true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (85354, 42673) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
