import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 96024, payload cursor 48010, depth 6, 83 tokens. -/
theorem chunk2903 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 55 96024 48010 (pathBox rootBox [(true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96107, 48052) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
