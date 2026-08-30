import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 97831, payload cursor 48910, depth 13, 69 tokens. -/
theorem chunk2932 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 97831 48910 (pathBox rootBox [(false, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (97900, 48945) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
