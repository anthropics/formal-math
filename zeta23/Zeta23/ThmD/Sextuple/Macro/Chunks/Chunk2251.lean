import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 73409, payload cursor 36696, depth 29, 1 tokens. -/
theorem chunk2251 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 32 73409 36696 (pathBox rootBox [(false, 0), (false, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (true, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (73410, 36697) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
