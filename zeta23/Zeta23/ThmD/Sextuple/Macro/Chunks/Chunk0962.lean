import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 33162, payload cursor 16573, depth 28, 1 tokens. -/
theorem chunk0962 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 33 33162 16573 (pathBox rootBox [(false, 3), (true, 1), (true, 2), (true, 4), (false, 0), (false, 3), (false, 1), (true, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (true, 0), (true, 3), (true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (33163, 16574) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
