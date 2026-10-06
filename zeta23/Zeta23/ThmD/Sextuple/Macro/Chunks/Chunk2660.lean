import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 86711, payload cursor 43345, depth 34, 1 tokens. -/
theorem chunk2660 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 27 86711 43345 (pathBox rootBox [(false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (false, 2), (true, 4), (true, 0), (true, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (86712, 43346) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
