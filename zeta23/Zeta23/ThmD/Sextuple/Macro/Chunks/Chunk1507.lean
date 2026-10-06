import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 50029, payload cursor 25008, depth 19, 1 tokens. -/
theorem chunk1507 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 42 50029 25008 (pathBox rootBox [(false, 0), (true, 3), (true, 1), (true, 2), (true, 4), (false, 0), (true, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (50030, 25009) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
