import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 73204, payload cursor 36595, depth 17, 1 tokens. -/
theorem chunk2242 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 73204 36595 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (73205, 36596) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
