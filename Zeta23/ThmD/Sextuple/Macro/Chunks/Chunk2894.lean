import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 95450, payload cursor 47719, depth 13, 89 tokens. -/
theorem chunk2894 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 95450 47719 (pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (95539, 47764) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
