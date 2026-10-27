import Zeta23.ThmD.Sextuple.Macro.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Subtree at topology cursor 59843, payload cursor 29915, depth 17, 21 tokens. -/
theorem chunk1796 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 44 59843 29915 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (true, 0), (false, 3), (true, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (59864, 29926) := by
  decide +kernel

end Zeta23.ThmD.Sextuple.MacroPrototype
