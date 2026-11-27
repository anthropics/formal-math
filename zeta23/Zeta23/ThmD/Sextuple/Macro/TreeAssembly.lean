import Zeta23.ThmD.Sextuple.Macro.TreeWords
import Zeta23.ThmD.Sextuple.Macro.Assembly.Part029
import Zeta23.ThmD.Sextuple.Macro.AssemblyStep

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- The complete replay from the root consumes both streams exactly. -/
theorem rootReplay :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 61 0 0 (rootBox) =
      some (99507, 49754) := by
  have h := node2967
  simpa only [pathBox] using h

end Zeta23.ThmD.Sextuple.MacroPrototype
