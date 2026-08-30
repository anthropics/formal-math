import Zeta23.ThmD.Sextuple.A1285.Layout
import Zeta23.ThmD.Sextuple.A1285.Assembly.Part301

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype.A1285
open Zeta23.ThmD.Sextuple

/-- The complete replay consumes both logical streams exactly. -/
theorem improvedRootReplay :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream
      74 0 0 improvedRootBox = some (1771973, 885987) := by
  have h := improvedNode30151
  simpa only [improvedPathBox] using h

#print axioms improvedRootReplay

end Zeta23.ThmD.Sextuple.MacroPrototype.A1285
