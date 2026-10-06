import Zeta23.ThmD.Sextuple.A1275.TreeWords

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

/-- Calibration chunk 62: exactly 99 topology tokens, 50 payloads. -/
theorem improvedChunkCalibration :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream
      56 2455 1218 (improvedPathBox improvedRootBox [(false, ⟨0, by decide⟩), (true, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (true, ⟨4, by decide⟩), (true, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (true, ⟨0, by decide⟩), (true, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (true, ⟨2, by decide⟩), (true, ⟨4, by decide⟩), (true, ⟨0, by decide⟩), (true, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (true, ⟨2, by decide⟩), (true, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (2554, 1268) := by
  decide +kernel

#print axioms improvedChunkCalibration
end Zeta23.ThmD.Sextuple.MacroPrototype
