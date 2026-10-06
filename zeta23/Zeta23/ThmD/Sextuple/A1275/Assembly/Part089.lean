import Zeta23.ThmD.Sextuple.A1275.TreeWords
import Zeta23.ThmD.Sextuple.A1275.Assembly.Part088
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8902
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8903
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8904
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8905
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8906
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8907
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8908
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8909
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8910
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8911
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8912
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8913
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8914
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8915
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8916
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8917
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8918
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8919
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8920
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8921
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8922
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8923
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8924
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8925
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8926
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8927
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8928
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8929
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8930
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8931
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8932
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8933
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8934
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8935
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8936
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8937
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8938
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8939
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8940
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8941
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8942
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8943
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8944
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8945
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8946
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8947
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8948
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8949
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8950
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8951
import Zeta23.ThmD.Sextuple.A1275.Chunks.Chunk8952
import Zeta23.ThmD.Sextuple.Macro.AssemblyStep

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

theorem improvedNode8900 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 82 383045 191519 (improvedPathBox improvedRootBox [(false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (true, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (383640, 191817) :=
  replayAffineTree_split_step (fuel := 81) (t := 383045) (p := 191519)
    (axis := ⟨0, by decide⟩) (tm := 383573) (pm := 191783)
    (t' := 383640) (p' := 191817)
    (by decide +kernel) improvedNode8899 improvedChunk8902

theorem improvedNode8901 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 83 383044 191519 (improvedPathBox improvedRootBox [(false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (true, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (383707, 191851) :=
  replayAffineTree_split_step (fuel := 82) (t := 383044) (p := 191519)
    (axis := ⟨3, by decide⟩) (tm := 383640) (pm := 191817)
    (t' := 383707) (p' := 191851)
    (by decide +kernel) improvedNode8900 improvedChunk8903

theorem improvedNode8902 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 84 383043 191519 (improvedPathBox improvedRootBox [(false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (true, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (383786, 191891) :=
  replayAffineTree_split_step (fuel := 83) (t := 383043) (p := 191519)
    (axis := ⟨1, by decide⟩) (tm := 383707) (pm := 191851)
    (t' := 383786) (p' := 191891)
    (by decide +kernel) improvedNode8901 improvedChunk8904

theorem improvedNode8903 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 85 383042 191519 (improvedPathBox improvedRootBox [(false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (true, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (383879, 191938) :=
  replayAffineTree_split_step (fuel := 84) (t := 383042) (p := 191519)
    (axis := ⟨2, by decide⟩) (tm := 383786) (pm := 191891)
    (t' := 383879) (p' := 191938)
    (by decide +kernel) improvedNode8902 improvedChunk8905

theorem improvedNode8904 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 86 383041 191519 (improvedPathBox improvedRootBox [(false, ⟨0, by decide⟩), (true, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (383880, 191939) :=
  replayAffineTree_split_step (fuel := 85) (t := 383041) (p := 191519)
    (axis := ⟨4, by decide⟩) (tm := 383879) (pm := 191938)
    (t' := 383880) (p' := 191939)
    (by decide +kernel) improvedNode8903 improvedChunk8906

theorem improvedNode8905 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 87 383040 191519 (improvedPathBox improvedRootBox [(true, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (383881, 191940) :=
  replayAffineTree_split_step (fuel := 86) (t := 383040) (p := 191519)
    (axis := ⟨0, by decide⟩) (tm := 383880) (pm := 191939)
    (t' := 383881) (p' := 191940)
    (by decide +kernel) improvedNode8904 improvedChunk8907

theorem improvedNode8906 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 88 2 0 (improvedPathBox improvedRootBox [(false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (383881, 191940) :=
  replayAffineTree_split_step (fuel := 87) (t := 2) (p := 0)
    (axis := ⟨3, by decide⟩) (tm := 383040) (pm := 191519)
    (t' := 383881) (p' := 191940)
    (by decide +kernel) improvedNode8891 improvedNode8905

theorem improvedNode8907 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 76 383893 191940 (improvedPathBox improvedRootBox [(false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384006, 191997) :=
  replayAffineTree_split_step (fuel := 75) (t := 383893) (p := 191940)
    (axis := ⟨4, by decide⟩) (tm := 383971) (pm := 191979)
    (t' := 384006) (p' := 191997)
    (by decide +kernel) improvedChunk8908 improvedChunk8909

theorem improvedNode8908 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 77 383892 191940 (improvedPathBox improvedRootBox [(false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384059, 192024) :=
  replayAffineTree_split_step (fuel := 76) (t := 383892) (p := 191940)
    (axis := ⟨0, by decide⟩) (tm := 384006) (pm := 191997)
    (t' := 384059) (p' := 192024)
    (by decide +kernel) improvedNode8907 improvedChunk8910

theorem improvedNode8909 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 78 383891 191940 (improvedPathBox improvedRootBox [(false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384140, 192065) :=
  replayAffineTree_split_step (fuel := 77) (t := 383891) (p := 191940)
    (axis := ⟨3, by decide⟩) (tm := 384059) (pm := 192024)
    (t' := 384140) (p' := 192065)
    (by decide +kernel) improvedNode8908 improvedChunk8911

theorem improvedNode8910 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 78 384140 192065 (improvedPathBox improvedRootBox [(true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384247, 192119) :=
  replayAffineTree_split_step (fuel := 77) (t := 384140) (p := 192065)
    (axis := ⟨3, by decide⟩) (tm := 384214) (pm := 192102)
    (t' := 384247) (p' := 192119)
    (by decide +kernel) improvedChunk8912 improvedChunk8913

theorem improvedNode8911 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 79 383890 191940 (improvedPathBox improvedRootBox [(false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384247, 192119) :=
  replayAffineTree_split_step (fuel := 78) (t := 383890) (p := 191940)
    (axis := ⟨1, by decide⟩) (tm := 384140) (pm := 192065)
    (t' := 384247) (p' := 192119)
    (by decide +kernel) improvedNode8909 improvedNode8910

theorem improvedNode8912 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 78 384248 192119 (improvedPathBox improvedRootBox [(false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384377, 192184) :=
  replayAffineTree_split_step (fuel := 77) (t := 384248) (p := 192119)
    (axis := ⟨3, by decide⟩) (tm := 384344) (pm := 192167)
    (t' := 384377) (p' := 192184)
    (by decide +kernel) improvedChunk8914 improvedChunk8915

theorem improvedNode8913 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 79 384247 192119 (improvedPathBox improvedRootBox [(true, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384422, 192207) :=
  replayAffineTree_split_step (fuel := 78) (t := 384247) (p := 192119)
    (axis := ⟨1, by decide⟩) (tm := 384377) (pm := 192184)
    (t' := 384422) (p' := 192207)
    (by decide +kernel) improvedNode8912 improvedChunk8916

theorem improvedNode8914 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 80 383889 191940 (improvedPathBox improvedRootBox [(false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384422, 192207) :=
  replayAffineTree_split_step (fuel := 79) (t := 383889) (p := 191940)
    (axis := ⟨2, by decide⟩) (tm := 384247) (pm := 192119)
    (t' := 384422) (p' := 192207)
    (by decide +kernel) improvedNode8911 improvedNode8913

theorem improvedNode8915 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 81 383888 191940 (improvedPathBox improvedRootBox [(false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384497, 192245) :=
  replayAffineTree_split_step (fuel := 80) (t := 383888) (p := 191940)
    (axis := ⟨4, by decide⟩) (tm := 384422) (pm := 192207)
    (t' := 384497) (p' := 192245)
    (by decide +kernel) improvedNode8914 improvedChunk8917

theorem improvedNode8916 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 82 383887 191940 (improvedPathBox improvedRootBox [(false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384576, 192285) :=
  replayAffineTree_split_step (fuel := 81) (t := 383887) (p := 191940)
    (axis := ⟨0, by decide⟩) (tm := 384497) (pm := 192245)
    (t' := 384576) (p' := 192285)
    (by decide +kernel) improvedNode8915 improvedChunk8918

theorem improvedNode8917 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 83 383886 191940 (improvedPathBox improvedRootBox [(false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384661, 192328) :=
  replayAffineTree_split_step (fuel := 82) (t := 383886) (p := 191940)
    (axis := ⟨3, by decide⟩) (tm := 384576) (pm := 192285)
    (t' := 384661) (p' := 192328)
    (by decide +kernel) improvedNode8916 improvedChunk8919

theorem improvedNode8918 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 84 383885 191940 (improvedPathBox improvedRootBox [(false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384742, 192369) :=
  replayAffineTree_split_step (fuel := 83) (t := 383885) (p := 191940)
    (axis := ⟨1, by decide⟩) (tm := 384661) (pm := 192328)
    (t' := 384742) (p' := 192369)
    (by decide +kernel) improvedNode8917 improvedChunk8920

theorem improvedNode8919 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 80 384746 192369 (improvedPathBox improvedRootBox [(false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384855, 192424) :=
  replayAffineTree_split_step (fuel := 79) (t := 384746) (p := 192369)
    (axis := ⟨2, by decide⟩) (tm := 384832) (pm := 192412)
    (t' := 384855) (p' := 192424)
    (by decide +kernel) improvedChunk8921 improvedChunk8922

theorem improvedNode8920 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 81 384745 192369 (improvedPathBox improvedRootBox [(false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384856, 192425) :=
  replayAffineTree_split_step (fuel := 80) (t := 384745) (p := 192369)
    (axis := ⟨4, by decide⟩) (tm := 384855) (pm := 192424)
    (t' := 384856) (p' := 192425)
    (by decide +kernel) improvedNode8919 improvedChunk8923

theorem improvedNode8921 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 82 384744 192369 (improvedPathBox improvedRootBox [(false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384857, 192426) :=
  replayAffineTree_split_step (fuel := 81) (t := 384744) (p := 192369)
    (axis := ⟨0, by decide⟩) (tm := 384856) (pm := 192425)
    (t' := 384857) (p' := 192426)
    (by decide +kernel) improvedNode8920 improvedChunk8924

theorem improvedNode8922 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 83 384743 192369 (improvedPathBox improvedRootBox [(false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384858, 192427) :=
  replayAffineTree_split_step (fuel := 82) (t := 384743) (p := 192369)
    (axis := ⟨3, by decide⟩) (tm := 384857) (pm := 192426)
    (t' := 384858) (p' := 192427)
    (by decide +kernel) improvedNode8921 improvedChunk8925

theorem improvedNode8923 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 84 384742 192369 (improvedPathBox improvedRootBox [(true, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384859, 192428) :=
  replayAffineTree_split_step (fuel := 83) (t := 384742) (p := 192369)
    (axis := ⟨1, by decide⟩) (tm := 384858) (pm := 192427)
    (t' := 384859) (p' := 192428)
    (by decide +kernel) improvedNode8922 improvedChunk8926

theorem improvedNode8924 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 85 383884 191940 (improvedPathBox improvedRootBox [(false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384859, 192428) :=
  replayAffineTree_split_step (fuel := 84) (t := 383884) (p := 191940)
    (axis := ⟨2, by decide⟩) (tm := 384742) (pm := 192369)
    (t' := 384859) (p' := 192428)
    (by decide +kernel) improvedNode8918 improvedNode8923

theorem improvedNode8925 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 86 383883 191940 (improvedPathBox improvedRootBox [(false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384860, 192429) :=
  replayAffineTree_split_step (fuel := 85) (t := 383883) (p := 191940)
    (axis := ⟨4, by decide⟩) (tm := 384859) (pm := 192428)
    (t' := 384860) (p' := 192429)
    (by decide +kernel) improvedNode8924 improvedChunk8927

theorem improvedNode8926 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 87 383882 191940 (improvedPathBox improvedRootBox [(false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384861, 192430) :=
  replayAffineTree_split_step (fuel := 86) (t := 383882) (p := 191940)
    (axis := ⟨0, by decide⟩) (tm := 384860) (pm := 192429)
    (t' := 384861) (p' := 192430)
    (by decide +kernel) improvedNode8925 improvedChunk8928

theorem improvedNode8927 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 88 383881 191940 (improvedPathBox improvedRootBox [(true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩)]) =
      some (384862, 192431) :=
  replayAffineTree_split_step (fuel := 87) (t := 383881) (p := 191940)
    (axis := ⟨3, by decide⟩) (tm := 384861) (pm := 192430)
    (t' := 384862) (p' := 192431)
    (by decide +kernel) improvedNode8926 improvedChunk8929

theorem improvedNode8928 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 89 1 0 (improvedPathBox improvedRootBox [(false, ⟨2, by decide⟩)]) =
      some (384862, 192431) :=
  replayAffineTree_split_step (fuel := 88) (t := 1) (p := 0)
    (axis := ⟨1, by decide⟩) (tm := 383881) (pm := 191940)
    (t' := 384862) (p' := 192431)
    (by decide +kernel) improvedNode8906 improvedNode8927

theorem improvedNode8929 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 76 384875 192431 (improvedPathBox improvedRootBox [(false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385004, 192496) :=
  replayAffineTree_split_step (fuel := 75) (t := 384875) (p := 192431)
    (axis := ⟨4, by decide⟩) (tm := 384963) (pm := 192475)
    (t' := 385004) (p' := 192496)
    (by decide +kernel) improvedChunk8930 improvedChunk8931

theorem improvedNode8930 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 77 384874 192431 (improvedPathBox improvedRootBox [(false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385065, 192527) :=
  replayAffineTree_split_step (fuel := 76) (t := 384874) (p := 192431)
    (axis := ⟨0, by decide⟩) (tm := 385004) (pm := 192496)
    (t' := 385065) (p' := 192527)
    (by decide +kernel) improvedNode8929 improvedChunk8932

theorem improvedNode8931 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 78 384873 192431 (improvedPathBox improvedRootBox [(false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385158, 192574) :=
  replayAffineTree_split_step (fuel := 77) (t := 384873) (p := 192431)
    (axis := ⟨3, by decide⟩) (tm := 385065) (pm := 192527)
    (t' := 385158) (p' := 192574)
    (by decide +kernel) improvedNode8930 improvedChunk8933

theorem improvedNode8932 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 77 385159 192574 (improvedPathBox improvedRootBox [(false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385260, 192625) :=
  replayAffineTree_split_step (fuel := 76) (t := 385159) (p := 192574)
    (axis := ⟨0, by decide⟩) (tm := 385233) (pm := 192611)
    (t' := 385260) (p' := 192625)
    (by decide +kernel) improvedChunk8934 improvedChunk8935

theorem improvedNode8933 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 78 385158 192574 (improvedPathBox improvedRootBox [(true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385299, 192645) :=
  replayAffineTree_split_step (fuel := 77) (t := 385158) (p := 192574)
    (axis := ⟨3, by decide⟩) (tm := 385260) (pm := 192625)
    (t' := 385299) (p' := 192645)
    (by decide +kernel) improvedNode8932 improvedChunk8936

theorem improvedNode8934 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 79 384872 192431 (improvedPathBox improvedRootBox [(false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385299, 192645) :=
  replayAffineTree_split_step (fuel := 78) (t := 384872) (p := 192431)
    (axis := ⟨1, by decide⟩) (tm := 385158) (pm := 192574)
    (t' := 385299) (p' := 192645)
    (by decide +kernel) improvedNode8931 improvedNode8933

theorem improvedNode8935 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 78 385300 192645 (improvedPathBox improvedRootBox [(false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385425, 192708) :=
  replayAffineTree_split_step (fuel := 77) (t := 385300) (p := 192645)
    (axis := ⟨3, by decide⟩) (tm := 385386) (pm := 192688)
    (t' := 385425) (p' := 192708)
    (by decide +kernel) improvedChunk8937 improvedChunk8938

theorem improvedNode8936 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 79 385299 192645 (improvedPathBox improvedRootBox [(true, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385478, 192735) :=
  replayAffineTree_split_step (fuel := 78) (t := 385299) (p := 192645)
    (axis := ⟨1, by decide⟩) (tm := 385425) (pm := 192708)
    (t' := 385478) (p' := 192735)
    (by decide +kernel) improvedNode8935 improvedChunk8939

theorem improvedNode8937 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 80 384871 192431 (improvedPathBox improvedRootBox [(false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385478, 192735) :=
  replayAffineTree_split_step (fuel := 79) (t := 384871) (p := 192431)
    (axis := ⟨2, by decide⟩) (tm := 385299) (pm := 192645)
    (t' := 385478) (p' := 192735)
    (by decide +kernel) improvedNode8934 improvedNode8936

theorem improvedNode8938 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 81 384870 192431 (improvedPathBox improvedRootBox [(false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385565, 192779) :=
  replayAffineTree_split_step (fuel := 80) (t := 384870) (p := 192431)
    (axis := ⟨4, by decide⟩) (tm := 385478) (pm := 192735)
    (t' := 385565) (p' := 192779)
    (by decide +kernel) improvedNode8937 improvedChunk8940

theorem improvedNode8939 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 82 384869 192431 (improvedPathBox improvedRootBox [(false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385656, 192825) :=
  replayAffineTree_split_step (fuel := 81) (t := 384869) (p := 192431)
    (axis := ⟨0, by decide⟩) (tm := 385565) (pm := 192779)
    (t' := 385656) (p' := 192825)
    (by decide +kernel) improvedNode8938 improvedChunk8941

theorem improvedNode8940 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 83 384868 192431 (improvedPathBox improvedRootBox [(false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385753, 192874) :=
  replayAffineTree_split_step (fuel := 82) (t := 384868) (p := 192431)
    (axis := ⟨3, by decide⟩) (tm := 385656) (pm := 192825)
    (t' := 385753) (p' := 192874)
    (by decide +kernel) improvedNode8939 improvedChunk8942

theorem improvedNode8941 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 80 385756 192874 (improvedPathBox improvedRootBox [(false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385865, 192929) :=
  replayAffineTree_split_step (fuel := 79) (t := 385756) (p := 192874)
    (axis := ⟨2, by decide⟩) (tm := 385846) (pm := 192919)
    (t' := 385865) (p' := 192929)
    (by decide +kernel) improvedChunk8943 improvedChunk8944

theorem improvedNode8942 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 81 385755 192874 (improvedPathBox improvedRootBox [(false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385866, 192930) :=
  replayAffineTree_split_step (fuel := 80) (t := 385755) (p := 192874)
    (axis := ⟨4, by decide⟩) (tm := 385865) (pm := 192929)
    (t' := 385866) (p' := 192930)
    (by decide +kernel) improvedNode8941 improvedChunk8945

theorem improvedNode8943 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 82 385754 192874 (improvedPathBox improvedRootBox [(false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385867, 192931) :=
  replayAffineTree_split_step (fuel := 81) (t := 385754) (p := 192874)
    (axis := ⟨0, by decide⟩) (tm := 385866) (pm := 192930)
    (t' := 385867) (p' := 192931)
    (by decide +kernel) improvedNode8942 improvedChunk8946

theorem improvedNode8944 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 83 385753 192874 (improvedPathBox improvedRootBox [(true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385868, 192932) :=
  replayAffineTree_split_step (fuel := 82) (t := 385753) (p := 192874)
    (axis := ⟨3, by decide⟩) (tm := 385867) (pm := 192931)
    (t' := 385868) (p' := 192932)
    (by decide +kernel) improvedNode8943 improvedChunk8947

theorem improvedNode8945 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 84 384867 192431 (improvedPathBox improvedRootBox [(false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385868, 192932) :=
  replayAffineTree_split_step (fuel := 83) (t := 384867) (p := 192431)
    (axis := ⟨1, by decide⟩) (tm := 385753) (pm := 192874)
    (t' := 385868) (p' := 192932)
    (by decide +kernel) improvedNode8940 improvedNode8944

theorem improvedNode8946 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 85 384866 192431 (improvedPathBox improvedRootBox [(false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385963, 192980) :=
  replayAffineTree_split_step (fuel := 84) (t := 384866) (p := 192431)
    (axis := ⟨2, by decide⟩) (tm := 385868) (pm := 192932)
    (t' := 385963) (p' := 192980)
    (by decide +kernel) improvedNode8945 improvedChunk8948

theorem improvedNode8947 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 86 384865 192431 (improvedPathBox improvedRootBox [(false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385964, 192981) :=
  replayAffineTree_split_step (fuel := 85) (t := 384865) (p := 192431)
    (axis := ⟨4, by decide⟩) (tm := 385963) (pm := 192980)
    (t' := 385964) (p' := 192981)
    (by decide +kernel) improvedNode8946 improvedChunk8949

theorem improvedNode8948 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 87 384864 192431 (improvedPathBox improvedRootBox [(false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385965, 192982) :=
  replayAffineTree_split_step (fuel := 86) (t := 384864) (p := 192431)
    (axis := ⟨0, by decide⟩) (tm := 385964) (pm := 192981)
    (t' := 385965) (p' := 192982)
    (by decide +kernel) improvedNode8947 improvedChunk8950

theorem improvedNode8949 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 88 384863 192431 (improvedPathBox improvedRootBox [(false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (385966, 192983) :=
  replayAffineTree_split_step (fuel := 87) (t := 384863) (p := 192431)
    (axis := ⟨3, by decide⟩) (tm := 385965) (pm := 192982)
    (t' := 385966) (p' := 192983)
    (by decide +kernel) improvedNode8948 improvedChunk8951

theorem improvedNode8950 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 89 384862 192431 (improvedPathBox improvedRootBox [(true, ⟨2, by decide⟩)]) =
      some (385967, 192984) :=
  replayAffineTree_split_step (fuel := 88) (t := 384862) (p := 192431)
    (axis := ⟨1, by decide⟩) (tm := 385966) (pm := 192983)
    (t' := 385967) (p' := 192984)
    (by decide +kernel) improvedNode8949 improvedChunk8952

theorem improvedNode8951 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 90 0 0 (improvedPathBox improvedRootBox []) =
      some (385967, 192984) :=
  replayAffineTree_split_step (fuel := 89) (t := 0) (p := 0)
    (axis := ⟨2, by decide⟩) (tm := 384862) (pm := 192431)
    (t' := 385967) (p' := 192984)
    (by decide +kernel) improvedNode8928 improvedNode8950

end Zeta23.ThmD.Sextuple.MacroPrototype
