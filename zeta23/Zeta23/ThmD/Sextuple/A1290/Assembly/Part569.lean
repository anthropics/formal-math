import Zeta23.ThmD.Sextuple.A1290.TreeWords
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56902
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56903
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56904
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56905
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56906
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56907
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56908
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56909
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56910
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56911
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56912
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56913
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56914
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56915
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56916
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56917
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56918
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56919
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56920
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56921
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56922
import Zeta23.ThmD.Sextuple.A1290.Chunks.Chunk56923
import Zeta23.ThmD.Sextuple.A1290.Assembly.Part568
import Zeta23.ThmD.Sextuple.Macro.AssemblyStep

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype.A1290
open Zeta23.ThmD.Sextuple

theorem improvedNode56900 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 60 3549795 1774891 (improvedPathBox improvedRootBox [(false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3549946, 1774967) :=
  replayAffineTree_split_step (fuel := 59) (t := 3549795) (p := 1774891)
    (axis := ⟨4, by decide⟩) (tm := 3549905) (pm := 1774946)
    (t' := 3549946) (p' := 1774967)
    (by decide +kernel) improvedNode56899 improvedChunk56902

theorem improvedNode56901 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 61 3549794 1774891 (improvedPathBox improvedRootBox [(false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550009, 1774999) :=
  replayAffineTree_split_step (fuel := 60) (t := 3549794) (p := 1774891)
    (axis := ⟨0, by decide⟩) (tm := 3549946) (pm := 1774967)
    (t' := 3550009) (p' := 1774999)
    (by decide +kernel) improvedNode56900 improvedChunk56903

theorem improvedNode56902 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 62 3549793 1774891 (improvedPathBox improvedRootBox [(false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550106, 1775048) :=
  replayAffineTree_split_step (fuel := 61) (t := 3549793) (p := 1774891)
    (axis := ⟨3, by decide⟩) (tm := 3550009) (pm := 1774999)
    (t' := 3550106) (p' := 1775048)
    (by decide +kernel) improvedNode56901 improvedChunk56904

theorem improvedNode56903 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 61 3550107 1775048 (improvedPathBox improvedRootBox [(false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550214, 1775102) :=
  replayAffineTree_split_step (fuel := 60) (t := 3550107) (p := 1775048)
    (axis := ⟨0, by decide⟩) (tm := 3550187) (pm := 1775088)
    (t' := 3550214) (p' := 1775102)
    (by decide +kernel) improvedChunk56905 improvedChunk56906

theorem improvedNode56904 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 62 3550106 1775048 (improvedPathBox improvedRootBox [(true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550253, 1775122) :=
  replayAffineTree_split_step (fuel := 61) (t := 3550106) (p := 1775048)
    (axis := ⟨3, by decide⟩) (tm := 3550214) (pm := 1775102)
    (t' := 3550253) (p' := 1775122)
    (by decide +kernel) improvedNode56903 improvedChunk56907

theorem improvedNode56905 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 63 3549792 1774891 (improvedPathBox improvedRootBox [(false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550253, 1775122) :=
  replayAffineTree_split_step (fuel := 62) (t := 3549792) (p := 1774891)
    (axis := ⟨1, by decide⟩) (tm := 3550106) (pm := 1775048)
    (t' := 3550253) (p' := 1775122)
    (by decide +kernel) improvedNode56902 improvedNode56904

theorem improvedNode56906 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 62 3550254 1775122 (improvedPathBox improvedRootBox [(false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550379, 1775185) :=
  replayAffineTree_split_step (fuel := 61) (t := 3550254) (p := 1775122)
    (axis := ⟨3, by decide⟩) (tm := 3550340) (pm := 1775165)
    (t' := 3550379) (p' := 1775185)
    (by decide +kernel) improvedChunk56908 improvedChunk56909

theorem improvedNode56907 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 63 3550253 1775122 (improvedPathBox improvedRootBox [(true, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550432, 1775212) :=
  replayAffineTree_split_step (fuel := 62) (t := 3550253) (p := 1775122)
    (axis := ⟨1, by decide⟩) (tm := 3550379) (pm := 1775185)
    (t' := 3550432) (p' := 1775212)
    (by decide +kernel) improvedNode56906 improvedChunk56910

theorem improvedNode56908 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 64 3549791 1774891 (improvedPathBox improvedRootBox [(false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550432, 1775212) :=
  replayAffineTree_split_step (fuel := 63) (t := 3549791) (p := 1774891)
    (axis := ⟨2, by decide⟩) (tm := 3550253) (pm := 1775122)
    (t' := 3550432) (p' := 1775212)
    (by decide +kernel) improvedNode56905 improvedNode56907

theorem improvedNode56909 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 65 3549790 1774891 (improvedPathBox improvedRootBox [(false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550519, 1775256) :=
  replayAffineTree_split_step (fuel := 64) (t := 3549790) (p := 1774891)
    (axis := ⟨4, by decide⟩) (tm := 3550432) (pm := 1775212)
    (t' := 3550519) (p' := 1775256)
    (by decide +kernel) improvedNode56908 improvedChunk56911

theorem improvedNode56910 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 66 3549789 1774891 (improvedPathBox improvedRootBox [(false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550610, 1775302) :=
  replayAffineTree_split_step (fuel := 65) (t := 3549789) (p := 1774891)
    (axis := ⟨0, by decide⟩) (tm := 3550519) (pm := 1775256)
    (t' := 3550610) (p' := 1775302)
    (by decide +kernel) improvedNode56909 improvedChunk56912

theorem improvedNode56911 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 67 3549788 1774891 (improvedPathBox improvedRootBox [(false, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550709, 1775352) :=
  replayAffineTree_split_step (fuel := 66) (t := 3549788) (p := 1774891)
    (axis := ⟨3, by decide⟩) (tm := 3550610) (pm := 1775302)
    (t' := 3550709) (p' := 1775352)
    (by decide +kernel) improvedNode56910 improvedChunk56913

theorem improvedNode56912 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 64 3550712 1775352 (improvedPathBox improvedRootBox [(false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550823, 1775408) :=
  replayAffineTree_split_step (fuel := 63) (t := 3550712) (p := 1775352)
    (axis := ⟨2, by decide⟩) (tm := 3550804) (pm := 1775398)
    (t' := 3550823) (p' := 1775408)
    (by decide +kernel) improvedChunk56914 improvedChunk56915

theorem improvedNode56913 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 65 3550711 1775352 (improvedPathBox improvedRootBox [(false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550824, 1775409) :=
  replayAffineTree_split_step (fuel := 64) (t := 3550711) (p := 1775352)
    (axis := ⟨4, by decide⟩) (tm := 3550823) (pm := 1775408)
    (t' := 3550824) (p' := 1775409)
    (by decide +kernel) improvedNode56912 improvedChunk56916

theorem improvedNode56914 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 66 3550710 1775352 (improvedPathBox improvedRootBox [(false, ⟨3, by decide⟩), (true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550825, 1775410) :=
  replayAffineTree_split_step (fuel := 65) (t := 3550710) (p := 1775352)
    (axis := ⟨0, by decide⟩) (tm := 3550824) (pm := 1775409)
    (t' := 3550825) (p' := 1775410)
    (by decide +kernel) improvedNode56913 improvedChunk56917

theorem improvedNode56915 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 67 3550709 1775352 (improvedPathBox improvedRootBox [(true, ⟨1, by decide⟩), (false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550826, 1775411) :=
  replayAffineTree_split_step (fuel := 66) (t := 3550709) (p := 1775352)
    (axis := ⟨3, by decide⟩) (tm := 3550825) (pm := 1775410)
    (t' := 3550826) (p' := 1775411)
    (by decide +kernel) improvedNode56914 improvedChunk56918

theorem improvedNode56916 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 68 3549787 1774891 (improvedPathBox improvedRootBox [(false, ⟨2, by decide⟩), (false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550826, 1775411) :=
  replayAffineTree_split_step (fuel := 67) (t := 3549787) (p := 1774891)
    (axis := ⟨1, by decide⟩) (tm := 3550709) (pm := 1775352)
    (t' := 3550826) (p' := 1775411)
    (by decide +kernel) improvedNode56911 improvedNode56915

theorem improvedNode56917 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 69 3549786 1774891 (improvedPathBox improvedRootBox [(false, ⟨4, by decide⟩), (false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550921, 1775459) :=
  replayAffineTree_split_step (fuel := 68) (t := 3549786) (p := 1774891)
    (axis := ⟨2, by decide⟩) (tm := 3550826) (pm := 1775411)
    (t' := 3550921) (p' := 1775459)
    (by decide +kernel) improvedNode56916 improvedChunk56919

theorem improvedNode56918 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 70 3549785 1774891 (improvedPathBox improvedRootBox [(false, ⟨0, by decide⟩), (false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550922, 1775460) :=
  replayAffineTree_split_step (fuel := 69) (t := 3549785) (p := 1774891)
    (axis := ⟨4, by decide⟩) (tm := 3550921) (pm := 1775459)
    (t' := 3550922) (p' := 1775460)
    (by decide +kernel) improvedNode56917 improvedChunk56920

theorem improvedNode56919 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 71 3549784 1774891 (improvedPathBox improvedRootBox [(false, ⟨3, by decide⟩), (false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550923, 1775461) :=
  replayAffineTree_split_step (fuel := 70) (t := 3549784) (p := 1774891)
    (axis := ⟨0, by decide⟩) (tm := 3550922) (pm := 1775460)
    (t' := 3550923) (p' := 1775461)
    (by decide +kernel) improvedNode56918 improvedChunk56921

theorem improvedNode56920 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 72 3549783 1774891 (improvedPathBox improvedRootBox [(false, ⟨1, by decide⟩), (true, ⟨2, by decide⟩)]) =
      some (3550924, 1775462) :=
  replayAffineTree_split_step (fuel := 71) (t := 3549783) (p := 1774891)
    (axis := ⟨3, by decide⟩) (tm := 3550923) (pm := 1775461)
    (t' := 3550924) (p' := 1775462)
    (by decide +kernel) improvedNode56919 improvedChunk56922

theorem improvedNode56921 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 73 3549782 1774891 (improvedPathBox improvedRootBox [(true, ⟨2, by decide⟩)]) =
      some (3550925, 1775463) :=
  replayAffineTree_split_step (fuel := 72) (t := 3549782) (p := 1774891)
    (axis := ⟨1, by decide⟩) (tm := 3550924) (pm := 1775462)
    (t' := 3550925) (p' := 1775463)
    (by decide +kernel) improvedNode56920 improvedChunk56923

theorem improvedNode56922 :
    replayAffineTree improvedConcreteLeafCheck improvedTopologyStream improvedPayloadStream 74 0 0 (improvedPathBox improvedRootBox []) =
      some (3550925, 1775463) :=
  replayAffineTree_split_step (fuel := 73) (t := 0) (p := 0)
    (axis := ⟨2, by decide⟩) (tm := 3549782) (pm := 1774891)
    (t' := 3550925) (p' := 1775463)
    (by decide +kernel) improvedNode56898 improvedNode56921

end Zeta23.ThmD.Sextuple.MacroPrototype.A1290
