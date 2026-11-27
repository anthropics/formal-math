import Zeta23.ThmD.Sextuple.Macro.TreeWords
import Zeta23.ThmD.Sextuple.Macro.Assembly.Part028
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2902
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2903
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2904
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2905
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2906
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2907
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2908
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2909
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2910
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2911
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2912
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2913
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2914
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2915
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2916
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2917
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2918
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2919
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2920
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2921
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2922
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2923
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2924
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2925
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2926
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2927
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2928
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2929
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2930
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2931
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2932
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2933
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2934
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2935
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2936
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2937
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2938
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2939
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2940
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2941
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2942
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2943
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2944
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2945
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2946
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2947
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2948
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2949
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2950
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2951
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2952
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2953
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2954
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2955
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2956
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2957
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2958
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2959
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2960
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2961
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2962
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2963
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2964
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2965
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2966
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2967
import Zeta23.ThmD.Sextuple.Macro.Chunks.Chunk2968
import Zeta23.ThmD.Sextuple.Macro.AssemblyStep

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Zeta23.ThmD.Sextuple.MacroPrototype
open Zeta23.ThmD.Sextuple

theorem node2900 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 55 95443 47719 (pathBox rootBox [(false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96024, 48010) :=
  replayAffineTree_split_step (fuel := 54) (t := 95443) (p := 47719)
    (box := pathBox rootBox [(false, 2), (true, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) (axis := 1)
    (tm := 95953) (pm := 47974) (t' := 96024) (p' := 48010)
    (by decide +kernel) node2899 chunk2902

theorem node2901 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 56 95442 47719 (pathBox rootBox [(true, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96107, 48052) :=
  replayAffineTree_split_step (fuel := 55) (t := 95442) (p := 47719)
    (box := pathBox rootBox [(true, 4), (false, 0), (false, 3), (false, 1), (false, 2)]) (axis := 2)
    (tm := 96024) (pm := 48010) (t' := 96107) (p' := 48052)
    (by decide +kernel) node2900 chunk2903

theorem node2902 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 57 4 0 (pathBox rootBox [(false, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96107, 48052) :=
  replayAffineTree_split_step (fuel := 56) (t := 4) (p := 0)
    (box := pathBox rootBox [(false, 0), (false, 3), (false, 1), (false, 2)]) (axis := 4)
    (tm := 95442) (pm := 47719) (t' := 96107) (p' := 48052)
    (by decide +kernel) node2892 node2901

theorem node2903 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 96116 48052 (pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96217, 48103) :=
  replayAffineTree_split_step (fuel := 47) (t := 96116) (p := 48052)
    (box := pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) (axis := 0)
    (tm := 96184) (pm := 48086) (t' := 96217) (p' := 48103)
    (by decide +kernel) chunk2904 chunk2905

theorem node2904 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 96115 48052 (pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96270, 48130) :=
  replayAffineTree_split_step (fuel := 48) (t := 96115) (p := 48052)
    (box := pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) (axis := 3)
    (tm := 96217) (pm := 48103) (t' := 96270) (p' := 48130)
    (by decide +kernel) node2903 chunk2906

theorem node2905 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 50 96114 48052 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96353, 48172) :=
  replayAffineTree_split_step (fuel := 49) (t := 96114) (p := 48052)
    (box := pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) (axis := 1)
    (tm := 96270) (pm := 48130) (t' := 96353) (p' := 48172)
    (by decide +kernel) node2904 chunk2907

theorem node2906 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 50 96353 48172 (pathBox rootBox [(true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96476, 48234) :=
  replayAffineTree_split_step (fuel := 49) (t := 96353) (p := 48172)
    (box := pathBox rootBox [(true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) (axis := 1)
    (tm := 96441) (pm := 48216) (t' := 96476) (p' := 48234)
    (by decide +kernel) chunk2908 chunk2909

theorem node2907 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 51 96113 48052 (pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96476, 48234) :=
  replayAffineTree_split_step (fuel := 50) (t := 96113) (p := 48052)
    (box := pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) (axis := 2)
    (tm := 96353) (pm := 48172) (t' := 96476) (p' := 48234)
    (by decide +kernel) node2905 node2906

theorem node2908 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 52 96112 48052 (pathBox rootBox [(false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96537, 48265) :=
  replayAffineTree_split_step (fuel := 51) (t := 96112) (p := 48052)
    (box := pathBox rootBox [(false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) (axis := 4)
    (tm := 96476) (pm := 48234) (t' := 96537) (p' := 48265)
    (by decide +kernel) node2907 chunk2910

theorem node2909 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 53 96111 48052 (pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96600, 48297) :=
  replayAffineTree_split_step (fuel := 52) (t := 96111) (p := 48052)
    (box := pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) (axis := 0)
    (tm := 96537) (pm := 48265) (t' := 96600) (p' := 48297)
    (by decide +kernel) node2908 chunk2911

theorem node2910 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 54 96110 48052 (pathBox rootBox [(false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96669, 48332) :=
  replayAffineTree_split_step (fuel := 53) (t := 96110) (p := 48052)
    (box := pathBox rootBox [(false, 1), (false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) (axis := 3)
    (tm := 96600) (pm := 48297) (t' := 96669) (p' := 48332)
    (by decide +kernel) node2909 chunk2912

theorem node2911 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 55 96109 48052 (pathBox rootBox [(false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96744, 48370) :=
  replayAffineTree_split_step (fuel := 54) (t := 96109) (p := 48052)
    (box := pathBox rootBox [(false, 2), (false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) (axis := 1)
    (tm := 96669) (pm := 48332) (t' := 96744) (p' := 48370)
    (by decide +kernel) node2910 chunk2913

theorem node2912 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 56 96108 48052 (pathBox rootBox [(false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96831, 48414) :=
  replayAffineTree_split_step (fuel := 55) (t := 96108) (p := 48052)
    (box := pathBox rootBox [(false, 4), (true, 0), (false, 3), (false, 1), (false, 2)]) (axis := 2)
    (tm := 96744) (pm := 48370) (t' := 96831) (p' := 48414)
    (by decide +kernel) node2911 chunk2914

theorem node2913 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 57 96107 48052 (pathBox rootBox [(true, 0), (false, 3), (false, 1), (false, 2)]) =
      some (96832, 48415) :=
  replayAffineTree_split_step (fuel := 56) (t := 96107) (p := 48052)
    (box := pathBox rootBox [(true, 0), (false, 3), (false, 1), (false, 2)]) (axis := 4)
    (tm := 96831) (pm := 48414) (t' := 96832) (p' := 48415)
    (by decide +kernel) node2912 chunk2915

theorem node2914 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 58 3 0 (pathBox rootBox [(false, 3), (false, 1), (false, 2)]) =
      some (96832, 48415) :=
  replayAffineTree_split_step (fuel := 57) (t := 3) (p := 0)
    (box := pathBox rootBox [(false, 3), (false, 1), (false, 2)]) (axis := 0)
    (tm := 96107) (pm := 48052) (t' := 96832) (p' := 48415)
    (by decide +kernel) node2902 node2913

theorem node2915 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 96842 48415 (pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (96963, 48476) :=
  replayAffineTree_split_step (fuel := 47) (t := 96842) (p := 48415)
    (box := pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) (axis := 0)
    (tm := 96926) (pm := 48457) (t' := 96963) (p' := 48476)
    (by decide +kernel) chunk2916 chunk2917

theorem node2916 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 96841 48415 (pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97022, 48506) :=
  replayAffineTree_split_step (fuel := 48) (t := 96841) (p := 48415)
    (box := pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) (axis := 3)
    (tm := 96963) (pm := 48476) (t' := 97022) (p' := 48506)
    (by decide +kernel) node2915 chunk2918

theorem node2917 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 50 96840 48415 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97115, 48553) :=
  replayAffineTree_split_step (fuel := 49) (t := 96840) (p := 48415)
    (box := pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) (axis := 1)
    (tm := 97022) (pm := 48506) (t' := 97115) (p' := 48553)
    (by decide +kernel) node2916 chunk2919

theorem node2918 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 50 97115 48553 (pathBox rootBox [(true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97248, 48620) :=
  replayAffineTree_split_step (fuel := 49) (t := 97115) (p := 48553)
    (box := pathBox rootBox [(true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) (axis := 1)
    (tm := 97213) (pm := 48602) (t' := 97248) (p' := 48620)
    (by decide +kernel) chunk2920 chunk2921

theorem node2919 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 51 96839 48415 (pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97248, 48620) :=
  replayAffineTree_split_step (fuel := 50) (t := 96839) (p := 48415)
    (box := pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) (axis := 2)
    (tm := 97115) (pm := 48553) (t' := 97248) (p' := 48620)
    (by decide +kernel) node2917 node2918

theorem node2920 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 52 96838 48415 (pathBox rootBox [(false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97309, 48651) :=
  replayAffineTree_split_step (fuel := 51) (t := 96838) (p := 48415)
    (box := pathBox rootBox [(false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) (axis := 4)
    (tm := 97248) (pm := 48620) (t' := 97309) (p' := 48651)
    (by decide +kernel) node2919 chunk2922

theorem node2921 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 53 96837 48415 (pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97374, 48684) :=
  replayAffineTree_split_step (fuel := 52) (t := 96837) (p := 48415)
    (box := pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) (axis := 0)
    (tm := 97309) (pm := 48651) (t' := 97374) (p' := 48684)
    (by decide +kernel) node2920 chunk2923

theorem node2922 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 54 96836 48415 (pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97441, 48718) :=
  replayAffineTree_split_step (fuel := 53) (t := 96836) (p := 48415)
    (box := pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) (axis := 3)
    (tm := 97374) (pm := 48684) (t' := 97441) (p' := 48718)
    (by decide +kernel) node2921 chunk2924

theorem node2923 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 55 96835 48415 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97518, 48757) :=
  replayAffineTree_split_step (fuel := 54) (t := 96835) (p := 48415)
    (box := pathBox rootBox [(false, 2), (false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) (axis := 1)
    (tm := 97441) (pm := 48718) (t' := 97518) (p' := 48757)
    (by decide +kernel) node2922 chunk2925

theorem node2924 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 56 96834 48415 (pathBox rootBox [(false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97607, 48802) :=
  replayAffineTree_split_step (fuel := 55) (t := 96834) (p := 48415)
    (box := pathBox rootBox [(false, 4), (false, 0), (true, 3), (false, 1), (false, 2)]) (axis := 2)
    (tm := 97518) (pm := 48757) (t' := 97607) (p' := 48802)
    (by decide +kernel) node2923 chunk2926

theorem node2925 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 57 96833 48415 (pathBox rootBox [(false, 0), (true, 3), (false, 1), (false, 2)]) =
      some (97608, 48803) :=
  replayAffineTree_split_step (fuel := 56) (t := 96833) (p := 48415)
    (box := pathBox rootBox [(false, 0), (true, 3), (false, 1), (false, 2)]) (axis := 4)
    (tm := 97607) (pm := 48802) (t' := 97608) (p' := 48803)
    (by decide +kernel) node2924 chunk2927

theorem node2926 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 58 96832 48415 (pathBox rootBox [(true, 3), (false, 1), (false, 2)]) =
      some (97609, 48804) :=
  replayAffineTree_split_step (fuel := 57) (t := 96832) (p := 48415)
    (box := pathBox rootBox [(true, 3), (false, 1), (false, 2)]) (axis := 0)
    (tm := 97608) (pm := 48803) (t' := 97609) (p' := 48804)
    (by decide +kernel) node2925 chunk2928

theorem node2927 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 59 2 0 (pathBox rootBox [(false, 1), (false, 2)]) =
      some (97609, 48804) :=
  replayAffineTree_split_step (fuel := 58) (t := 2) (p := 0)
    (box := pathBox rootBox [(false, 1), (false, 2)]) (axis := 3)
    (tm := 96832) (pm := 48415) (t' := 97609) (p' := 48804)
    (by decide +kernel) node2914 node2926

theorem node2928 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 97620 48804 (pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (97759, 48874) :=
  replayAffineTree_split_step (fuel := 47) (t := 97620) (p := 48804)
    (box := pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 0)
    (tm := 97716) (pm := 48852) (t' := 97759) (p' := 48874)
    (by decide +kernel) chunk2929 chunk2930

theorem node2929 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 97619 48804 (pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (97830, 48910) :=
  replayAffineTree_split_step (fuel := 48) (t := 97619) (p := 48804)
    (box := pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 3)
    (tm := 97759) (pm := 48874) (t' := 97830) (p' := 48910)
    (by decide +kernel) node2928 chunk2931

theorem node2930 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 97830 48910 (pathBox rootBox [(true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (97933, 48962) :=
  replayAffineTree_split_step (fuel := 48) (t := 97830) (p := 48910)
    (box := pathBox rootBox [(true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 3)
    (tm := 97900) (pm := 48945) (t' := 97933) (p' := 48962)
    (by decide +kernel) chunk2932 chunk2933

theorem node2931 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 50 97618 48804 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (97933, 48962) :=
  replayAffineTree_split_step (fuel := 49) (t := 97618) (p := 48804)
    (box := pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 1)
    (tm := 97830) (pm := 48910) (t' := 97933) (p' := 48962)
    (by decide +kernel) node2929 node2930

theorem node2932 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 97934 48962 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98047, 49019) :=
  replayAffineTree_split_step (fuel := 48) (t := 97934) (p := 48962)
    (box := pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 3)
    (tm := 98016) (pm := 49003) (t' := 98047) (p' := 49019)
    (by decide +kernel) chunk2934 chunk2935

theorem node2933 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 50 97933 48962 (pathBox rootBox [(true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98092, 49042) :=
  replayAffineTree_split_step (fuel := 49) (t := 97933) (p := 48962)
    (box := pathBox rootBox [(true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 1)
    (tm := 98047) (pm := 49019) (t' := 98092) (p' := 49042)
    (by decide +kernel) node2932 chunk2936

theorem node2934 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 51 97617 48804 (pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98092, 49042) :=
  replayAffineTree_split_step (fuel := 50) (t := 97617) (p := 48804)
    (box := pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 2)
    (tm := 97933) (pm := 48962) (t' := 98092) (p' := 49042)
    (by decide +kernel) node2931 node2933

theorem node2935 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 52 97616 48804 (pathBox rootBox [(false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98165, 49079) :=
  replayAffineTree_split_step (fuel := 51) (t := 97616) (p := 48804)
    (box := pathBox rootBox [(false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 4)
    (tm := 98092) (pm := 49042) (t' := 98165) (p' := 49079)
    (by decide +kernel) node2934 chunk2937

theorem node2936 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 53 97615 48804 (pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98242, 49118) :=
  replayAffineTree_split_step (fuel := 52) (t := 97615) (p := 48804)
    (box := pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 0)
    (tm := 98165) (pm := 49079) (t' := 98242) (p' := 49118)
    (by decide +kernel) node2935 chunk2938

theorem node2937 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 54 97614 48804 (pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98325, 49160) :=
  replayAffineTree_split_step (fuel := 53) (t := 97614) (p := 48804)
    (box := pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 3)
    (tm := 98242) (pm := 49118) (t' := 98325) (p' := 49160)
    (by decide +kernel) node2936 chunk2939

theorem node2938 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 55 97613 48804 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98406, 49201) :=
  replayAffineTree_split_step (fuel := 54) (t := 97613) (p := 48804)
    (box := pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 1)
    (tm := 98325) (pm := 49160) (t' := 98406) (p' := 49201)
    (by decide +kernel) node2937 chunk2940

theorem node2939 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 51 98410 49201 (pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98511, 49252) :=
  replayAffineTree_split_step (fuel := 50) (t := 98410) (p := 49201)
    (box := pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 2)
    (tm := 98494) (pm := 49243) (t' := 98511) (p' := 49252)
    (by decide +kernel) chunk2941 chunk2942

theorem node2940 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 52 98409 49201 (pathBox rootBox [(false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98512, 49253) :=
  replayAffineTree_split_step (fuel := 51) (t := 98409) (p := 49201)
    (box := pathBox rootBox [(false, 0), (false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 4)
    (tm := 98511) (pm := 49252) (t' := 98512) (p' := 49253)
    (by decide +kernel) node2939 chunk2943

theorem node2941 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 53 98408 49201 (pathBox rootBox [(false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98513, 49254) :=
  replayAffineTree_split_step (fuel := 52) (t := 98408) (p := 49201)
    (box := pathBox rootBox [(false, 3), (false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 0)
    (tm := 98512) (pm := 49253) (t' := 98513) (p' := 49254)
    (by decide +kernel) node2940 chunk2944

theorem node2942 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 54 98407 49201 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98514, 49255) :=
  replayAffineTree_split_step (fuel := 53) (t := 98407) (p := 49201)
    (box := pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 3)
    (tm := 98513) (pm := 49254) (t' := 98514) (p' := 49255)
    (by decide +kernel) node2941 chunk2945

theorem node2943 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 55 98406 49201 (pathBox rootBox [(true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98515, 49256) :=
  replayAffineTree_split_step (fuel := 54) (t := 98406) (p := 49201)
    (box := pathBox rootBox [(true, 2), (false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 1)
    (tm := 98514) (pm := 49255) (t' := 98515) (p' := 49256)
    (by decide +kernel) node2942 chunk2946

theorem node2944 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 56 97612 48804 (pathBox rootBox [(false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98515, 49256) :=
  replayAffineTree_split_step (fuel := 55) (t := 97612) (p := 48804)
    (box := pathBox rootBox [(false, 4), (false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 2)
    (tm := 98406) (pm := 49201) (t' := 98515) (p' := 49256)
    (by decide +kernel) node2938 node2943

theorem node2945 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 57 97611 48804 (pathBox rootBox [(false, 0), (false, 3), (true, 1), (false, 2)]) =
      some (98516, 49257) :=
  replayAffineTree_split_step (fuel := 56) (t := 97611) (p := 48804)
    (box := pathBox rootBox [(false, 0), (false, 3), (true, 1), (false, 2)]) (axis := 4)
    (tm := 98515) (pm := 49256) (t' := 98516) (p' := 49257)
    (by decide +kernel) node2944 chunk2947

theorem node2946 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 58 97610 48804 (pathBox rootBox [(false, 3), (true, 1), (false, 2)]) =
      some (98517, 49258) :=
  replayAffineTree_split_step (fuel := 57) (t := 97610) (p := 48804)
    (box := pathBox rootBox [(false, 3), (true, 1), (false, 2)]) (axis := 0)
    (tm := 98516) (pm := 49257) (t' := 98517) (p' := 49258)
    (by decide +kernel) node2945 chunk2948

theorem node2947 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 59 97609 48804 (pathBox rootBox [(true, 1), (false, 2)]) =
      some (98518, 49259) :=
  replayAffineTree_split_step (fuel := 58) (t := 97609) (p := 48804)
    (box := pathBox rootBox [(true, 1), (false, 2)]) (axis := 3)
    (tm := 98517) (pm := 49258) (t' := 98518) (p' := 49259)
    (by decide +kernel) node2946 chunk2949

theorem node2948 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 60 1 0 (pathBox rootBox [(false, 2)]) =
      some (98518, 49259) :=
  replayAffineTree_split_step (fuel := 59) (t := 1) (p := 0)
    (box := pathBox rootBox [(false, 2)]) (axis := 1)
    (tm := 97609) (pm := 48804) (t' := 98518) (p' := 49259)
    (by decide +kernel) node2927 node2947

theorem node2949 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 47 98531 49259 (pathBox rootBox [(false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (98640, 49314) :=
  replayAffineTree_split_step (fuel := 46) (t := 98531) (p := 49259)
    (box := pathBox rootBox [(false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) (axis := 4)
    (tm := 98609) (pm := 49298) (t' := 98640) (p' := 49314)
    (by decide +kernel) chunk2950 chunk2951

theorem node2950 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 48 98530 49259 (pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (98689, 49339) :=
  replayAffineTree_split_step (fuel := 47) (t := 98530) (p := 49259)
    (box := pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) (axis := 0)
    (tm := 98640) (pm := 49314) (t' := 98689) (p' := 49339)
    (by decide +kernel) node2949 chunk2952

theorem node2951 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 98529 49259 (pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (98768, 49379) :=
  replayAffineTree_split_step (fuel := 48) (t := 98529) (p := 49259)
    (box := pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) (axis := 3)
    (tm := 98689) (pm := 49339) (t' := 98768) (p' := 49379)
    (by decide +kernel) node2950 chunk2953

theorem node2952 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 98768 49379 (pathBox rootBox [(true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (98887, 49439) :=
  replayAffineTree_split_step (fuel := 48) (t := 98768) (p := 49379)
    (box := pathBox rootBox [(true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) (axis := 3)
    (tm := 98854) (pm := 49422) (t' := 98887) (p' := 49439)
    (by decide +kernel) chunk2954 chunk2955

theorem node2953 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 50 98528 49259 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (98887, 49439) :=
  replayAffineTree_split_step (fuel := 49) (t := 98528) (p := 49259)
    (box := pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) (axis := 1)
    (tm := 98768) (pm := 49379) (t' := 98887) (p' := 49439)
    (by decide +kernel) node2951 node2952

theorem node2954 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 49 98888 49439 (pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99009, 49500) :=
  replayAffineTree_split_step (fuel := 48) (t := 98888) (p := 49439)
    (box := pathBox rootBox [(false, 1), (true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) (axis := 3)
    (tm := 98970) (pm := 49480) (t' := 99009) (p' := 49500)
    (by decide +kernel) chunk2956 chunk2957

theorem node2955 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 50 98887 49439 (pathBox rootBox [(true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99062, 49527) :=
  replayAffineTree_split_step (fuel := 49) (t := 98887) (p := 49439)
    (box := pathBox rootBox [(true, 2), (false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) (axis := 1)
    (tm := 99009) (pm := 49500) (t' := 99062) (p' := 49527)
    (by decide +kernel) node2954 chunk2958

theorem node2956 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 51 98527 49259 (pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99062, 49527) :=
  replayAffineTree_split_step (fuel := 50) (t := 98527) (p := 49259)
    (box := pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) (axis := 2)
    (tm := 98887) (pm := 49439) (t' := 99062) (p' := 49527)
    (by decide +kernel) node2953 node2955

theorem node2957 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 52 98526 49259 (pathBox rootBox [(false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99139, 49566) :=
  replayAffineTree_split_step (fuel := 51) (t := 98526) (p := 49259)
    (box := pathBox rootBox [(false, 0), (false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) (axis := 4)
    (tm := 99062) (pm := 49527) (t' := 99139) (p' := 49566)
    (by decide +kernel) node2956 chunk2959

theorem node2958 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 53 98525 49259 (pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99220, 49607) :=
  replayAffineTree_split_step (fuel := 52) (t := 98525) (p := 49259)
    (box := pathBox rootBox [(false, 3), (false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) (axis := 0)
    (tm := 99139) (pm := 49566) (t' := 99220) (p' := 49607)
    (by decide +kernel) node2957 chunk2960

theorem node2959 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 54 98524 49259 (pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99307, 49651) :=
  replayAffineTree_split_step (fuel := 53) (t := 98524) (p := 49259)
    (box := pathBox rootBox [(false, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) (axis := 3)
    (tm := 99220) (pm := 49607) (t' := 99307) (p' := 49651)
    (by decide +kernel) node2958 chunk2961

theorem node2960 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 54 99307 49651 (pathBox rootBox [(true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99408, 49702) :=
  replayAffineTree_split_step (fuel := 53) (t := 99307) (p := 49651)
    (box := pathBox rootBox [(true, 1), (false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) (axis := 3)
    (tm := 99407) (pm := 49701) (t' := 99408) (p' := 49702)
    (by decide +kernel) chunk2962 chunk2963

theorem node2961 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 55 98523 49259 (pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99408, 49702) :=
  replayAffineTree_split_step (fuel := 54) (t := 98523) (p := 49259)
    (box := pathBox rootBox [(false, 2), (false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) (axis := 1)
    (tm := 99307) (pm := 49651) (t' := 99408) (p' := 49702)
    (by decide +kernel) node2959 node2960

theorem node2962 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 56 98522 49259 (pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99503, 49750) :=
  replayAffineTree_split_step (fuel := 55) (t := 98522) (p := 49259)
    (box := pathBox rootBox [(false, 4), (false, 0), (false, 3), (false, 1), (true, 2)]) (axis := 2)
    (tm := 99408) (pm := 49702) (t' := 99503) (p' := 49750)
    (by decide +kernel) node2961 chunk2964

theorem node2963 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 57 98521 49259 (pathBox rootBox [(false, 0), (false, 3), (false, 1), (true, 2)]) =
      some (99504, 49751) :=
  replayAffineTree_split_step (fuel := 56) (t := 98521) (p := 49259)
    (box := pathBox rootBox [(false, 0), (false, 3), (false, 1), (true, 2)]) (axis := 4)
    (tm := 99503) (pm := 49750) (t' := 99504) (p' := 49751)
    (by decide +kernel) node2962 chunk2965

theorem node2964 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 58 98520 49259 (pathBox rootBox [(false, 3), (false, 1), (true, 2)]) =
      some (99505, 49752) :=
  replayAffineTree_split_step (fuel := 57) (t := 98520) (p := 49259)
    (box := pathBox rootBox [(false, 3), (false, 1), (true, 2)]) (axis := 0)
    (tm := 99504) (pm := 49751) (t' := 99505) (p' := 49752)
    (by decide +kernel) node2963 chunk2966

theorem node2965 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 59 98519 49259 (pathBox rootBox [(false, 1), (true, 2)]) =
      some (99506, 49753) :=
  replayAffineTree_split_step (fuel := 58) (t := 98519) (p := 49259)
    (box := pathBox rootBox [(false, 1), (true, 2)]) (axis := 3)
    (tm := 99505) (pm := 49752) (t' := 99506) (p' := 49753)
    (by decide +kernel) node2964 chunk2967

theorem node2966 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 60 98518 49259 (pathBox rootBox [(true, 2)]) =
      some (99507, 49754) :=
  replayAffineTree_split_step (fuel := 59) (t := 98518) (p := 49259)
    (box := pathBox rootBox [(true, 2)]) (axis := 1)
    (tm := 99506) (pm := 49753) (t' := 99507) (p' := 49754)
    (by decide +kernel) node2965 chunk2968

theorem node2967 :
    replayAffineTree concreteLeafCheck topologyStream payloadStream 61 0 0 (pathBox rootBox []) =
      some (99507, 49754) :=
  replayAffineTree_split_step (fuel := 60) (t := 0) (p := 0)
    (box := pathBox rootBox []) (axis := 2)
    (tm := 98518) (pm := 49259) (t' := 99507) (p' := 49754)
    (by decide +kernel) node2948 node2966

end Zeta23.ThmD.Sextuple.MacroPrototype
