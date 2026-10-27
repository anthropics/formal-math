/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Top.Defs
import ClauseBound.Alg.Decode
import ClauseBound.Alg.CertTop
import PaddedDescent.Col.CertG

/-! # The test whether every variable occurs is polynomial-time

`allOccU_polyT`: the test `allOccU`, whether every variable occurs in the formula read from the
input, is polynomial-time. -/

public section

namespace UniformInK.CertBoth

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks

/-- The test whether every variable occurs is polynomial-time. -/
theorem allOccU_polyT : PolyT allOccU := by
  have hd : PolyT fmlOf := Decode.stCertDecM.2
  have hn : Unary nU := Unary.of_length hd.fst
  obtain ⟨F, hF, hFe⟩ : ∃ F : List Bool → Fml, PolyT F ∧ ∀ x, (fmlOf x).2 = F x := ⟨_, hd.snd, fun _ => rfl⟩
  have e : allOccU = fun x => (List.range (nU x)).all fun v => (F x).any fun C => C.any fun l => l.1 == v := by
    funext x
    rw [allOccU, hFe]
  rw [e]
  fun_prop

end UniformInK.CertBoth

namespace UniformInK

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK.CertBoth

end UniformInK
