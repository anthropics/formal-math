/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Program
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.RealParameters
public import ThreeSumApsp.RunningTimes.Sec4.Corollary31_32.Arithmetic

/-!
# Corollaries 31 and 32 on the word RAM

The route.  For rational `c` and `θ` the data structure of Theorem 30 with `L = ⌈cm⌉` levels and
switching order `t = ⌈θm⌉` is one program (`Light.Sec4.program31`), which computes `m`, `L` and `t`
itself.  The parameters include a threshold `m₀`: for `m < m₀` the preprocessing finds `m` and `4^m`
and stores the flag 0, and a query computes an inner product (the paper: "for smaller m the
corollary again holds trivially").  Real `c` and `θ` are replaced by rational ones nearby, for which
`ε` is still admissible, `γ` is no smaller and `q` no larger; at these the two costs of Theorem 30
obey the bounds of the corollaries on the inputs with `D ≤ N^ε` and `m ≥ m₀`
(`Light.Sec4.exists_ratParams`).  The two lemmas about this program, compiled
(`Light.Sec4.isDataStructure_of_costsWithin` for the data structure,
`Light.Sec4.solves_of_costsWithin` for the wanted entries), then give both corollaries in a form
that includes `D = 1` (`Corollary31.from_one`, `Corollary32.from_one`).  The corollaries as
printed, and the bounds without logarithmic factors for every `ε < ε*`
(`dataStructureBelow_wantedBelow_epsStar`), follow by arithmetic alone: the same programs, a smaller
domain, and a bound that dominates the proved one (`exists_isDataStructure_of_dominated`,
`exists_solves_of_dominated`).
-/

public section

open ThreeSumApsp.WordRam
open Light Light.Sec4

namespace ThreeSumApsp

/-! ## The form that includes `D = 1`

NOTE.  This form is not in the paper.  The last sentences of Theorems 1 and 3 have no lower bound
on `D`, while Theorems 24 and 25 and Corollaries 31 and 32 assume `D ≥ 2`; Section 4.1 adds that
"for D = 1 the bounds are trivial".  In a statement about programs, one program has to serve all
`D`, so the case `D = 1` cannot be added by arithmetic to a statement about `D ≥ 2`.  Here
`log D + 1` stands in place of `log D`, which is 0 at `D = 1`. -/

/-- Corollary 31, on the word RAM, with `D = 1` included: preprocessing in
`O(N² (log D + 1)² / D^γ)` time and space, and a query in `O(D^q (log D + 1))` time. -/
theorem Corollary31.from_one {c θ ε : ℝ} (h : Admissible c θ ε) (c₀ : ℕ) :
    ∃ (P Q : List EndStatement.Instr) (qI qJ qOut : ℤ) (b : ℕ) (C : ℝ),
      IsDataStructure P Q qI qJ qOut b [] (Items.thinDom 1 ε c₀)
        (fun x => C * ((x.N : ℝ) ^ 2 * (Real.log x.D + 1) ^ 2 / (x.D : ℝ) ^ gammaOf c θ))
        (fun x => C * ((x.N : ℝ) ^ 2 * (Real.log x.D + 1) ^ 2 / (x.D : ℝ) ^ gammaOf c θ))
        (fun x => C * ((x.D : ℝ) ^ qOf θ * (Real.log x.D + 1))) := by
  obtain ⟨G, C, hC, hcosts⟩ := exists_ratParams h
  exact ⟨_, _, _, _, _, isDataStructure_of_costsWithin G hC c₀
    fun x ⟨hN, hD, hthin, hU⟩ => ⟨hU, hcosts x.N x.D hN hD hthin⟩⟩

/-- Preprocess `X` and `Y` by Corollary 31 and "ask one query for each position of W" (proof of
Theorem 25; "With Corollary 31 in place of Theorem 24, the same argument gives explicit exponents"),
on the word RAM, with `D = 1` included: the entries at every set `W` of positions in
`O(|W| D^q (log D + 1) + N² (log D + 1)² / D^γ)` time. -/
theorem Corollary32.from_one {c θ ε : ℝ} (h : Admissible c θ ε) (c₀ : ℕ) :
    ∃ (P : List EndStatement.Instr) (b : ℕ) (C : ℝ),
      Solves (thinProduct []) P b (fun x => Items.thinDom 1 ε c₀ x.toThinPair)
        (fun x => C * ((x.W.length : ℝ) * ((x.D : ℝ) ^ qOf θ * (Real.log x.D + 1)) +
          (x.N : ℝ) ^ 2 * (Real.log x.D + 1) ^ 2 / (x.D : ℝ) ^ gammaOf c θ)) := by
  obtain ⟨G, C, hC, hcosts⟩ := exists_ratParams h
  exact ⟨_, solves_of_costsWithin G hC c₀
    fun x ⟨hN, hD, hthin, hU⟩ => ⟨hU, hcosts x.N x.D hN hD hthin⟩⟩

/-! ## The corollaries as printed -/

/-- **Corollary 31**, on the word RAM. -/
theorem wordRam_corollary_31 : Items.Corollary_31 := by
  intro c θ ε hc h0 h1 hε c₀
  exact exists_isDataStructure_of_dominated (Corollary31.from_one ⟨hc, h0, h1, hε⟩ c₀)
    (fun x hx => hx.mono one_le_two) (dominated_preprocessing_log (fun x hx => hx.two_le_D) _)
    (dominated_query_log (fun x hx => hx.two_le_D) _)

/-- **Corollary 32**, on the word RAM. -/
theorem wordRam_corollary_32 : Items.Corollary_32 := by
  intro c θ ε κ hc h0 h1 hε hκ c₀
  exact exists_solves_of_dominated (Corollary32.from_one ⟨hc, h0, h1, hε⟩ c₀)
    (fun x hx => hx.1.mono one_le_two)
    (dominated_wanted_log (fun x hx => hx.1.two_le_D) fun x hx => hx.2)

/-! ## Without the logarithmic factors, for every `ε < ε*` -/

/-- The last sentences of Theorems 3 and 1, on the word RAM, for every `ε < ε*` (the theorems have
`ε < 0.1204`): choose `c` and `θ` as in the proof of Theorem 24 (`exists_admissible`), for the
wanted entries with `q := κ/2` and `γ' := min{γ, κ/2}` as in the proof of Theorem 25, and give away
half of the exponent to absorb the logarithmic factors. -/
theorem dataStructureBelow_wantedBelow_epsStar :
    Items.DataStructureBelow epsStar ∧ Items.WantedBelow epsStar := by
  refine ⟨fun ε q hε hq => ?_, fun ε κ hε hκ => ?_⟩
  · obtain ⟨c, θ, hadm, hqθ⟩ := exists_admissible hε hq
    have hγ := hadm.gamma_pos
    exact ⟨gammaOf c θ / 2, half_pos hγ, fun c₀ => exists_isDataStructure_of_dominated
      (Corollary31.from_one hadm c₀) (fun _ hx => hx)
      (dominated_preprocessing (fun x hx => hx.one_le_D) (half_lt_self hγ))
      (dominated_query (fun x hx => hx.one_le_D) hqθ)⟩
  · obtain ⟨c, θ, hadm, hqθ⟩ := exists_admissible hε (half_pos hκ)
    have hmin : 0 < min (gammaOf c θ) (κ / 2) := lt_min hadm.gamma_pos (half_pos hκ)
    have hhalf := half_lt_self hmin
    exact ⟨min (gammaOf c θ) (κ / 2) / 2, half_pos hmin, fun c₀ => exists_solves_of_dominated
      (Corollary32.from_one hadm c₀) (fun _ hx => hx.1)
      (dominated_wanted_sparse (fun x hx => hx.1.one_le_D) (fun x hx => hx.2)
        (hhalf.trans_le (min_le_left _ _))
        ((hhalf.trans_le (min_le_right _ _)).trans (by linarith)))⟩

end ThreeSumApsp
