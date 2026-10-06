/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.RunningTimes.Sec4.Corollary31_32
public import ThreeSumApsp.Sec4.Corollary32

/-!
# Theorems 24 and 25 on the word RAM

Theorem 24, as in the paper: for `ε < ε*` and `q > 0` choose `c` and `θ` with `ε < R_c(γ)` and with
the `q` of Corollary 31 below the given one (`exists_admissible`), and apply Corollary 31.
Theorem 25, as in the paper: "Apply Theorem 24 with q := κ/2, and ask one query for each position of
W."  A statement "there are programs" gives no program that another one could call, so the lemma
`Theorem24.with_queries` says two things of one `γ`: there is the data structure of Theorem 24, and
there is a program that computes the entries at every set `W` of positions in
`O(N² log² D/D^γ + |W| D^q log D)` time.  In its proof both come from one choice of `c` and `θ`, and
the program is the one of `Corollary32.from_one`, which preprocesses and asks one query for each
position of `W`.  Theorem 24 is the first half of the lemma.  Theorem 25 is its second half at
`q := κ/2`, with `γ' := min{γ, κ/2}` and the sum of the two times from `Theorem25.time`.
The programs are those of Corollaries 31 and 32; only the bounds are rewritten
(`exists_isDataStructure_of_dominated`, `exists_solves_of_dominated`).
-/

public section

open ThreeSumApsp.WordRam

namespace ThreeSumApsp

/-- Theorem 24, and what the proof of Theorem 25 does with it: "ask one query for each position of
W".  For `ε < ε*` and `q > 0` there is a `γ > 0` with the data structure of Theorem 24 and with a
program that computes the entries at every set `W` of positions in
`O(N² log² D/D^γ + |W| D^q log D)` time. -/
theorem Theorem24.with_queries {ε q : ℝ} (hε : ε < epsStar) (hq : 0 < q) :
    ∃ γ : ℝ, 0 < γ ∧ Items.HasDataStructure ε γ q ∧
      ∀ c₀ : ℕ, ∃ (P : List EndStatement.Instr) (b : ℕ) (C : ℝ),
        Solves (thinProduct []) P b (fun x => Items.thinDom 2 ε c₀ x.toThinPair)
          (fun x => C * ((x.N : ℝ) ^ 2 * Real.log x.D ^ 2 / (x.D : ℝ) ^ γ +
            (x.W.length : ℝ) * (x.D : ℝ) ^ q * Real.log x.D)) := by
  obtain ⟨c, θ, hadm, hqθ⟩ := exists_admissible hε hq
  refine ⟨gammaOf c θ, hadm.gamma_pos, fun c₀ => ?_, fun c₀ => ?_⟩
  · exact exists_isDataStructure_of_dominated
      (wordRam_corollary_31 c θ ε hadm.c_gt hadm.θ_pos hadm.θ_lt hadm.thin c₀) (fun _ hx => hx)
      (.refl _ _) (.of_le fun x hx => mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hx.one_le_D hqθ.le) (by positivity))
  · exact exists_solves_of_dominated (Corollary32.from_one hadm c₀)
      (fun x hx => hx.mono one_le_two)
      (dominated_wanted_add (fun x hx => hx.two_le_D) (fun x _ => x.W.length.cast_nonneg) _ hqθ.le)

/-- **Theorem 24**, on the word RAM. -/
theorem wordRam_theorem_24 : Items.Theorem_24 := by
  intro ε q hε hq
  obtain ⟨γ, hγ, hstructure, -⟩ := Theorem24.with_queries hε hq
  exact ⟨γ, hγ, hstructure⟩

/-- **Theorem 25**, on the word RAM. -/
theorem wordRam_theorem_25 : Items.Theorem_25 := by
  intro ε κ hε hκ
  -- "Apply Theorem 24 with q := κ/2, and ask one query for each position of W."
  obtain ⟨γ, hγ, -, hqueries⟩ := Theorem24.with_queries hε (half_pos hκ)
  obtain ⟨C, hC, htime⟩ := Theorem25.time γ κ
  exact ⟨min γ (κ / 2), lt_min hγ (half_pos hκ), fun c₀ =>
    exists_solves_of_dominated (hqueries c₀) (fun _ hx => hx.1)
      (.of_le_const_mul hC fun x ⟨⟨_, hD, _⟩, hW⟩ => htime x.N x.D x.W.length hD hW)⟩

end ThreeSumApsp
