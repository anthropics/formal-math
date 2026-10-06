/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.Corollary31.Limit
public import ThreeSumApsp.Sec4.Table2

/-!
# The captions of Tables 1 and 2

* "the θ at which γ = κ - q" (Section 4.4), which the right half of Table 2 uses: `γ` and `q`
  increase with `θ` (`gammaOf_strictMono`, `qOf_strictMonoOn`), so `γ + q` takes the value `κ`
  exactly once, and there the exponent `min{γ, κ - q}` of Corollary 32 is largest
  (`exists_gammaOf_eq_sub_qOf`). Nothing else rests on this lemma.
* For every entry, Corollary 31 or 32 gives what the caption of Table 2 claims:
  `table_2_query_valid`, `table_2_ninth_valid`, `table_2_density_valid`.
* "A larger c gives a larger γ but a smaller ε" (`table_2_larger_c`), and the parameters of Section
  2 are the entry `c = 19`, `q = 0.43` (`table_1_section_2_column`).

The rows themselves are `table_2_c40` to `table_2_c10_5`.
-/

public section

open Finset

namespace ThreeSumApsp

/-! ## The `θ` at which `γ = κ - q` -/

/-- The balance point exists: `γ + q` is continuous, it is 0 at `θ = 0`, and at `θ = 0.9` it exceeds
`log_4 10 ≥ κ`. -/
private lemma exists_gammaOf_add_qOf_eq (c κ : ℝ) (hc : 10 < c) (hκ0 : 0 < κ)
    (hκ1 : κ ≤ Real.logb 4 10) : ∃ θ : ℝ, 0 < θ ∧ θ < 0.9 ∧ gammaOf c θ + qOf θ = κ := by
  have hzero : gammaOf c 0 + qOf 0 < κ := by
    rw [gammaOf_eq_mul, qOf_zero]
    linarith
  have hnine : κ < gammaOf c 0.9 + qOf 0.9 := by
    rw [qOf_nine_tenths]
    linarith [corollary_31_gamma_pos c 0.9 hc (by norm_num)]
  obtain ⟨θ, hθ, hθκ⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 0.9)
    (continuous_gammaOf_add_qOf c).continuousOn ⟨hzero, hnine⟩
  exact ⟨θ, hθ.1, hθ.2, hθκ⟩

/-- Section 4.4 speaks of "the θ at which γ = κ - q": there is exactly one such `θ` in `(0, 0.9)`
when `c > 10` and `0 < κ ≤ log_4 10`, and the exponent `min{γ, κ - q}` of Corollary 32 is largest
there. At this `θ` the two terms of Corollary 32 are equal; Section 4.1: "Setting the parameters to
balance the preprocessing time and the total time for all the queries". -/
theorem exists_gammaOf_eq_sub_qOf (c κ : ℝ) (hc : 10 < c) (hκ0 : 0 < κ) (hκ1 : κ ≤ Real.logb 4 10) :
    ∃ θ : ℝ, (0 < θ ∧ θ < 0.9 ∧ gammaOf c θ = κ - qOf θ) ∧
      (∀ θ' : ℝ, 0 < θ' → θ' < 0.9 → gammaOf c θ' = κ - qOf θ' → θ' = θ) ∧
      (∀ θ' : ℝ, 0 < θ' → θ' < 0.9 →
        min (gammaOf c θ') (κ - qOf θ') ≤ min (gammaOf c θ) (κ - qOf θ)) := by
  obtain ⟨θ, hθ0, hθ9, hθκ⟩ := exists_gammaOf_add_qOf_eq c κ hc hκ0 hκ1
  have hθ : θ ∈ Set.Icc (0 : ℝ) 0.9 := ⟨hθ0.le, hθ9.le⟩
  have hγ := gammaOf_strictMono c hc
  refine ⟨θ, ⟨hθ0, hθ9, eq_sub_of_add_eq hθκ⟩, fun θ' h0 h9 hθ' => ?_, fun θ' h0 h9 => ?_⟩
  · -- Uniqueness: `γ + q` increases strictly.
    exact ((hγ.strictMonoOn _).add qOf_strictMonoOn).injOn ⟨h0.le, h9.le⟩ hθ
      ((add_eq_of_eq_sub hθ').trans hθκ.symm)
  · -- Below `θ` the first term of the minimum is smaller, above `θ` the second one is.
    rw [min_eq_left (eq_sub_of_add_eq hθκ).le]
    rcases le_total θ' θ with h | h
    · exact (min_le_left _ _).trans (hγ.monotone h)
    · have hq := qOf_strictMonoOn.monotoneOn hθ ⟨h0.le, h9.le⟩ h
      exact (min_le_right _ _).trans (by linarith)

/-! ## What the caption of Table 2 claims for an entry -/

/-- Caption of Table 2, left half: "the numerical entry is a value γ for which Theorem 24 holds,
meaning that after O(N² log² D/D^γ) preprocessing, a query takes O(D^q log D) time", "whenever
D ≤ N^ε". For an entry computed as Section 4.4 prescribes (`Table2Query`), Corollary 31 gives these
bounds (`ValidQueryEntry`). -/
theorem table_2_query_valid (c ε q γ₀ : ℝ) (h : Table2Query c ε q γ₀) :
    ValidQueryEntry c ε q γ₀ := by
  obtain ⟨hc, θ, h0, h9, hq, hγ₀, -, hε⟩ := h
  exact ⟨hc, θ, h0, h9, hε, hq.le, hγ₀⟩

/-- Caption of Table 2: "the column q = 0.43 uses the switching order t = m/9 of Section 2 (more
precisely, q = 0.4277…)". For an entry of this column, computed at `θ = 1/9` (`Table2Ninth`),
Corollary 31 gives the bounds of the caption with `q = 0.43`. -/
theorem table_2_ninth_valid (c ε γ₀ : ℝ) (h : Table2Ninth c ε γ₀) :
    ValidQueryEntry c ε 0.43 γ₀ := by
  obtain ⟨hc, hγ₀, -, hε⟩ := h
  exact ⟨hc, 1 / 9, by norm_num, by norm_num, hε, qOf_ninth_mem.2.trans (by norm_num), hγ₀⟩

/-- Caption of Table 2, right half: "the numerical entry is a value γ for which Theorem 25 holds,
meaning that any |W| ≤ N²/D^κ wanted entries take O(N² log² D/D^γ) time". For an entry computed as
Section 4.4 prescribes (`Table2Density`), Corollary 32 gives this bound (`ValidDensityEntry`). -/
theorem table_2_density_valid (c ε κ γ₀ : ℝ) (h : Table2Density c ε κ γ₀) :
    ValidDensityEntry c ε κ γ₀ := by
  obtain ⟨hc, hκ, θ, h0, h9, hθκ, hγ₀, -, hε⟩ := h
  exact ⟨hc, hκ, θ, h0, h9, hε, le_min hγ₀ (hγ₀.trans hθκ.le)⟩

/-! ## The captions -/

/-- Caption of Table 2: "A larger c gives a larger γ but a smaller ε" (at a fixed `θ > 0`). A fixed
`θ` is a fixed column of the left half of the table: there `γ` increases with `c` and `R_c(γ)`
decreases. In the right half `θ` changes with `c`; for it the sentence is not stated. Nor is it
stated for the `ε` of a row, which is the smallest `R_c(γ)` over all entries of the row. -/
theorem table_2_larger_c (θ : ℝ) (hθ : 0 < θ) :
    StrictMonoOn (fun c : ℝ => gammaOf c θ) (Set.Ioi 10) ∧
      StrictAntiOn (fun c : ℝ => Rc c (gammaOf c θ)) (Set.Ioi 10) := by
  refine ⟨fun c₁ h1 c₂ _ h12 => gammaOf_lt_gammaOf hθ h1 h12, fun c₁ h1 c₂ h2 h12 => ?_⟩
  have h1' : 10 < c₁ := h1
  have h2' : 10 < c₂ := h2
  have hpos : 0 < gammaOf c₁ θ := corollary_31_gamma_pos c₁ θ h1' hθ
  have hlt := gammaOf_lt_gammaOf hθ h1' h12
  -- First raise `γ` at the ratio `c₂`, then compare the two ratios at the smaller `γ`.
  calc Rc c₂ (gammaOf c₂ θ) < Rc c₂ (gammaOf c₁ θ) :=
        Rc_strictAntiOn_right c₂ h2'.le (Set.mem_Ici.2 hpos.le) (Set.mem_Ici.2 (hpos.trans hlt).le)
          hlt
    _ < Rc c₁ (gammaOf c₁ θ) :=
        sec4_Rc_strictAntiOn _ hpos.le (Set.mem_Ici.2 h1'.le) (Set.mem_Ici.2 h2'.le) h12

/-- Table 1 (column "in Section 2"), Table 2's caption and Section 4.1: at `L = 19m` one has
"ρ < 1/2"; the bold entry `c = 19`, `θ = 1/9` is Theorem 5, "where γ = 1/18 = 0.0555…"; Theorem 5's
`ε = 1/18` is below `R_19(1/18)`; and "Theorem 5 is the entry c = 19, q = 0.43, applied to a set W
of N²/√D wanted entries (that is, κ = 1/2)", where the exponent `min{γ, κ - q}` of Corollary 32 is
still `1/18`. -/
theorem table_1_section_2_column :
    (∀ m : ℕ, rho (19 * m) m < 1 / 2) ∧
      gammaOf 19 (1 / 9) = 1 / 18 ∧
      1 / 18 < Rc 19 (1 / 18) ∧
      min (gammaOf 19 (1 / 9)) (1 / 2 - qOf (1 / 9)) = 1 / 18 := by
  have hγ : gammaOf 19 (1 / 9) = 1 / 18 := by
    rw [gammaOf_19]
    norm_num
  refine ⟨fun m => ?_, hγ,
    (lt_Rc_of_lnΛ_zero_mem (Γ := 1 / 18) lnΛ_19_zero_mem) _ (by norm_num) le_rfl, ?_⟩
  · have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    unfold rho
    push_cast
    rw [div_lt_iff₀ (by linarith)]
    linarith
  · rw [hγ]
    exact min_eq_left (by linarith [qOf_ninth_mem.2])

end ThreeSumApsp
