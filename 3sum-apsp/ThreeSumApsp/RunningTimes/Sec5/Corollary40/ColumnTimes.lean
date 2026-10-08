/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Phases
public import ThreeSumApsp.Programs.Sec5.Corollary40.DataStructureBounds
public import ThreeSumApsp.Sec5.Corollary40.GeneralParameters
public import ThreeSumApsp.Sec5.Corollary40.HintSizeArithmetic

/-!
# Corollary 40: what the running times of v-hinted Mv and Mv-hinted Mv have in common

In both problems Phase 2 preprocesses an n × t matrix X and a t × n matrix Y, with t = ⌊n^τ⌋, and
Phase 3 asks for the n entries of a column of XY.  The paper treats the second problem with the
words "The proof is the same, with X := N_{[n],I} and Y := V".  This file has what is the same.

* `ColumnRates τ a₂ a₃`: at these sizes the preprocessing of the data structure takes O(n^a₂) steps
  and n queries take O(n^a₃).  It holds with the exponents of Corollary 26 for τ < 1/18
  (`columnRates_of_lt_eighteenth`) and with those of Corollary 31 for general τ
  (`columnRates_of_genParams`); the latter is for given c, θ, ε and γ, so that one γ serves all
  problems (`exists_genParams` chooses them for a given τ).
* `KitRates.phaseRun_column`: a run of three phases in which Phase 2 takes the time of the
  preprocessing and w more steps, and Phase 3 the time of n queries and O(n) more steps, is a
  `PhaseRun` with the exponents 0, a₂, a₃, if w = O(n^a₂).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec5

open ThreeSumApsp.WordRam ThreeSumApsp.HintedMv Light.Sec4

/-! ## The rates at the sizes n and t -/

/-- The data structure with the parameters G takes, at the sizes N = n and D = t = ⌊n^τ⌋, at most
C n^a₂ steps for the preprocessing, at most C n^a₃ steps for n queries, and at most A n² cells. -/
def ColumnRates (τ a₂ a₃ : ℝ) (G : RatParams) (A : ℕ) (C : ℝ) : Prop :=
  ∀ (R : Program) (n : ℕ), 1 ≤ n →
    KitRates (kit31 G R) (limKit31 G n (hintSize τ n)) A (slopeExp31 G) C n (hintSize τ n)
      ((n : ℝ) ^ a₂) ((n : ℝ) ^ a₃ / n)

/-- Rates tp and tq with tp ≤ E n^a₂ and n tq ≤ E n^a₃ are rates for a column. -/
theorem columnRates_of_le {τ a₂ a₃ C E : ℝ} {G : RatParams} {A : ℕ} {tp tq : ℕ → ℝ} (hC : 0 ≤ C)
    (hrates : ∀ (R : Program) (n : ℕ), 1 ≤ n →
      KitRates (kit31 G R) (limKit31 G n (hintSize τ n)) A (slopeExp31 G) C n (hintSize τ n) (tp n)
        (tq n))
    (htp : ∀ n : ℕ, 1 ≤ n → tp n ≤ E * (n : ℝ) ^ a₂)
    (htq : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * tq n ≤ E * (n : ℝ) ^ a₃) :
    ColumnRates τ a₂ a₃ G A (C * E) := fun R n hn =>
  (hrates R n hn).mono hC (htp n hn) (by
    rw [← mul_div_assoc, le_div_iff₀' (Nat.cast_pos.2 hn)]
    exact htq n hn)

/-- **The rates of Corollary 26**, for 0 < τ < 1/18: "in O(n²/D^0.063) = O(n^{2−0.063τ}) time" and
"O(n D^0.437) = O(n^{1+0.437τ}) time". -/
theorem columnRates_of_lt_eighteenth {τ : ℝ} (h0 : 0 < τ) (h1 : τ < 1 / 18) :
    ∃ (G : RatParams) (A : ℕ) (C : ℝ), 0 ≤ C ∧
      ColumnRates τ (2 - 0.063 * τ) (1 + 0.437 * τ) G A C := by
  obtain ⟨A, C, hC, hrates⟩ := kitRates_corollary26
  exact ⟨_, A, C * 2, by positivity, columnRates_of_le hC
    (fun R n hn => hrates R n _ (one_le_hintSize hn h0.le) (hintSize_pow_eighteen_le hn h1.le))
    (fun n hn => sq_div_hintSize_le hn h0.le)
    (fun n hn => (mul_hintSize_rpow_le hn τ).trans
      (le_mul_of_one_le_left (by positivity) (by norm_num)))⟩

/-- **The rates of Corollary 31**, for parameters c, θ, ε, γ as in `GenParams` and 0 < τ < ε: "Phase
2 in O(n²/D^γ) = O(n^{2−γτ}) time and Phase 3 in O(n D^{1/2}) = O(n^{1+τ/2}) time". -/
theorem columnRates_of_genParams {c θ ε γ τ : ℝ} (p : GenParams c θ ε γ) (h0 : 0 < τ)
    (hτ : τ < ε) :
    ∃ (G : RatParams) (A : ℕ) (C : ℝ), 0 ≤ C ∧ ColumnRates τ (2 - γ * τ) (1 + τ / 2) G A C := by
  obtain ⟨G, A, C, -, hC, hrates⟩ := kitRates_corollary31 p.toAdmissible 0
  obtain ⟨C₁, hC₁, hpre⟩ := general_pre_le p.γ_pos.le p.γ_lt
  obtain ⟨C₂, hC₂, hquery⟩ := general_query_le (qOf_nonneg θ p.θ_pos p.θ_lt) p.q_lt
  have hτ1 : τ ≤ 1 := by linarith [p.ε_lt_epsStar, sec4_epsStar_numeric.2]
  refine ⟨G, A, C * (C₁ + C₂), by positivity, columnRates_of_le hC
    (fun R n hn => hrates R n _ (one_le_hintSize hn h0.le) (hintSize_le hn hτ1)
      fun _ => (hintSize_le_rpow n τ).trans (natCast_rpow_le_rpow hn hτ.le))
    (fun n hn => ?_) (fun n hn => ?_)⟩
  · exact (hpre n τ hn h0.le).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · exact ((mul_assoc _ _ _).symm.trans_le (hquery n τ hn h0.le)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

/-! ## The three phases -/

/-- The inputs, the output and what else lies before the data structure, at most 3 + 5 n² cells,
and a data structure of at most A n² cells take polynomially many cells. -/
theorem columnSpace_le {n fr A s sz : ℕ} (hfr : fr ≤ 3 + 5 * (n * n)) (hsz : sz ≤ A * (n * n)) :
    fr + sz ≤ polyBound (s + Nat.size (A + 8)) 40 [n] := by
  refine le_polyBound_of_le_pow (e := 2) (by norm_num) ?_
  have hsq : (A + 8) * (n + 1) ^ 2 = A * (n * n) + A * (2 * n + 1) + 8 * (n * n) + 16 * n + 8 := by
    ring
  omega

/-- **Three phases over a kit with given rates.**  The data structure lies at the address fr, with
n ≤ fr ≤ 3 + 5 n², and the memory ends after it.  If Phase 1 takes at most 4 steps, Phase 2 the
time of the preprocessing and w ≤ 100 (n^a₂ + 1) more steps, and Phase 3 the time of n queries and
30 n + 64 more steps, then the run is within limits that are polynomial in n, and the phases take
O(1), O(n^a₂) and O(n^a₃) steps. -/
theorem KitRates.phaseRun_column {P : Program} {K : DsKit P} {limK : ℕ → Limits} {A s₀ : ℕ}
    {C a₂ a₃ : ℝ} {n t : ℕ} (hK : KitRates K limK A s₀ C n t ((n : ℝ) ^ a₂) ((n : ℝ) ^ a₃ / n))
    (hC : 0 ≤ C) (hn : 1 ≤ n) (htn : t ≤ n) (ha₃ : 1 ≤ a₃) {fr w : ℕ} (hfr : n ≤ fr)
    (hfr' : fr ≤ 3 + 5 * (n * n)) (hw : (w : ℝ) ≤ 100 * ((n : ℝ) ^ a₂ + 1))
    {good : (ℕ → ℤ) → ℕ → Prop} {p₁ p₂ p₃ c₁ c₂ c₃ : ℕ} {ws₁ ws₂ ws₃ : List ℤ} (h₁ : c₁ ≤ 4)
    (h₂ : c₂ ≤ K.tPre n t + w) (h₃ : c₃ ≤ n * (K.tQ t + 30) + 64)
    (hrun : LightPhases (limK (fr + K.size n t)) P good (fun _ => 0) 0
      [(p₁, ws₁, c₁), (p₂, ws₂, c₂), (p₃, ws₃, c₃)]) :
    PhaseRun (limK (fr + K.size n t)) P (s₀ + Nat.size (A + 8) + 1) 40 (C + 100) n [n, t] good
      [(p₁, ws₁, c₁), (p₂, ws₂, c₂), (p₃, ws₃, c₃)] [0, a₂, a₃] := by
  obtain ⟨-, hword, -⟩ := hK.lim_at fr
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hpow₂ : (0 : ℝ) ≤ (n : ℝ) ^ a₂ := by positivity
  refine {
    small := hK.small n 40 (s₀ + Nat.size (A + 8)) _ le_rfl le_rfl (by omega)
      (columnSpace_le hfr' hK.size_le)
    sizes_le := by
      simpa using And.intro (le_trans (by exact_mod_cast hfr.trans (Nat.le_add_right _ _)) hword)
        (le_trans (by exact_mod_cast (htn.trans hfr).trans (Nat.le_add_right _ _)) hword)
    steps := .cons ?_ (.cons ?_ (.cons ?_ .nil))
    run := hrun } <;> unfold Within
  · -- Phase 1 returns at once
    have hsteps : (c₁ : ℝ) ≤ 4 := by exact_mod_cast h₁
    rw [Real.rpow_zero]
    linarith
  · -- Phase 2: the preprocessing, at most C n^a₂ steps, and w steps
    have hsteps : (c₂ : ℝ) ≤ (K.tPre n t : ℝ) + w := by exact_mod_cast h₂
    linarith [hK.tPre_le]
  · -- Phase 3: n queries, at most C n^a₃ steps, and 30 n + 64 steps, where n ≤ n^a₃
    have hsteps : (c₃ : ℝ) ≤ (n : ℝ) * ((K.tQ t : ℝ) + 30) + 64 := by exact_mod_cast h₃
    have hquery : (n : ℝ) * (K.tQ t : ℝ) ≤ C * (n : ℝ) ^ a₃ :=
      calc (n : ℝ) * (K.tQ t : ℝ) ≤ n * (C * ((n : ℝ) ^ a₃ / n)) :=
            mul_le_mul_of_nonneg_left hK.tQ_le hn0.le
        _ = C * (n : ℝ) ^ a₃ := by field_simp
    have hlinear : (n : ℝ) ≤ (n : ℝ) ^ a₃ := by simpa using natCast_rpow_le_rpow hn ha₃
    linarith

end Light.Sec5
