/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.TimeClaims.Sec3.Arithmetic
public import ThreeSumApsp.TimeClaims.Sec5.Definitions
public import ThreeSumApsp.Util.Asymptotics.LogU

/-!
# Corollary 39 from Theorem 19

All lemmas are about an arbitrary interpretation `M : DetTimeModel5` of "is solved in time T".

A `k`-clique is a triangle in one of `n^t` graphs `H` on `N = n^⌊k/3⌋` vertices per part, with
weights up to `binom(k, 2) n^κ` (`κ` is the paper's ν).  For constant `k` and `κ` all times are
functions of `n` alone, bounded from above up to logarithms:

1. Theorem 19 decides whether `H` has a triangle of weight zero in time `Õ(N^{3-ε'})`
   (`upperPowPolylog_exactTriangle`);
2. a maximum weight triangle costs `O(log² n)` times as much, and a minimum weight triangle is a
   maximum weight triangle for the negated weights (`upperPowPolylog_maxTriangle` and the first
   lines of `minMaxClique_of_theorem_19_VW13`);
3. building a graph costs `Õ(N²)` (`isPowPolylog_sq_mul_one_add_logU`), and the `n^t` graphs
   together cost `Õ(n^t N^{3-ε'}) ⊆ O(n^{k-ε_T ⌊k/3⌋})` (`upperBigOPow_clique`,
   `exists_clique_of_triangle`).
-/

public section

namespace ThreeSumApsp

open Filter

/-- `N = n^w` is `O(n^w)`. -/
private theorem isBigOPow_cast_pow (w : ℕ) : IsBigOPow (fun n : ℕ => ((n ^ w : ℕ) : ℝ)) w := by
  simpa only [Nat.cast_pow] using isBigOPow_natCast_pow w

/-- Writing a graph on `N = n^w` vertices per part costs `N² (1 + log U) = Õ(N^{3-ε'})`. -/
private theorem isPowPolylog_sq_mul_one_add_logU (w : ℕ) {U : ℕ → ℝ}
    (hU : IsPowPolylog (fun n => logU (U n)) 0) :
    IsPowPolylog (fun n : ℕ => ((n ^ w : ℕ) : ℝ) ^ 2 * (1 + logU (U n)))
      ((3 - 0.00175) * w) :=
  (((isBigOPow_cast_pow w).pow 2).isPowPolylog.mul ((isPowPolylog_const 1).add hU)).mono (by
    have hw : (0 : ℝ) ≤ w := w.cast_nonneg
    push_cast
    linarith)

/-- "Theorem 19 decides whether H has a triangle of weight zero in O(N^{3-ε'} log N) time": the
explicit bound of Theorem 19 at `N = n^w` vertices per part and weights up to `U(n) ≤ n^κ`. -/
private theorem upperPowPolylog_exactTriangle {T : ℕ → ℝ → ℝ} {K : ℝ}
    (hb : ∀ (n : ℕ) (κ u : ℝ), 16 ^ 18 ≤ n → 1 ≤ κ → u ≤ (n : ℝ) ^ κ →
      T n u ≤ K * (κ * ((n : ℝ) ^ (3 - 0.00175 : ℝ) * Real.log n ^ 1)))
    {w : ℕ} (hw : 1 ≤ w) {κ : ℝ} (hκ : 1 ≤ κ) {U : ℕ → ℝ}
    (hU : ∀ᶠ n : ℕ in atTop, U n ≤ (n : ℝ) ^ κ) :
    UpperPowPolylog (fun n => T (n ^ w) (U n)) ((3 - 0.00175) * w) := by
  refine ((((isPowPolylog_rpow_mul_log_pow (3 - 0.00175) 1).comp (isBigOPow_cast_pow w)
    (by norm_num) w.cast_nonneg).const_mul κ).const_mul K).upperPowPolylog.mono_left ?_
  filter_upwards [hU, eventually_ge_atTop (16 ^ 18)] with n hu hn
  have hsize : n ≤ n ^ w := Nat.le_self_pow (by omega) n
  exact hb (n ^ w) κ (U n) (hn.trans hsize) hκ
    (hu.trans (Real.rpow_le_rpow n.cast_nonneg (Nat.cast_le.2 hsize) (by linarith)))

/-- "Finding a maximum weight triangle costs O(log² n) times as much": the time that the cited
reduction gives on `N = n^w` vertices per part. -/
private theorem upperPowPolylog_maxTriangle {F U : ℕ → ℝ} {C : ℝ} (w : ℕ) (hC : 0 ≤ C)
    (hF : UpperPowPolylog F ((3 - 0.00175) * w)) (hU : IsPowPolylog (fun n => logU (U n)) 0) :
    UpperPowPolylog (fun n : ℕ => C * ((F n + ((n ^ w : ℕ) : ℝ) ^ 2 * (1 + logU (U n))) *
      (logU (U n) + Real.log ((n ^ w : ℕ) : ℝ) + 1) ^ 2)) ((3 - 0.00175) * w) := by
  have hrounds := ((hU.add (isBigOPow_cast_pow w).isPowPolylog_log_natCast).add
    (isPowPolylog_const 1)).pow 2
  exact (((hF.add (isPowPolylog_sq_mul_one_add_logU w hU).upperPowPolylog).mul
    hrounds.upperPowPolylog (.of_forall fun n => sq_nonneg _)).const_mul hC).mono
      (le_of_eq (by ring))

/-- "The n^t graphs together cost O(n^t N^{3-ε_T}) = O(n^{k-ε_T ⌊k/3⌋})": if one graph costs
`F(n) = Õ(N^{3-ε'})`, apart from building it. -/
private theorem upperBigOPow_clique {k : ℕ} (hk : 3 ≤ k) {F U : ℕ → ℝ} (C₀ : ℝ)
    (hF : UpperPowPolylog F ((3 - 0.00175) * ((k / 3 : ℕ) : ℝ)))
    (hU : IsPowPolylog (fun n => logU (U n)) 0) :
    UpperBigOPow (fun n : ℕ => (n : ℝ) ^ KClique.numFixed k *
        (F n + C₀ * (((n ^ (k / 3) : ℕ) : ℝ) ^ 2 * (1 + logU (U n)))))
      (Claim.cliqueExponent k) := by
  have hthird : (1 : ℝ) ≤ ((k / 3 : ℕ) : ℝ) := Nat.one_le_cast.2 (by omega)
  have hfixed : ((KClique.numFixed k : ℕ) : ℝ) = (k : ℝ) - 3 * ((k / 3 : ℕ) : ℝ) := by
    rw [KClique.numFixed, Nat.cast_sub (Nat.mul_div_le k 3)]
    push_cast
    ring
  have hgraph := hF.add
    ((isPowPolylog_sq_mul_one_add_logU (k / 3) hU).const_mul C₀).upperPowPolylog
  have hall := hgraph.mul
    (isBigOPow_natCast_pow (KClique.numFixed k)).isPowPolylog.upperPowPolylog
    (.of_forall fun n => by positivity)
  simpa only [mul_comm] using hall.upperBigOPow (by rw [hfixed, Claim.cliqueExponent]; linarith)

/-- The reduction from a clique problem to a triangle problem, on weights up to `n^κ`: if the
triangle problem on one graph `H` costs `Õ(N^{3-ε'})`, the clique problem costs
`O(n^{k-ε_T ⌊k/3⌋})`. -/
private theorem exists_clique_of_triangle {k : ℕ} (hk : 3 ≤ k) {κ : ℝ} (hκ : 1 ≤ κ)
    {triangle clique : (ℕ → ℝ → ℝ) → Prop} (hfold : Claim.CliqueFromTriangle triangle clique k)
    {T : ℕ → ℝ → ℝ} (hT : triangle T)
    (hgraph : UpperPowPolylog (fun n : ℕ => T (n ^ (k / 3)) ((k.choose 2 : ℝ) * (n : ℝ) ^ κ))
      ((3 - 0.00175) * ((k / 3 : ℕ) : ℝ))) :
    ∃ T' : ℕ → ℝ → ℝ, clique T' ∧
      UpperBigOPow (fun n => T' n ((n : ℝ) ^ κ)) (Claim.cliqueExponent k) := by
  obtain ⟨C₀, hfold⟩ := hfold
  exact ⟨_, hfold T hT, upperBigOPow_clique hk C₀ hgraph
    (isPowPolylog_logU_of_le (c := 1) fun n hn =>
      ⟨Real.one_le_rpow (Nat.one_le_cast.2 hn) (by linarith), (one_mul _).ge⟩)⟩

/-- The weights of the graphs `H`: `log (binom(k, 2) n^κ) = Õ(1)`. -/
private theorem isPowPolylog_logU_weights {k : ℕ} (hk : 3 ≤ k) {κ : ℝ} (hκ : 1 ≤ κ) :
    IsPowPolylog (fun n : ℕ => logU ((k.choose 2 : ℝ) * (n : ℝ) ^ κ)) 0 :=
  isPowPolylog_logU_mul_rpow (Nat.one_le_cast.2 (Nat.choose_pos (by omega))) (by linarith)

/-- The deduction of the Zero-Weight part of Corollary 39 from Theorem 19 (in the explicit form of
`Claim.Theorem_19_explicit`): "Theorem 19 decides whether H has a triangle of weight zero
in O(N^{3-ε'} log N) time ... so each graph H costs O(N^{3-ε_T}) time, and the n^t graphs together
cost O(n^t N^{3-ε_T}) = O(n^{k-ε_T⌊k/3⌋})." -/
theorem zeroClique_of_theorem_19 (M : DetTimeModel5) (k : ℕ) (hk : 3 ≤ k)
    (h19 : Claim.Theorem_19_explicit M.toDetTimeModel 0.00175 1)
    (hfold : Claim.ZeroCliqueFromExactTriangle M k) : Claim.Corollary_39_zero M k := by
  obtain ⟨K, T, hT, hb⟩ := h19
  intro κ hκ
  exact exists_clique_of_triangle hk hκ hfold hT
    (upperPowPolylog_exactTriangle hb (by omega) (by linarith : 1 ≤ κ + 1)
      (eventually_mul_rpow_le _ (lt_add_one κ)))

/-- The deduction of the Min-Weight and Max-Weight parts of Corollary 39 from Theorem 19 and the
cited [VW13, Theorem 3.3].  The paper: "finding a maximum weight triangle costs O(log² n) times as
much, and a minimum weight triangle is a maximum weight triangle for the negated weights.  Since
ε' > ε_T, the logarithmic factors are absorbed". -/
theorem minMaxClique_of_theorem_19_VW13 (M : DetTimeModel5) (k : ℕ) (hk : 3 ≤ k)
    (h19 : Claim.Theorem_19_explicit M.toDetTimeModel 0.00175 1)
    (hVW : Claim.VW13_Theorem_3_3_max M) (hneg : Claim.MinTriangleFromMax M)
    (hmax : Claim.MaxCliqueFromMaxTriangle M k) (hmin : Claim.MinCliqueFromMinTriangle M k) :
    Claim.Corollary_39_min_max M k := by
  obtain ⟨K, T, hT, hb⟩ := h19
  obtain ⟨c, C, hc, hC, hVW⟩ := hVW
  obtain ⟨Cn, hneg⟩ := hneg
  intro κ hκ
  have hweights := isPowPolylog_logU_weights hk hκ
  have hzero : UpperPowPolylog (fun n : ℕ => T (n ^ (k / 3)) (c * ((k.choose 2 : ℝ) * (n : ℝ) ^ κ)))
      ((3 - 0.00175) * ((k / 3 : ℕ) : ℝ)) :=
    upperPowPolylog_exactTriangle hb (by omega) (by linarith : 1 ≤ κ + 1) (by
      simpa only [mul_assoc] using eventually_mul_rpow_le (c * (k.choose 2 : ℝ)) (lt_add_one κ))
  have hmaxTriangle := upperPowPolylog_maxTriangle (k / 3) hC hzero hweights
  have hminTriangle := hmaxTriangle.add
    ((isPowPolylog_sq_mul_one_add_logU (k / 3) hweights).const_mul Cn).upperPowPolylog
  exact ⟨exists_clique_of_triangle hk hκ hmin (hneg _ (hVW T hT)) hminTriangle,
    exists_clique_of_triangle hk hκ hmax (hVW T hT) hmaxTriangle⟩

end ThreeSumApsp
