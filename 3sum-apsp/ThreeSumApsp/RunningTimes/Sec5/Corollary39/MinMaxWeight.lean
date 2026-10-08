/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec5.Corollary39.MinMaxWeight.Host
public import ThreeSumApsp.Programs.Sec5.Corollary39.MinMaxWeight.TimeBound
public import ThreeSumApsp.RunningTimes.Sec5.Corollary39.ZeroWeight

/-!
# Corollary 39, minimum and maximum weight, on the word RAM

Corollary 39 finds a k-clique of minimum, or of maximum, total weight.

* The host that builds the graph H for each choice of the fixed vertices and calls a solver that
  finds a best triangle takes at most n^t (T(N, ·) + C N²) steps (`exists_optTime_le`).  So it
  proves the two transfer claims of the proof (`claim_maxCliqueFromMaxTriangle`,
  `claim_minCliqueFromMinTriangle`).  The two other claims are [VW13, Theorem 3.3] for finding a
  maximum weight triangle, and the negation of the weights (`claim_VW13_Theorem_3_3_max`,
  `claim_minTriangleFromMax`).
* The input is that of Zero-Weight k-Clique.  The vertices of the clique go to the k cells behind
  it, and the free pointer is behind them (`optInst`, `pre_optClique`, `post_optClique`).  So a
  solver of either task gives a program for the layout of the end statement (`wrapMaxClique`,
  `wrapMinClique`).
* With the bound of Theorem 19 for Exact Triangle, the arithmetic of the running times, which holds
  for any reading of "is solved in time T" (`minMaxClique_of_theorem_19_VW13`), gives
  the bound of Corollary 39, and `Wrap.realized` and `FromClaims.solvedAt_of_realized` carry it to
  the word RAM (`corollary_39_min_max_of_theorem_19`).
-/

@[expose] public section

namespace Light.Sec5

open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.KClique ThreeSumApsp.Spec Light.Sec3

/-! ## The two transfer claims -/

/-- The time of the host: n^t calls of the solver, and a constant times N² steps for each of them
(proof of Corollary 39: t = numFixed k, N = n ^ width k). -/
theorem exists_optTime_le (k : ℕ) : ∃ C : ℕ, ∀ (T : ℕ → ℕ → ℕ) (n U : ℕ), 1 ≤ n →
    optTime k T n U ≤ n ^ numFixed k *
      (T (n ^ width k) (lenH k * U) + C * (n ^ width k * n ^ width k)) := by
  obtain ⟨c, hc⟩ := exists_fillT_le k
  refine ⟨c + (28 * numFixed k + 91) +
    (3 * (14 * width k + 13) + (2 * width k + 2 * numFixed k + 10 * k + 80)), fun T n U hn => ?_⟩
  have hN : 1 ≤ n ^ width k := Nat.one_le_pow _ _ hn
  have hX : 1 ≤ n ^ width k * n ^ width k := Nat.mul_pos hN hN
  -- the steps outside the rounds
  have houtside : 3 * (n ^ width k * (14 * width k + 13)) +
      (2 * width k + 2 * numFixed k + 10 * k + 80) * 1 ≤
      (3 * (14 * width k + 13) + (2 * width k + 2 * numFixed k + 10 * k + 80)) *
        (n ^ width k * n ^ width k) :=
    calc _ ≤ 3 * (n ^ width k * n ^ width k * (14 * width k + 13)) +
          (2 * width k + 2 * numFixed k + 10 * k + 80) * (n ^ width k * n ^ width k) := by
          gcongr
          exact Nat.le_mul_of_pos_left _ hN
      _ = _ := by ring
  refine le_of_eq_of_le ?_ (hostTime_le (Nat.one_le_pow _ _ hn) hX (hc _ hN) houtside)
  unfold optTime optRoundT
  ring

/-- The transfer claim for maximum weight. -/
theorem claim_maxCliqueFromMaxTriangle {k : ℕ} (hk : 3 ≤ k) :
    Claim.MaxCliqueFromMaxTriangle lightModel5 k :=
  let ⟨C, hC⟩ := exists_optTime_le k
  ⟨C, fun _ hT => solvedIn_of_hostTime hk (isHost_maxKc hk) hC hT⟩

/-- The transfer claim for minimum weight. -/
theorem claim_minCliqueFromMinTriangle {k : ℕ} (hk : 3 ≤ k) :
    Claim.MinCliqueFromMinTriangle lightModel5 k :=
  let ⟨C, hC⟩ := exists_optTime_le k
  ⟨C, fun _ hT => solvedIn_of_hostTime hk (isHost_minKc hk) hC hT⟩

/-! ## The layout of the end statement -/

/-- The arguments of the solver: n, U, the address 1 of the weights, the address 1 + k² n² of the
answer, and the free pointer 1 + k + k² n². -/
def wrapOptArgs (kk : ℕ) : List Expr :=
  [v 1, v 2, k 1, k 1 +' k (kk * kk) *' v 3, k (1 + kk) +' k (kk * kk) *' v 3]

/-- The values of the arguments. -/
theorem wrapOpt_vals (kk n U : ℕ) (σ : State) (hn : σ.loc 1 = n) (hU : σ.loc 2 = U)
    (hnn : σ.loc 3 = ((n * n : ℕ) : ℤ)) :
    (wrapOptArgs kk).map (·.val σ) =
      [(n : ℤ), (U : ℤ), ((1 : ℕ) : ℤ), ((1 + kk * kk * n * n : ℕ) : ℤ)] ++
        [((1 + kk * kk * n * n + kk : ℕ) : ℤ)] := by
  simp only [wrapOptArgs, List.map_cons, List.map_nil, Expr.val, Op.eval, hn, hU, hnn]
  simp
  constructor <;> ring

/-- The arguments stay within the limits. -/
theorem wrapOpt_safe (kk n : ℕ) (lim : Limits) (σ : State) (hnn : σ.loc 3 = ((n * n : ℕ) : ℤ))
    (hw : (((kk * kk + kk + 1) * (n * n + 1) : ℕ) : ℤ) ≤ lim.word) :
    ∀ e ∈ wrapOptArgs kk, e.Safe lim σ := by
  rw [show (kk * kk + kk + 1) * (n * n + 1) =
    kk * kk * (n * n) + kk * (n * n) + kk * kk + kk + n * n + 1 by ring] at hw
  push_cast at hw hnn
  have : (0 : ℤ) ≤ (kk : ℤ) * kk * ((n : ℤ) * n) := by positivity
  have : (0 : ℤ) ≤ (kk : ℤ) * kk := by positivity
  have : (0 : ℤ) ≤ (n : ℤ) * n := by positivity
  have : (0 : ℤ) ≤ (kk : ℤ) * ((n : ℤ) * n) := by positivity
  simp [wrapOptArgs, hnn, abs_le]
  omega

/-- The free pointer is within what `Wrap` allows. -/
theorem wrapOpt_fr_le (kk n : ℕ) :
    1 + kk * kk * n * n + kk ≤ (kk * kk + kk + 1) * (n * n + 1) := by
  rw [show (kk * kk + kk + 1) * (n * n + 1) =
    kk * kk * n * n + kk * (n * n) + kk * kk + kk + n * n + 1 by ring]
  omega

/-- The instance of either task: the weights stand from cell 1 on, and the answer goes behind
them. -/
def optInst {kk n : ℕ} (w : Fin kk → Fin kk → Fin n → Fin n → ℤ) (U : ℕ) : KcFindInst kk :=
  ⟨⟨n, U, 1, upperGraph w⟩, 1 + kk * kk * n * n⟩

/-- The input meets the precondition of either task. -/
theorem pre_optClique {kk n U : ℕ} (w : Fin kk → Fin kk → Fin n → Fin n → ℤ)
    (hw : ∀ a ∈ kList w, a.natAbs ≤ U) (hn : 1 ≤ n) (hU : 1 ≤ U) :
    (optInst w U).Pre (memOf ((n : ℤ) :: kList w)) (1 + kk * kk * n * n + kk) where
  toPre := kcPre_input w hw hn hU (by omega)
  belowRes := le_rfl
  apart := Or.inl le_rfl

/-- The cells in which a solver of either task leaves the clique are the output cells. -/
theorem post_optClique {kk n : ℕ} (w : Fin kk → Fin kk → Fin n → Fin n → ℤ) {μ' : ℕ → ℤ}
    {c : Fin kk → Fin n} (hc : ∀ p : Fin kk, μ' (1 + kk * kk * n * n + p) = (c p).val)
    (p : Fin kk) : μ' (((n : ℤ) :: kList w).length + p) = (c p).val := by
  rw [List.length_cons, length_kList, Nat.add_comm _ 1]
  exact hc p

/-- A comparison of two cliques in the graph that the solver is told is a comparison of the weights
that the end statement sums. -/
theorem cliqueWeight_le_of_upperGraph {kk n : ℕ} (w : Fin kk → Fin kk → Fin n → Fin n → ℤ)
    {c c' : Fin kk → Fin n}
    (h : (upperGraph w).cliqueWeight c ≤ (upperGraph w).cliqueWeight c') :
    cliqueWeight w c ≤ cliqueWeight w c' := by
  rwa [cliqueWeight_upperGraph, cliqueWeight_upperGraph] at h

/-- What connects Max-Weight k-Clique in the layout of the end statement with the task.  The program
always accepts: the answer is in the output cells. -/
noncomputable def wrapMaxClique (kk : ℕ) : Wrap (MaxKClique kk) (maxKcTask kk) false where
  cst := kk * kk + kk + 1
  cst_pos := by omega
  args := wrapOptArgs kk
  inst x := optInst x.x.1 x.U
  fr x := 1 + kk * kk * x.n * x.n + kk
  size_eq _ := rfl
  bound_eq _ := rfl
  fr_pos x := by omega
  fr_le x := wrapOpt_fr_le kk x.n
  vals x σ hn hU hnn := wrapOpt_vals kk x.n x.U σ hn hU hnn
  safe x lim σ _ _ hnn hw := wrapOpt_safe kk x.n lim σ hnn hw
  zero x hn _ := absurd x.x.2 (by omega)
  pre x hn hU := pre_optClique x.x.1 x.bounded hn hU
  post x r μ' _ h :=
    let ⟨⟨c, hc, hbest⟩, _⟩ := h
    ⟨⟨fun _ => trivial, fun _ => rfl⟩, c, post_optClique x.x.1 hc,
      fun c' => cliqueWeight_le_of_upperGraph x.x.1 (hbest c')⟩

/-- What connects Min-Weight k-Clique in the layout of the end statement with the task.  The program
always accepts: the answer is in the output cells. -/
noncomputable def wrapMinClique (kk : ℕ) : Wrap (MinKClique kk) (minKcTask kk) false where
  cst := kk * kk + kk + 1
  cst_pos := by omega
  args := wrapOptArgs kk
  inst x := optInst x.x.1 x.U
  fr x := 1 + kk * kk * x.n * x.n + kk
  size_eq _ := rfl
  bound_eq _ := rfl
  fr_pos x := by omega
  fr_le x := wrapOpt_fr_le kk x.n
  vals x σ hn hU hnn := wrapOpt_vals kk x.n x.U σ hn hU hnn
  safe x lim σ _ _ hnn hw := wrapOpt_safe kk x.n lim σ hnn hw
  zero x hn _ := absurd x.x.2 (by omega)
  pre x hn hU := pre_optClique x.x.1 x.bounded hn hU
  post x r μ' _ h :=
    let ⟨⟨c, hc, hbest⟩, _⟩ := h
    ⟨⟨fun _ => trivial, fun _ => rfl⟩, c, post_optClique x.x.1 hc,
      fun c' => cliqueWeight_le_of_upperGraph x.x.1 (hbest c')⟩

/-! ## Corollary 39, minimum and maximum weight -/

/-- **Corollary 39, minimum and maximum weight, on the word RAM**, from the bound of Theorem 19 for
Exact Triangle for programs of the light language. -/
theorem corollary_39_min_max_of_theorem_19 (h19 : Claim.Theorem_19_explicit lightModel 0.00175 1) :
    Items.Corollary_39_min_max := by
  intro k hk
  have hclaim := minMaxClique_of_theorem_19_VW13 lightModel5 k hk h19
    claim_VW13_Theorem_3_3_max claim_minTriangleFromMax (claim_maxCliqueFromMaxTriangle hk)
    (claim_minCliqueFromMinTriangle hk)
  refine ⟨FromClaims.solvedInTime_of_one_le (Q := MinKClique k) (fun w => kList_zero w.1)
      fun κ hκ => ?_,
    FromClaims.solvedInTime_of_one_le (Q := MaxKClique k) (fun w => kList_zero w.1)
      fun κ hκ => ?_⟩
  · obtain ⟨⟨T, hT, C, hb⟩, -⟩ := hclaim κ (by exact_mod_cast hκ)
    exact FromClaims.solvedAt_of_realized T κ ((wrapMinClique k).realized hT) (C := C)
      (by simpa only [pow_zero, mul_one] using hb)
  · obtain ⟨-, ⟨T, hT, C, hb⟩⟩ := hclaim κ (by exact_mod_cast hκ)
    exact FromClaims.solvedAt_of_realized T κ ((wrapMaxClique k).realized hT) (C := C)
      (by simpa only [pow_zero, mul_one] using hb)

end Light.Sec5
