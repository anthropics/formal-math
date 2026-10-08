/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.TimeClaims.Sec3.Arithmetic

/-!
# Running-time claims of Section 3.1: Corollaries 15 and 16

All lemmas are about an arbitrary interpretation `M : DetTimeModel` of "is solved in time T".

* Corollary 15, first case, from Theorem 5 ("Apply Theorem 5 with N = n to the two biadjacency
  matrices"): `Corollary15.first_of_theorem_5`.
* Corollary 15, general case ("splitting W into sets of at most n²/√D query pairs"):
  `Corollary15.general_of_theorem_5`.  One call costs `O(n² log² D / D^{1/18})`, and all calls
  with the overhead cost `O((n² + |W| √D) log² D / D^{1/18})` (`dominated_calls`).
* Corollary 16 from Corollary 26 ("This is Corollary 26 with N = n"):
  `Corollary16.of_corollary_26`.

In each deduction the overheads `n D`, `|W|` and `1` of writing the matrices and copying the answers
are at most the bound of the corollary, because `n ≥ D^18`.  The bounds are added up by the calculus
of `Dominated` on the parameters `n`, `D`, `w`.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## The calculus on the parameters `n`, `D`, `w` -/

/-- The parameters of an instance of (#)Lop-AE-SparseTri: `n` and `D` as in Definition 13, and the
number `w` of query pairs. -/
structure LopSize where
  /-- The number of vertices of the two large parts. -/
  n : ℕ
  /-- The bound on the number of vertices of the middle part. -/
  D : ℕ
  /-- The number of query pairs. -/
  w : ℕ

/-- From the time `T` for the product of the two biadjacency matrices to the times for counting and
for detection (the claims `LopCountFromThinProduct` and `LopDetectFromCount`): if `T` and the
overheads `n D`, `w` and `1` are `O(g)`, so are the two times, with one constant. -/
private theorem exists_const_count_detect {dom : LopSize → Prop} {T g : LopSize → ℝ} (C₁ C₃ : ℝ)
    (hT : Dominated dom T g) (hnD : Dominated dom (fun p => (p.n : ℝ) * p.D) g)
    (hw : Dominated dom (fun p => (p.w : ℝ)) g) (hone : Dominated dom (fun _ => (1 : ℝ)) g)
    (hg : ∀ p, dom p → 0 ≤ g p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p, dom p → T p + C₁ * ((p.n : ℝ) * p.D + p.w + 1) ≤ C * g p ∧
      T p + C₁ * ((p.n : ℝ) * p.D + p.w + 1) + C₃ * ((p.w : ℝ) + 1) ≤ C * g p := by
  have hcount := hT.add (((hnD.add hw).add hone).const_mul_of_nonneg C₁ fun p _ => by positivity)
  exact hcount.exists_const_and
    (hcount.add ((hw.add hone).const_mul_of_nonneg C₃ fun p _ => by positivity)) hg hg

/-! ## Corollary 15, the first case -/

/-- The deduction of the first case of Corollary 15 from Theorem 5: "Apply Theorem 5 with
N = n to the two biadjacency matrices". -/
theorem Corollary15.first_of_theorem_5 (M : DetTimeModel) (h5 : Claim.Theorem_5 M)
    (hlop : Claim.LopCountFromThinProduct M) (hdet : Claim.LopDetectFromCount M) :
    Claim.Corollary_15_first M := by
  obtain ⟨C₁, hlop⟩ := hlop
  obtain ⟨C₃, hdet⟩ := hdet
  obtain ⟨C, T, hT, hb⟩ := h5 0
  obtain ⟨K, hK0, hK⟩ := exists_const_count_detect C₁ C₃
    (dom := fun p => (∃ k : ℕ, p.D = 4 ^ k) ∧ 4 ≤ p.D ∧ p.D ^ 18 ≤ p.n ∧
      (p.w : ℝ) ≤ (p.n : ℝ) ^ 2 / Real.sqrt p.D)
    (T := fun p => T p.n p.D p.w 1)
    (g := fun p => thinBound p.n p.D)
    (.of_exists_const ⟨C, fun p ⟨hk, hD, hDn, hw⟩ =>
      hb p.n p.D p.w 1 hk hD hDn hw (Real.rpow_zero _).ge⟩ fun p _ => by positivity)
    (.of_le fun p ⟨_, hD, hDn, _⟩ => mul_le_thinBound hD hDn)
    (.of_le fun p ⟨_, hD, _, hw⟩ => hw.trans (sq_div_sqrt_le_thinBound p.n hD))
    (.of_le fun p ⟨_, hD, hDn, _⟩ => one_le_thinBound hD hDn)
    fun p _ => by positivity
  exact ⟨K, _, _, hK0, hlop T hT, hdet _ (hlop T hT), fun n D w hk hD hDn hw =>
    hK ⟨n, D, w⟩ ⟨hk, hD, hDn, hw⟩⟩

/-! ## Corollary 15, the general case -/

/-- "For larger W, apply the theorem to each of at most [...] pieces": if one call costs
`O(n² log² D / D^{1/18})`, then all calls cost `O((n² + w √D) log² D / D^{1/18})`. -/
private theorem dominated_calls {dom : LopSize → Prop} {call : LopSize → ℝ}
    (hdom : ∀ p, dom p → 1 ≤ p.D ∧ 1 ≤ p.n)
    (hcall : Dominated dom call fun p => thinBound p.n p.D) :
    Dominated dom (fun p => (⌈(p.w : ℝ) / (splitCap p.n p.D : ℝ)⌉₊ : ℝ) * call p)
      fun p => splitBound p.n p.D p.w := by
  have hnumber : Dominated dom (fun p => (⌈(p.w : ℝ) / (splitCap p.n p.D : ℝ)⌉₊ : ℝ)) fun p =>
      ((p.n : ℝ) ^ 2 + (p.w : ℝ) * Real.sqrt p.D) / (p.n : ℝ) ^ 2 :=
    .of_le_const_mul zero_le_two fun p hp => ceil_div_splitCap_le p.w (hdom p hp).1 (hdom p hp).2
  refine ((hcall.mul_left fun p _ => Nat.cast_nonneg _).trans
    (hnumber.mul_right fun p _ => by positivity)).congr (fun _ _ => rfl) fun p hp => ?_
  have hn0 : (p.n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.one_le_iff_ne_zero.1 (hdom p hp).2)
  rw [thinBound, splitBound]
  field_simp

/-- The deduction of the general case of Corollary 15 from Theorem 5: "For larger W, apply
the theorem to each of at most [...] pieces." -/
theorem Corollary15.general_of_theorem_5 (M : DetTimeModel) (h5 : Claim.Theorem_5 M)
    (hlop : Claim.LopCountFromThinProduct M) (hsplit : Claim.LopSplit M)
    (hdet : Claim.LopDetectFromCount M) : Claim.Corollary_15_general M := by
  obtain ⟨C₁, hlop⟩ := hlop
  obtain ⟨C₂, hsplit⟩ := hsplit
  obtain ⟨C₃, hdet⟩ := hdet
  obtain ⟨C, T, hT, hb⟩ := h5 0
  have hcount := hsplit _ (hlop T hT)
  set dom : LopSize → Prop := fun p => (∃ k : ℕ, p.D = 4 ^ k) ∧ 4 ≤ p.D ∧ p.D ^ 18 ≤ p.n
  -- The parts of one call, on a piece of `splitCap n D ≤ n² / √D` query pairs.
  have hproduct : Dominated dom (fun p => T p.n p.D (splitCap p.n p.D) 1) fun p =>
      thinBound p.n p.D :=
    .of_exists_const ⟨C, fun p ⟨hk, hD, hDn⟩ => hb p.n p.D _ 1 hk hD hDn
      (splitCap_le (by omega) hDn) (Real.rpow_zero _).ge⟩ fun p _ => by positivity
  have hnD : Dominated dom (fun p => (p.n : ℝ) * p.D) fun p => thinBound p.n p.D :=
    .of_le fun p ⟨_, hD, hDn⟩ => mul_le_thinBound hD hDn
  have hcap : Dominated dom (fun p => (splitCap p.n p.D : ℝ)) fun p => thinBound p.n p.D :=
    .of_le fun p ⟨_, hD, hDn⟩ =>
      (splitCap_le (by omega) hDn).trans (sq_div_sqrt_le_thinBound p.n hD)
  have hone : Dominated dom (fun _ => (1 : ℝ)) fun p => thinBound p.n p.D :=
    .of_le fun p ⟨_, hD, hDn⟩ => one_le_thinBound hD hDn
  -- All calls, and the overhead `w + 1`.
  have hcalls := dominated_calls
    (fun p ⟨_, hD, hDn⟩ => ⟨by omega, (Nat.one_le_pow _ _ (by omega)).trans hDn⟩)
    ((hproduct.add (((hnD.add hcap).add hone).const_mul_of_nonneg C₁ fun p _ => by positivity)).add
      ((hnD.add hone).const_mul_of_nonneg C₂ fun p _ => by positivity))
  have hover : Dominated dom (fun p => (p.w : ℝ) + 1) fun p => splitBound p.n p.D p.w :=
    .of_le fun p ⟨_, hD, hDn⟩ => add_one_le_splitBound p.w hD hDn
  have htotal := hcalls.add (hover.const_mul_of_nonneg C₂ fun p _ => by positivity)
  obtain ⟨K, hK0, hK⟩ := htotal.exists_const_and
    (htotal.add (hover.const_mul_of_nonneg C₃ fun p _ => by positivity))
    (fun p _ => by positivity) fun p _ => by positivity
  exact ⟨K, _, _, hK0, hcount, hdet _ hcount, fun n D w hk hD hDn => hK ⟨n, D, w⟩ ⟨hk, hD, hDn⟩⟩

/-! ## Corollary 16 -/

/-- The deduction of Corollary 16 from Corollary 26: "This is Corollary 26 with N = n,
applied to the two biadjacency matrices as above." -/
theorem Corollary16.of_corollary_26 (M : DetTimeModel)
    (h26 : Claim.Corollary_26_wanted M) (hlop : Claim.LopCountFromThinProduct M)
    (hdet : Claim.LopDetectFromCount M) : Claim.Corollary_16 M := by
  obtain ⟨C₁, hlop⟩ := hlop
  obtain ⟨C₃, hdet⟩ := hdet
  obtain ⟨C, T, hT, hb⟩ := h26 0
  obtain ⟨K, hK0, hK⟩ := exists_const_count_detect C₁ C₃
    (dom := fun p => 1 ≤ p.D ∧ p.D ^ 18 ≤ p.n) (T := fun p => T p.n p.D p.w 1)
    (g := fun p => wantedBound p.n p.D p.w)
    (.of_exists_const ⟨C, fun p ⟨hD, hDn⟩ => hb p.n p.D p.w 1 hD hDn (Real.rpow_zero _).ge⟩
      fun p _ => by positivity)
    (.of_le fun p ⟨hD, hDn⟩ => (mul_le_sq_div_rpow hD hDn (by norm_num)).trans
      (sq_div_rpow_le_wantedBound p.n p.D p.w))
    (.of_le fun p ⟨hD, _⟩ => (le_mul_of_one_le_right p.w.cast_nonneg
      (Real.one_le_rpow (Nat.one_le_cast.2 hD) (by norm_num))).trans
        (le_add_of_nonneg_right (by positivity)))
    (.of_le fun p ⟨hD, hDn⟩ => one_le_wantedBound hD hDn p.w)
    fun p _ => by positivity
  exact ⟨K, _, _, hK0, hlop T hT, hdet _ (hlop T hT), fun n D w hD hDn => hK ⟨n, D, w⟩ ⟨hD, hDn⟩⟩

end ThreeSumApsp
