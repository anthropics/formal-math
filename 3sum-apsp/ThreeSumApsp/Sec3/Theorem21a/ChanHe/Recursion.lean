/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Collisions

/-!
# Theorem 21(a), the reduction of Chan and He: one node, and the recursion for three sets

This file proves that the reduction for three sets, `reduction n U`, is correct and makes
polylogarithmically many instances.  It follows the proof of [CH20, Theorem 5.1], one of the
reductions behind Theorem 21(a).  A node of the recursion tree consists of three sets and a
modulus `M`.

* One node.  The elements that are alone in their residue class modulo `M` are called light.  The
  first two arrays hold each light element of the first two sets at the index of its remainder.  The
  third array holds `-c`, for each light element `c` of the third set, at the remainder of `-c` and
  once more `M` cells further on.  All other cells hold padding.  Padding is too large to take part
  in a solution, and `a + b + c = 0` makes the remainders of `a` and `b` add up to that of `-c`, or
  to that plus `M`.  So the Convolution-3SUM instance of the node has a solution iff the light
  elements of the three sets have a 3SUM solution (`node_correct`).
* The recursion.  A 3SUM solution consists of three light elements, or one of its elements is heavy
  (`hasSol_split`).  The three children of a node replace one set each by its heavy elements.
* The depth.  A set that has been replaced `j` times has at most `n / d_j` elements, where `d₀ = 1`
  and `d_{j+1} = 2 d_j²` (`Replaced.heavy`).  Since `d_j > n` for `j = height n` (`lt_dSeq_height`),
  it is then empty (`Replaced.eq_empty`), so no node lies below the `fuel n` levels of the tree that
  are built.  This gives `nodes_correct`, by induction on the number of levels, and
  `reduction_correct`, whose hypotheses on the three sets are collected in `Admissible`.
* The size.  A ternary tree with `fuel n` levels has at most `3 ^ fuel n ≤ (2⌊log₂ n⌋ + 2)⁵` nodes
  (`length_reduction_le`).  The entries of the arrays are bounded in `abs_arrXY_le` and
  `abs_arrZ_le`, and the count for the searches of one node in `scan_node_le`.
-/

@[expose] public section

namespace ThreeSumApsp

namespace ChanHe

open Finset

/-! ## Light elements and the cells of the arrays -/

section cells

variable {S : Finset ℤ} {M U : ℕ}

/-- The elements of `S` that are alone in their residue class modulo `M`.  They play the role of
the good elements of [CH20]. -/
def light (S : Finset ℤ) (M : ℕ) : Finset ℤ := S \ heavy S M

/-- An element is light iff it collides with no other element. -/
private theorem mem_light {x : ℤ} : x ∈ light S M ↔ x ∈ S ∧ ∀ y ∈ S, y ≠ x → ¬ (M : ℤ) ∣ x - y := by
  simp only [light, heavy, mem_sdiff, mem_filter, not_and, not_exists]
  exact and_congr_right fun h => ⟨fun g => g h, fun g _ => g⟩

/-- Light elements are elements. -/
theorem light_subset (S : Finset ℤ) (M : ℕ) : light S M ⊆ S := sdiff_subset

/-- Heavy elements are elements. -/
theorem heavy_subset (S : Finset ℤ) (M : ℕ) : heavy S M ⊆ S := filter_subset _ _

/-- A subset of a bounded set is bounded. -/
theorem Bdd.mono {S T : Finset ℤ} (h : Bdd U S) (hT : T ⊆ S) : Bdd U T := fun x hx => h x (hT hx)

/-- The bucket of a light element contains nothing else. -/
private theorem bucket_of_light {x : ℤ} (hx : x ∈ light S M) : bucket S M (x % (M : ℤ)) = {x} := by
  obtain ⟨hxS, halone⟩ := mem_light.mp hx
  refine eq_singleton_iff_unique_mem.mpr ⟨mem_filter.mpr ⟨hxS, rfl⟩, fun y hy => ?_⟩
  obtain ⟨hyS, hmod⟩ := mem_filter.mp hy
  by_contra hne
  exact halone y hyS hne ((natCast_dvd_sub_iff_emod_eq M x y).mpr hmod.symm)

/-- A light element sits in the cell of its remainder. -/
private theorem arr_of_light {x : ℤ} (hx : x ∈ light S M) (pd : ℤ) {i : ℕ}
    (hi : (i : ℤ) = x % (M : ℤ)) : arr S M pd i = x := by
  rw [arr, hi, bucket_of_light hx, card_singleton, if_pos rfl, sum_singleton]

/-- A cell of the array holds a light element or padding. -/
private theorem arr_mem_light_or_eq (S : Finset ℤ) (M : ℕ) (pd : ℤ) (i : ℕ) :
    arr S M pd i ∈ light S M ∨ arr S M pd i = pd := by
  unfold arr
  split_ifs with h
  · left
    obtain ⟨x, hx⟩ := card_eq_one.mp h
    have hmem : ∀ y, y ∈ bucket S M i ↔ y = x := fun y => by rw [hx, mem_singleton]
    obtain ⟨hxS, hxi⟩ := mem_filter.mp ((hmem x).mpr rfl)
    rw [hx, sum_singleton]
    refine mem_light.mpr ⟨hxS, fun y hy hne hd => hne ((hmem y).mp (mem_filter.mpr ⟨hy, ?_⟩))⟩
    rw [← hxi]
    exact ((natCast_dvd_sub_iff_emod_eq M x y).mp hd).symm
  · exact .inr rfl

/-- Negation preserves lightness. -/
private theorem neg_mem_light_neg (S : Finset ℤ) (M : ℕ) (c : ℤ) :
    -c ∈ light (S.image fun c => -c) M ↔ c ∈ light S M := by
  simp only [mem_light, mem_image, neg_inj, exists_eq_right, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, ne_eq, ← neg_sub', dvd_neg]

/-- A cell of the first or second array holds a light element or `pad U`. -/
private theorem arrXY_cases (M : ℕ) (h : Bdd U S) (i : ℕ) :
    (arrXY S M U i ∈ light S M ∧ |arrXY S M U i| ≤ U) ∨ arrXY S M U i = pad U :=
  (arr_mem_light_or_eq S M (pad U) i).imp_left fun hx => ⟨hx, h _ (light_subset S M hx)⟩

/-- A cell of the third array holds `-c` for a light element `c`, or `-pad U`. -/
private theorem arrZ_cases (M : ℕ) (h : Bdd U S) (k : ℕ) :
    (∃ c ∈ light S M, |c| ≤ U ∧ arrZ S M U k = -c) ∨ arrZ S M U k = -pad U := by
  unfold arrZ
  split_ifs with hk
  · refine (arr_mem_light_or_eq (S.image fun c => -c) M (-pad U) (k % M)).imp_left fun hx => ?_
    rw [← neg_neg (arr _ _ _ _), neg_mem_light_neg] at hx
    exact ⟨_, hx, h _ (light_subset S M hx), (neg_neg _).symm⟩
  · exact .inr rfl

/-- For a light element `c`, the third array holds `-c` in the two cells below `2M` whose index is
congruent to `-c`. -/
private theorem arrZ_of_light {c : ℤ} (hc : c ∈ light S M) (U : ℕ) {k : ℕ} (hk : k < 2 * M)
    (hkc : ((k % M : ℕ) : ℤ) = -c % (M : ℤ)) : arrZ S M U k = -c := by
  rw [arrZ, if_pos hk]
  exact arr_of_light ((neg_mem_light_neg S M c).mpr hc) _ hkc

/-- The padding value has absolute value `2U + 1`. -/
private theorem abs_pad (U : ℕ) : |pad U| = 2 * (U : ℤ) + 1 :=
  abs_of_nonneg (by unfold pad; positivity)

/-- The entries of the array made from the first or the second set of a node have absolute value at
most `2U + 1`. -/
theorem abs_arrXY_le (M : ℕ) (h : Bdd U S) (i : ℕ) : |arrXY S M U i| ≤ 2 * (U : ℤ) + 1 := by
  rcases arrXY_cases M h i with ⟨-, hb⟩ | he
  · exact hb.trans (by omega)
  · rw [he, abs_pad]

/-- The entries of the third array of a node have absolute value at most `2U + 1`. -/
theorem abs_arrZ_le (M : ℕ) (h : Bdd U S) (k : ℕ) : |arrZ S M U k| ≤ 2 * (U : ℤ) + 1 := by
  rcases arrZ_cases M h k with ⟨c, -, hb, he⟩ | he
  · rw [he, abs_neg]
    exact hb.trans (by omega)
  · rw [he, abs_neg, abs_pad]

end cells

/-! ## One node -/

/-- **Correctness of one node.**  Its Convolution-3SUM instance, read at any length `N ≥ 2M`, has a
solution iff the light elements of the three sets have a 3SUM solution. -/
theorem node_correct {U M N : ℕ} (hM : 1 ≤ M) (hN : 2 * M ≤ N) {S₁ S₂ S₃ : Finset ℤ}
    (h₁ : Bdd U S₁) (h₂ : Bdd U S₂) (h₃ : Bdd U S₃) :
    ConvSol N (arrXY S₁ M U) (arrXY S₂ M U) (arrZ S₃ M U) ↔
      HasSol (light S₁ M) (light S₂ M) (light S₃ M) := by
  constructor
  · rintro ⟨i, j, -, heq⟩
    rcases arrXY_cases M h₁ i with ⟨ha, ha'⟩ | ha <;>
      rcases arrXY_cases M h₂ j with ⟨hb, hb'⟩ | hb <;>
      rcases arrZ_cases M h₃ (i + j) with ⟨c, hc, hc', hz⟩ | hz
    · exact ⟨_, ha, _, hb, c, hc, by rw [heq, hz]; ring⟩
    -- in all other cases a cell holds `±(2U + 1)`, which the other two cells cannot balance
    all_goals
      simp only [pad, abs_le] at *
      omega
  · rintro ⟨a, ha, b, hb, c, hc, hsum⟩
    have hM0 : (M : ℤ) ≠ 0 := by omega
    obtain ⟨i, hi⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg a hM0)
    obtain ⟨j, hj⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg b hM0)
    have hiM := Int.emod_lt_of_pos a (by omega : (0 : ℤ) < M)
    have hjM := Int.emod_lt_of_pos b (by omega : (0 : ℤ) < M)
    have hij : (((i + j) % M : ℕ) : ℤ) = -c % (M : ℤ) := by
      push_cast
      rw [← hi, ← hj, ← Int.add_emod]
      congr 1
      omega
    refine ⟨i, j, by omega, ?_⟩
    rw [arrXY, arr_of_light ha _ hi.symm, arrXY, arr_of_light hb _ hj.symm,
      arrZ_of_light hc U (by omega) hij]
    omega

/-! ## The sizes of the sets along the recursion -/

/-- The sequence `d₀ = 1`, `d_{j+1} = 2 d_j²` of [CH20], in closed form. -/
def dSeq (j : ℕ) : ℕ := 2 ^ (2 ^ j - 1)

/-- The recurrence `d_{j+1} = 2 d_j²`. -/
private theorem dSeq_succ (j : ℕ) : dSeq (j + 1) = 2 * dSeq j ^ 2 := by
  have hexp : 2 ^ (j + 1) - 1 = 1 + (2 ^ j - 1) * 2 := by
    have := Nat.one_le_two_pow (n := j)
    rw [pow_succ]
    omega
  rw [dSeq, dSeq, hexp, pow_add, pow_mul, pow_one]

/-- The sequence `dSeq` is nondecreasing. -/
private theorem dSeq_mono {i j : ℕ} (h : i ≤ j) : dSeq i ≤ dSeq j :=
  Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) h) 1)

/-- `d_h > n` at `h = height n`. -/
private theorem lt_dSeq_height (n : ℕ) : n < dSeq (height n) := by
  have hclog : Nat.log 2 n + 2 ≤ 2 ^ height n := Nat.le_pow_clog (by norm_num) _
  calc n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
    _ ≤ dSeq (height n) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `height n` is at least 1, so the subtraction in `fuel` does not truncate. -/
theorem height_pos (n : ℕ) : 1 ≤ height n :=
  Nat.clog_pos (b := 2) (n := Nat.log 2 n + 2) (by norm_num) (by omega)

/-- `2^(height n) ≤ 2⌊log₂ n⌋ + 2`. -/
private theorem two_pow_height_le (n : ℕ) : 2 ^ height n ≤ 2 * Nat.log 2 n + 2 := by
  have hlt : 2 ^ (height n - 1) < Nat.log 2 n + 2 :=
    Nat.pow_pred_clog_lt_self (b := 2) (x := Nat.log 2 n + 2) (by norm_num) (by omega)
  rw [← Nat.sub_add_cancel (height_pos n), pow_succ]
  omega

/-- What is known about a set `T` that has been replaced `j` times by its heavy elements: its
elements have absolute value at most `U`, and there are at most `n / d_j` of them. -/
structure Replaced (n U j : ℕ) (T : Finset ℤ) : Prop where
  /-- The elements have absolute value at most `U`. -/
  bdd : Bdd U T
  /-- There are at most `n / d_j` elements. -/
  card : #T * dSeq j ≤ n

namespace Replaced

variable {n U j : ℕ} {T : Finset ℤ}

/-- At the root no set has been replaced. -/
theorem zero (hb : Bdd U T) (hc : #T ≤ n) : Replaced n U 0 T :=
  ⟨hb, by rwa [dSeq, pow_zero, Nat.sub_self, pow_zero, mul_one]⟩

/-- One more replacement: if at most `|T|²/(2n)` elements of `T` are heavy, then these are at most
`n / d_{j+1}`. -/
theorem heavy (h : Replaced n U j T) (hn : 1 ≤ n) {M : ℕ}
    (hM : 2 * n * #(ChanHe.heavy T M) ≤ #T ^ 2) : Replaced n U (j + 1) (ChanHe.heavy T M) := by
  refine ⟨h.bdd.mono (heavy_subset T M), Nat.le_of_mul_le_mul_left ?_ hn⟩
  calc n * (#(ChanHe.heavy T M) * dSeq (j + 1))
      = 2 * n * #(ChanHe.heavy T M) * dSeq j ^ 2 := by rw [dSeq_succ]; ring
    _ ≤ #T ^ 2 * dSeq j ^ 2 := Nat.mul_le_mul_right _ hM
    _ = #T * dSeq j * (#T * dSeq j) := by ring
    _ ≤ n * n := Nat.mul_le_mul h.card h.card

/-- After `height n` replacements a set is empty. -/
theorem eq_empty (h : Replaced n U j T) (hj : height n ≤ j) : T = ∅ := by
  by_contra hne
  have hcard : 1 ≤ #T := card_pos.mpr (nonempty_iff_ne_empty.mpr hne)
  -- `n < d_{height n} ≤ d_j ≤ |T| d_j ≤ n`
  have := lt_dSeq_height n
  have := dSeq_mono hj
  have := Nat.mul_le_mul_right (dSeq j) hcard
  have := h.card
  omega

end Replaced

/-- After `3 (height n) - 2` replacements in all, one of the three sets is empty. -/
private theorem exists_eq_empty {n U j₁ j₂ j₃ : ℕ} {T₁ T₂ T₃ : Finset ℤ} (r₁ : Replaced n U j₁ T₁)
    (r₂ : Replaced n U j₂ T₂) (r₃ : Replaced n U j₃ T₃) (hj : 3 * height n - 2 ≤ j₁ + j₂ + j₃) :
    T₁ = ∅ ∨ T₂ = ∅ ∨ T₃ = ∅ := by
  have := height_pos n
  rcases (by omega : height n ≤ j₁ ∨ height n ≤ j₂ ∨ height n ≤ j₃) with h | h | h
  · exact .inl (r₁.eq_empty h)
  · exact .inr (.inl (r₂.eq_empty h))
  · exact .inr (.inr (r₃.eq_empty h))

/-! ## The recursion tree -/

/-- A solution stays a solution when the sets grow. -/
theorem HasSol.mono {S₁ S₂ S₃ T₁ T₂ T₃ : Finset ℤ} (h : HasSol S₁ S₂ S₃) (h₁ : S₁ ⊆ T₁)
    (h₂ : S₂ ⊆ T₂) (h₃ : S₃ ⊆ T₃) : HasSol T₁ T₂ T₃ :=
  let ⟨a, ha, b, hb, c, hc, hs⟩ := h
  ⟨a, h₁ ha, b, h₂ hb, c, h₃ hc, hs⟩

/-- If one of the three sets is empty there is no solution. -/
private theorem not_hasSol_of_empty {S₁ S₂ S₃ : Finset ℤ} (h : S₁ = ∅ ∨ S₂ = ∅ ∨ S₃ = ∅) :
    ¬ HasSol S₁ S₂ S₃ := by
  rintro ⟨a, ha, b, hb, c, hc, -⟩
  rcases h with rfl | rfl | rfl <;> simp_all

/-- A solution consists of three light elements, or it contains a heavy one.  The brackets are those
of the list of the children in `nodes`. -/
theorem hasSol_split (S₁ S₂ S₃ : Finset ℤ) (M : ℕ) :
    HasSol S₁ S₂ S₃ ↔ HasSol (light S₁ M) (light S₂ M) (light S₃ M) ∨
      (HasSol (heavy S₁ M) S₂ S₃ ∨ HasSol S₁ (heavy S₂ M) S₃) ∨ HasSol S₁ S₂ (heavy S₃ M) := by
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, hs⟩
    by_contra hno
    simp only [not_or] at hno
    obtain ⟨hlight, ⟨hheavy₁, hheavy₂⟩, hheavy₃⟩ := hno
    exact hlight ⟨a, mem_sdiff.mpr ⟨ha, fun h => hheavy₁ ⟨a, h, b, hb, c, hc, hs⟩⟩,
      b, mem_sdiff.mpr ⟨hb, fun h => hheavy₂ ⟨a, ha, b, h, c, hc, hs⟩⟩,
      c, mem_sdiff.mpr ⟨hc, fun h => hheavy₃ ⟨a, ha, b, hb, c, h, hs⟩⟩, hs⟩
  · rintro (h | (h | h) | h)
    · exact h.mono (light_subset _ _) (light_subset _ _) (light_subset _ _)
    · exact h.mono (heavy_subset _ _) Subset.rfl Subset.rfl
    · exact h.mono Subset.rfl (heavy_subset _ _) Subset.rfl
    · exact h.mono Subset.rfl Subset.rfl (heavy_subset _ _)

/-- The first `f` levels of the tree have at most `(3^f - 1)/2` nodes. -/
theorem length_nodes_le (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    2 * (nodes Q Λ f S₁ S₂ S₃).length + 1 ≤ 3 ^ f := by
  induction f generalizing S₁ S₂ S₃ with
  | zero => simp [nodes]
  | succ f ih =>
    unfold nodes
    split_ifs with h
    · exact Nat.one_le_pow _ _ (by norm_num)
    · simp only [List.length_cons, List.length_append]
      have := ih (heavy S₁ (modulus Q Λ S₁ S₂ S₃)) S₂ S₃
      have := ih S₁ (heavy S₂ (modulus Q Λ S₁ S₂ S₃)) S₃
      have := ih S₁ S₂ (heavy S₃ (modulus Q Λ S₁ S₂ S₃))
      rw [pow_succ]
      omega

/-- The sets of a node are subsets of the sets at the root. -/
theorem nodes_subset (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    ∀ ν ∈ nodes Q Λ f S₁ S₂ S₃, ν.S₁ ⊆ S₁ ∧ ν.S₂ ⊆ S₂ ∧ ν.S₃ ⊆ S₃ := by
  induction f generalizing S₁ S₂ S₃ with
  | zero => simp [nodes]
  | succ f ih =>
    intro ν hν
    unfold nodes at hν
    split_ifs at hν with he
    · simp at hν
    · simp only [List.mem_cons, List.mem_append] at hν
      rcases hν with rfl | (hν | hν) | hν
      · exact ⟨Subset.rfl, Subset.rfl, Subset.rfl⟩
      · obtain ⟨s₁, s₂, s₃⟩ := ih _ _ _ ν hν
        exact ⟨s₁.trans (heavy_subset _ _), s₂, s₃⟩
      · obtain ⟨s₁, s₂, s₃⟩ := ih _ _ _ ν hν
        exact ⟨s₁, s₂.trans (heavy_subset _ _), s₃⟩
      · obtain ⟨s₁, s₂, s₃⟩ := ih _ _ _ ν hν
        exact ⟨s₁, s₂, s₃.trans (heavy_subset _ _)⟩

/-- The hypotheses on the set `Q` of candidates for the two searches: primes, all at most `m`, and
enough of them for `card_heavy_modulus_le`. -/
structure Candidates (n U m : ℕ) (Q : Finset ℕ) : Prop where
  /-- The candidates are primes. -/
  prime : ∀ p ∈ Q, p.Prime
  /-- The candidates are at most `m`. -/
  le : ∀ p ∈ Q, p ≤ m
  /-- There are at least `√(18n) Λ` candidates. -/
  card : 18 * Lam U ^ 2 * n ≤ #Q ^ 2

/-- The primes up to `mPar n U`, among which `reduction n U` searches, meet the hypotheses. -/
private theorem candidates_primesLE (n U : ℕ) :
    Candidates n U (mPar n U) (Nat.primesLE (mPar n U)) :=
  ⟨fun _ => Nat.prime_of_mem_primesLE, fun _ => Nat.le_of_mem_primesLE,
    le_card_primesLE_mPar_sq n U⟩

/-- The induction behind `reduction_correct`.  If the `i`-th set has been replaced `j_i` times, then
`f` levels of the tree are enough as soon as `f + j₁ + j₂ + j₃ ≥ 3 (height n) - 2`. -/
theorem nodes_correct {n U N m : ℕ} (hn : 1 ≤ n) {Q : Finset ℕ} (hQ : Candidates n U m Q)
    (hN : 2 * m ^ 2 ≤ N) (f : ℕ) {T₁ T₂ T₃ : Finset ℤ} {j₁ j₂ j₃ : ℕ} (r₁ : Replaced n U j₁ T₁)
    (r₂ : Replaced n U j₂ T₂) (r₃ : Replaced n U j₃ T₃)
    (hf : 3 * height n - 2 ≤ f + j₁ + j₂ + j₃) :
    HasSol T₁ T₂ T₃ ↔ ∃ ν ∈ nodes Q (Lam U) f T₁ T₂ T₃, ν.Conv U N := by
  induction f generalizing T₁ T₂ T₃ j₁ j₂ j₃ with
  | zero => simp [nodes, not_hasSol_of_empty (exists_eq_empty r₁ r₂ r₃ (by omega))]
  | succ f ih =>
    unfold nodes
    split_ifs with he
    · simp [not_hasSol_of_empty he]
    obtain ⟨hM1, hMm⟩ := modulus_bounds (nonempty_of_le_card_sq hQ.card hn) hQ.prime hQ.le
      r₁.bdd r₂.bdd r₃.bdd
    have hheavy := card_heavy_modulus_le hQ.prime hQ.card hn r₁.bdd r₂.bdd r₃.bdd
    generalize modulus Q (Lam U) T₁ T₂ T₃ = M at hM1 hMm hheavy ⊢
    -- the node itself treats the light elements, and its three children the heavy ones
    have hnode := node_correct (N := N) hM1 (by omega) r₁.bdd r₂.bdd r₃.bdd
    have hchild₁ := ih (r₁.heavy hn (hheavy T₁ (by simp))) r₂ r₃ (by omega)
    have hchild₂ := ih r₁ (r₂.heavy hn (hheavy T₂ (by simp))) r₃ (by omega)
    have hchild₃ := ih r₁ r₂ (r₃.heavy hn (hheavy T₃ (by simp))) (by omega)
    rw [hasSol_split T₁ T₂ T₃ M, ← hnode, hchild₁, hchild₂, hchild₃]
    simp only [List.mem_cons, List.mem_append, or_and_right, exists_or, exists_eq_left]
    -- `Node.Conv` of the new node is by definition the instance of `node_correct`
    rfl

/-! ## The reduction for three sets -/

/-- The hypotheses on an input of `reduction n U`: each of the three sets has at most `n` elements,
all of absolute value at most `U`. -/
structure Admissible (n U : ℕ) (S₁ S₂ S₃ : Finset ℤ) : Prop where
  /-- The first set has at most `n` elements. -/
  card₁ : #S₁ ≤ n
  /-- The second set has at most `n` elements. -/
  card₂ : #S₂ ≤ n
  /-- The third set has at most `n` elements. -/
  card₃ : #S₃ ≤ n
  /-- The elements of the first set have absolute value at most `U`. -/
  bdd₁ : Bdd U S₁
  /-- The elements of the second set have absolute value at most `U`. -/
  bdd₂ : Bdd U S₂
  /-- The elements of the third set have absolute value at most `U`. -/
  bdd₃ : Bdd U S₃

/-- The sets of a node satisfy the hypotheses that the sets at the root satisfy. -/
theorem Admissible.of_mem {n U : ℕ} {S₁ S₂ S₃ : Finset ℤ} (h : Admissible n U S₁ S₂ S₃) {ν : Node}
    (hν : ν ∈ reduction n U S₁ S₂ S₃) : Admissible n U ν.S₁ ν.S₂ ν.S₃ :=
  let ⟨s₁, s₂, s₃⟩ := nodes_subset _ _ _ _ _ _ ν hν
  ⟨(card_le_card s₁).trans h.card₁, (card_le_card s₂).trans h.card₂,
    (card_le_card s₃).trans h.card₃, h.bdd₁.mono s₁, h.bdd₂.mono s₂, h.bdd₃.mono s₃⟩

/-- **Correctness of the reduction for three sets.**  Let the three sets have at most `n ≥ 1`
elements each, all of absolute value at most `U`, and let `N ≥ 2 * mPar n U ^ 2`.  Then 3SUM has a
solution iff the Convolution-3SUM instance of some node has one at length `N`. -/
theorem reduction_correct {n U N : ℕ} (hn : 1 ≤ n) (hN : 2 * mPar n U ^ 2 ≤ N)
    {S₁ S₂ S₃ : Finset ℤ} (h : Admissible n U S₁ S₂ S₃) :
    HasSol S₁ S₂ S₃ ↔ ∃ ν ∈ reduction n U S₁ S₂ S₃, ν.Conv U N :=
  nodes_correct hn (candidates_primesLE n U) hN (fuel n) (.zero h.bdd₁ h.card₁)
    (.zero h.bdd₂ h.card₂) (.zero h.bdd₃ h.card₃) le_rfl

/-- A ternary tree with `fuel n` levels has polylogarithmically many nodes. -/
theorem three_pow_fuel_le (n : ℕ) : 3 ^ fuel n ≤ (2 * Nat.log 2 n + 2) ^ 5 :=
  calc 3 ^ fuel n ≤ 3 ^ (3 * height n) := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    _ = 27 ^ height n := by rw [pow_mul]; norm_num
    _ ≤ 32 ^ height n := Nat.pow_le_pow_left (by norm_num) _
    _ = (2 ^ height n) ^ 5 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    _ ≤ (2 * Nat.log 2 n + 2) ^ 5 := Nat.pow_le_pow_left (two_pow_height_le n) 5

/-- **The reduction makes at most `(2⌊log₂ n⌋ + 2)⁵` nodes**, and each node is one instance. -/
theorem length_reduction_le (n U : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    (reduction n U S₁ S₂ S₃).length ≤ (2 * Nat.log 2 n + 2) ^ 5 := by
  have := length_nodes_le (Nat.primesLE (mPar n U)) (Lam U) (fuel n) S₁ S₂ S₃
  have := three_pow_fuel_le n
  unfold reduction
  omega

/-- The two searches of a node go through at most `m = mPar n U` primes each, and its three sets
have at most `3n` elements in all.  This bounds a number of pairs (candidate prime, element), not a
running time. -/
theorem scan_node_le {n U : ℕ} {ν : Node} (h : Admissible n U ν.S₁ ν.S₂ ν.S₃) :
    2 * #(Nat.primesLE (mPar n U)) * (#ν.S₁ + #ν.S₂ + #ν.S₃) ≤ 2 * mPar n U * (3 * n) := by
  have := h.card₁
  have := h.card₂
  have := h.card₃
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.card_primesLE_le _)) (by omega)

end ChanHe

end ThreeSumApsp
