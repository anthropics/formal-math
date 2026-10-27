/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Interfaces
public import PaddedDescent.F.RebalF
public import StepMachines.Math.CodeSeq
public import Groundwork.Net.Net

/-! # A network evaluated by enumeration of its labels

Replacing every Ψ_jj' by its factorization gives Z_ι = Σ_θ ∏_j Σ_{z_j} W_j(z_j) ∏_{j' ≠ j}
f_jj'(z_j, θ_jj'), where θ consists of one string
θ_jj' = θ_j'j for each pair. `value_eq_sum_labels` is this identity for any network. `stEnum` says
that the function `enumF`, which runs through all θ written as one
word of U/2 bits, returns the value of the network N that the functions of `F` (its tables W and f
and the lengths n and cap) present, if the pad is at least as long as the number of these words and
as the number of
states of every node. -/

public section

namespace ClauseBound.Alg.Enum

open Finset Groundwork Groundwork.Prog PaddedDescent.F

/-! ### The identity -/

section identity

variable {J σ τ : Type} [Fintype J] [LinearOrder J]

/-- The value of a network is the sum, over all choices t of a label for every pair, of the product
over the nodes a of Σ_z W_a(z) ∏_{b ≠ a} f_ab(z, t_ab). -/
theorem value_eq_sum_labels (N : Network J σ τ) (t₀ : τ) :
    N.value = ∑ t ∈ tuples (fun p : J × J => p.1 < p.2) (fun p => N.lab p.1 p.2) t₀,
      ∏ a, ∑ z ∈ N.S a, N.W a z * ∏ b ∈ univ.erase a, N.f a b z (t (pr a b)) := by
  unfold Network.value
  have h1 : ∀ z : J → σ, ∏ p ∈ pairs J, N.Ψ p.1 p.2 (z p.1) (z p.2) =
      ∑ t ∈ tuples (fun p : J × J => p.1 < p.2) (fun p => N.lab p.1 p.2) t₀,
        ∏ p ∈ pairs J, N.f p.1 p.2 (z p.1) (t p) * N.f p.2 p.1 (z p.2) (t p) := fun z =>
    (sum_tuples_prod (fun p : J × J => p.1 < p.2) (fun p => N.lab p.1 p.2) t₀
      fun p θ => N.f p.1 p.2 (z p.1) θ * N.f p.2 p.1 (z p.2) θ).symm
  simp_rw [h1, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  rw [prod_univ_sum]
  refine sum_congr rfl fun z _ => ?_
  rw [prod_mul_distrib (s := univ), prod_erase_eq_pairs fun a b => N.f a b (z a) (t (pr a b))]
  congr 1
  refine prod_congr rfl fun p hp => ?_
  have h := pr_of_lt (mem_filter.1 hp).2
  rw [h.1, h.2]

/-- A sum over ordered pairs of distinct nodes, regrouped by unordered pairs. -/
theorem sum_erase_eq_pairs (G : J → J → ℕ) :
    ∑ a, ∑ b ∈ univ.erase a, G a b = ∑ p ∈ pairs J, (G p.1 p.2 + G p.2 p.1) := by
  rw [← sum_finset_product' (univ.filter fun p : J × J => p.1 ≠ p.2) univ (fun a => univ.erase a)
    (by intro p; simp [eq_comm])]
  rw [sum_add_distrib]
  have h1 : ∑ p ∈ pairs J, G p.2 p.1 = ∑ p ∈ univ.filter (fun p : J × J => p.2 < p.1), G p.1 p.2 :=
    sum_nbij' Prod.swap Prod.swap (by intro p; simp [pairs]) (by intro p; simp [pairs]) (by intro p; simp)
      (by intro p; simp) (by intro p; simp)
  rw [h1, pairs, ← sum_union]
  · congr 1; ext p; simp [lt_or_lt_iff_ne]
  · rw [disjoint_left]; intro p; simp; grind

end identity

/-! ### The place of the pair (a, b) in the word of all labels -/

section place

variable {g : ℕ}

/-- The number a·g + b of the pair (a, b). -/
def pos (p : Fin g × Fin g) : ℕ := p.1.val * g + p.2.val

theorem pos_div (p : Fin g × Fin g) : pos p / g = p.1.val := by
  have hg : 0 < g := p.1.pos
  rw [pos, Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt p.2.2, Nat.zero_add]

theorem pos_mod (p : Fin g × Fin g) : pos p % g = p.2.val := by
  rw [pos, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt p.2.2]

theorem pos_bijOn : Set.BijOn (pos (g := g)) {_p | True} (range (g * g)) := by
  refine ⟨fun p _ => ?_, fun p _ q _ h => ?_, fun j hj => ?_⟩
  · have h1 : (p.1.val + 1) * g ≤ g * g := Nat.mul_le_mul_right g p.1.2
    have h2 := p.2.2
    rw [Nat.succ_mul] at h1
    exact mem_coe.2 (mem_range.2 (by unfold pos; omega))
  · exact Prod.ext (Fin.ext (by rw [← pos_div p, h, pos_div])) (Fin.ext (by rw [← pos_mod p, h, pos_mod]))
  · have hj : j < g * g := mem_range.1 (mem_coe.1 hj)
    have hg : 0 < g := Nat.pos_of_ne_zero fun e => by simp [e] at hj
    exact ⟨(⟨j / g, Nat.div_lt_of_lt_mul hj⟩, ⟨j % g, Nat.mod_lt _ hg⟩), trivial, Nat.div_add_mod' j g⟩

/-- A sum over all numbers below g·g is a sum over all pairs. -/
theorem sum_range_eq_sum_pos (G : ℕ → ℕ) : ∑ j ∈ range (g * g), G j = ∑ p : Fin g × Fin g, G (pos p) :=
  (sum_nbij pos (fun p _ => pos_bijOn.mapsTo trivial) (fun p _ q _ h => pos_bijOn.injOn trivial trivial h)
    (fun j hj => by
      obtain ⟨p, _, e⟩ := pos_bijOn.surjOn hj
      exact ⟨p, mem_coe.2 (mem_univ p), e⟩) fun _ _ => rfl).symm

end place

/-! ### The function -/

section prog

variable {C : Type} {g : ℕ} {F : FNet C} {c : C} {N : Network (Fin g) (List Bool) (List Bool)}

theorem W_eq (hN : F.toP.Presents c N 0 0) (a : Fin g) (z : List Bool) (hz : z.length = F.n c a) :
    F.W (c, (a.val, z)) = N.W a z :=
  (RebalF.freeM_runs F.W _).unique (hN.W_runs a z hz)

theorem f_eq (hN : F.toP.Presents c N 0 0) (a b : Fin g) (z θ : List Bool) (hab : a ≠ b) (hz : z.length = F.n c a)
    (hθ : θ.length = F.cap c a b) : F.f (c, ((a.val, b.val), (z, θ))) = N.f a b z θ :=
  (RebalF.freeM_runs F.f _).unique (hN.f_runs a b z θ hab hz hθ)

/-- The two lengths given for the labels of a pair agree. -/
theorem cap_comm (hN : F.toP.Presents c N 0 0) (a b : Fin g) (hab : a ≠ b) : F.cap c a b = F.cap c b a := by
  have h : words (F.cap c a b) = words (F.cap c b a) := by
    rw [← show N.lab a b = words (F.cap c a b) from hN.lab_eq a b hab, N.lab_comm]
    exact hN.lab_eq b a hab.symm
  have h2 := congrArg card h
  rw [card_words, card_words] at h2
  exact Nat.pow_right_injective le_rfl h2

theorem enumLen_pos (p : Fin g × Fin g) : enumLen g F c (pos p) = if p.1 < p.2 then F.cap c p.1 p.2 else 0 := by
  rw [enumLen, pos_div, pos_mod]
  rfl

/-- The word of all labels has U/2 bits. -/
theorem two_mul_enumBits (hN : F.toP.Presents c N 0 0) : 2 * enumBits g F c = N.U := by
  rw [Network.U, sum_erase_eq_pairs, enumBits, sum_range_eq_sum_pos, pairs, sum_filter, mul_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [enumLen_pos]
  split_ifs with h
  · rw [hN.c_eq _ _ h.ne, hN.c_eq _ _ h.ne']
    have := cap_comm hN _ _ h.ne
    change 2 * F.cap c p.1 p.2 = F.cap c p.1 p.2 + F.cap c p.2 p.1
    omega
  · rfl

/-- The labels of all pairs are the tuples that have a word of the length of the chunk at every
place. -/
theorem tuples_eq (hN : F.toP.Presents c N 0 0) :
    tuples (fun p : Fin g × Fin g => p.1 < p.2) (fun p => N.lab p.1 p.2) [] =
      tuples (fun _ : Fin g × Fin g => True) (fun p => words (enumLen g F c (pos p))) [] := by
  unfold tuples
  congr 1
  funext p
  change (if p.1 < p.2 then N.lab p.1 p.2 else {[]}) = if True then words (enumLen g F c (pos p)) else {[]}
  rw [if_pos trivial, enumLen_pos]
  split_ifs with h
  · exact hN.lab_eq _ _ h.ne
  · ext w; simp

/-- A sum over all words of U/2 bits is a sum over these tuples: the entry at a place is the chunk
of that number. -/
theorem sum_words_eq (g : ℕ) (F : FNet C) (c : C) (G : (Fin g × Fin g → List Bool) → ℤ) :
    ∑ w ∈ words (enumBits g F c), G (fun p => chunkAt (enumLen g F c) (pos p) w) =
      ∑ t ∈ tuples (fun _ : Fin g × Fin g => True) (fun p => words (enumLen g F c (pos p))) [], G t := by
  have hD : ((words (enumBits g F c)).filter fun w => ∀ p : Fin g × Fin g, True →
      chunkAt (enumLen g F c) (pos p) w ∈ words (enumLen g F c (pos p))) = words (enumBits g F c) :=
    filter_true_of_mem fun w hw p _ =>
      mem_words.2 (length_chunkAt _ (mem_range.1 (mem_coe.1 (pos_bijOn.mapsTo trivial))) (mem_words.1 hw))
  have h := (Code.seq (fun _ : Fin g × Fin g => True) pos (g * g) pos_bijOn (enumLen g F c)
    (fun p => words (enumLen g F c (pos p))) (fun _ => id) (fun _ _ _ hw => mem_words.1 hw) (fun _ _ => Set.bijOn_id _) []).sum_dec G
  rw [← h]
  refine (sum_congr hD.symm fun w _ => congrArg G (funext fun p => ?_))
  change _ = if True then id (chunkAt (enumLen g F c) (pos p) w) else []
  rw [if_pos trivial]
  rfl

/-- The term of one choice t of labels, written with the functions W and f of `F`. -/
def term (F : FNet C) (c : C) (t : Fin g × Fin g → List Bool) : ℤ :=
  ∏ a : Fin g, ∑ z ∈ words (F.n c a), F.W (c, (a.val, z)) * ∏ b ∈ univ.erase a, F.f (c, ((a.val, b.val), (z, t (pr a b))))

theorem term_eq (hN : F.toP.Presents c N 0 0) (t : Fin g × Fin g → List Bool)
    (ht : t ∈ tuples (fun p : Fin g × Fin g => p.1 < p.2) (fun p => N.lab p.1 p.2) []) :
    ∏ a, ∑ z ∈ N.S a, N.W a z * ∏ b ∈ univ.erase a, N.f a b z (t (pr a b)) = term F c t := by
  unfold term
  refine prod_congr rfl fun a _ => ?_
  have hS : N.S a = words (F.n c a) := hN.S_eq a
  rw [hS]
  refine sum_congr rfl fun z hz => ?_
  rw [W_eq hN a z (mem_words.1 hz)]
  congr 1
  refine prod_congr rfl fun b hb => ?_
  have hab : a ≠ b := (ne_of_mem_erase hb).symm
  refine (f_eq hN a b z _ hab (mem_words.1 hz) ?_).symm
  rcases lt_or_gt_of_ne hab with h | h
  · have h1 := ((mem_tuples _ _ _ t).1 ht (a, b)).1 h
    rw [(pr_of_lt h).1]
    rw [show N.lab a b = words (F.cap c a b) from hN.lab_eq a b hab] at h1
    exact mem_words.1 h1
  · have h1 := ((mem_tuples _ _ _ t).1 ht (b, a)).1 h
    rw [(pr_of_lt h).2, cap_comm hN a b hab]
    rw [show N.lab b a = words (F.cap c b a) from hN.lab_eq b a hab.symm] at h1
    exact mem_words.1 h1

/-- With a long enough pad the function is the sum of the terms over all words of U/2 bits. -/
theorem enumF_eq (pad : U) (g : ℕ) (F : FNet C) (c : C) (hE : 2 ^ enumBits g F c ≤ pad.length)
    (hn : ∀ a < g, 2 ^ F.n c a ≤ pad.length) :
    enumF pad g F c = ∑ w ∈ words (enumBits g F c), term F c fun p : Fin g × Fin g => chunkAt (enumLen g F c) (pos p) w := by
  unfold enumF
  rw [sumF_eq hE, ← sum_toWord]
  refine sum_congr rfl fun y _ => ?_
  rw [prodL_eq, ← Fin.prod_univ_eq_prod_range]
  unfold term
  refine prod_congr rfl fun a _ => ?_
  rw [sumF_eq (hn a a.2), ← sum_toWord]
  refine sum_congr rfl fun zi _ => ?_
  congr 1
  rw [prodL_eq, ← Fin.prod_univ_eq_prod_range, ← prod_erase univ (a := a) (by simp)]
  refine prod_congr rfl fun b hb => ?_
  rw [if_neg fun e => ne_of_mem_erase hb (Fin.ext e)]
  simp only [pos, pr, Fin.coe_min, Fin.coe_max]

end prog

/-- The function `enumF` returns the value of the network, and the word of all labels has U/2 bits. -/
theorem stEnum : StEnum := by
  intro C pad g F c N hN hE hn
  refine ⟨?_, two_mul_enumBits hN⟩
  rw [value_eq_sum_labels N [], sum_congr rfl (term_eq hN), tuples_eq hN, ← sum_words_eq]
  exact enumF_eq pad g F c hE hn

end ClauseBound.Alg.Enum
