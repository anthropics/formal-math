/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Defs
public import ClauseBound.Group.Grouping

/-! # Lemma 8 (Appendix A), case (ii): some grouping has exactly g/K nodes in every group and Y < (U + 2ζgP)/K²

The proof of Appendix A, sentence by sentence, by counting instead of probability. The sample space
is the set of all permutations e of the g = K·n nodes; the grouping that belongs to e is χ₀∘e,
where χ₀ is one fixed grouping with n nodes in every group. "With probability at most ε" reads "for
at most ε·(K·n)! permutations". The order of the file is that of the text: the random grouping
(`group_uniform`), Hoeffding's inequality (`hoeffding_sample`, `exp_le_inv`), the numbers c_a and U
(`cz`, `cs`, `tot`), the two kinds of events (`event_first_kind`, `event_second_kind`), the union
bound
(`card_events_lt`, `exists_no_event`), the display (`display_left`, `display_right`), and the claim
(`GeneralPieces.stCaseII`). -/

@[expose] public section

namespace GeneralPieces.Group

open Finset ClauseBound.Group ClauseBound.Group.Grouping

variable {K n : ℕ}

/-! ### The random grouping -/

/-- The group number γ of the grouping χ₀∘e, written out. -/
theorem cls_eq (e : Equiv.Perm (Fin (K * n))) (γ : Fin K) : cls e γ = ({a | chi0 (e a) = γ} : Finset (Fin (K * n))) := by
  ext a
  rw [mem_cls, mem_filter, and_iff_right (mem_univ a)]

/-- "Let χ be uniformly random among the groupings in which every group has exactly g/K nodes":
every grouping χ₀∘e has exactly n = g/K nodes in every group. -/
theorem card_group (e : Equiv.Perm (Fin (K * n))) (γ : Fin K) : #{a | chi0 (e a) = γ} = n := by rw [← cls_eq, card_cls]

/-- "Then each G_γ is a uniformly random set of g/K nodes": if at most the fraction ε of all sets of
n nodes have a property, then for at most the fraction ε of all permutations e the group γ of χ₀∘e
has it. -/
theorem group_uniform (γ : Fin K) (Q : Finset (Fin (K * n)) → Prop) [DecidablePred Q] (ε : ℝ)
    (hQ : (#{A ∈ powersetCard n (univ : Finset (Fin (K * n))) | Q A} : ℝ) ≤ ε * #(powersetCard n (univ : Finset (Fin (K * n))))) :
    (#{e : Equiv.Perm (Fin (K * n)) | Q (cls e γ)} : ℝ) ≤ ε * #(univ : Finset (Equiv.Perm (Fin (K * n)))) := by
  refine card_filter_le_of_fibers univ (fun e => cls e γ) (powersetCard n univ)
    (fun e _ => mem_powersetCard.2 ⟨subset_univ _, card_cls e γ⟩) (fun A' hA' A'' hA'' => ?_) Q ε hQ
  obtain ⟨p, -, hp⟩ := exists_perm_sets ∅ A' A'' (disjoint_empty_left _) (disjoint_empty_left _)
    (by rw [(mem_powersetCard.1 hA').2, (mem_powersetCard.1 hA'').2])
  exact fiber_le univ p (fun _ _ => mem_univ _) γ A' A'' hp

/-! ### Hoeffding's inequality for sampling without replacement -/

/-- "The sum S of a uniformly random set of j entries of a list of numbers in [0, R] satisfies Pr(S
≥ E S + ζjR) ≤ exp(−2jζ²)." Here E S is j times the mean of the list. The text cites this; the
proof is `ClauseBound.Group.card_sample_tail_le`. -/
theorem hoeffding_sample {ι : Type} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ) {R ζ : ℝ} (hR : 0 < R) (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ R)
    (hs : s.Nonempty) (j : ℕ) (hζ : 0 ≤ ζ) :
    (#{S ∈ powersetCard j s | j * ((∑ i ∈ s, x i) / #s) + ζ * j * R ≤ ∑ i ∈ S, x i} : ℝ) ≤ Real.exp (-(2 * j * ζ ^ 2)) * #(powersetCard j s) := by
  rw [card_powersetCard]
  exact card_sample_tail_le s x hR hx hs j hζ

/-- "Which for j = g/K is at most 1/(2gK)", because 2ζ²g ≥ K·ln(2gK). -/
theorem exp_le_inv (hK : 1 ≤ K) (hn : 1 ≤ n) {ζ : ℝ} (h : (K : ℝ) * Real.log (2 * ((K * n : ℕ) : ℝ) * K) ≤ 2 * ζ ^ 2 * ((K * n : ℕ) : ℝ)) :
    Real.exp (-(2 * n * ζ ^ 2)) ≤ 1 / (2 * ((K * n : ℕ) : ℝ) * K) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < 2 * ((K * n : ℕ) : ℝ) * K := by push_cast; positivity
  have h1 : Real.log (2 * ((K * n : ℕ) : ℝ) * K) ≤ 2 * n * ζ ^ 2 := by
    refine le_of_mul_le_mul_left (h.trans (le_of_eq ?_)) hK0
    push_cast; ring
  rw [one_div, ← Real.exp_log hpos, ← Real.exp_neg, Real.exp_le_exp]
  linarith

/-- Hoeffding's inequality for the sum of a list x of numbers in [0, R] over the group number γ: its
expectation is (Σ x)/K, and j = n. -/
theorem group_tail (hK : 1 ≤ K) (hn : 1 ≤ n) (x : Fin (K * n) → ℝ) {R ζ : ℝ} (hR : 0 < R) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ R) (hζ : 0 ≤ ζ) (γ : Fin K) :
    (#{e : Equiv.Perm (Fin (K * n)) | (∑ i, x i) / K + ζ * n * R ≤ ∑ i ∈ cls e γ, x i} : ℝ) ≤
      Real.exp (-(2 * n * ζ ^ 2)) * #(univ : Finset (Equiv.Perm (Fin (K * n)))) := by
  have : Nonempty (Fin (K * n)) := ⟨⟨0, Nat.mul_pos hK hn⟩⟩
  refine group_uniform γ (fun A => (∑ i, x i) / K + ζ * n * R ≤ ∑ i ∈ A, x i) _ ?_
  have w := hoeffding_sample univ x hR (fun i _ => hx i) univ_nonempty n hζ
  have e : (n : ℝ) * ((∑ i, x i) / #(univ : Finset (Fin (K * n)))) = (∑ i, x i) / K := by
    have hK0 : (K : ℝ) ≠ 0 := by positivity
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [card_univ, Fintype.card_fin]
    push_cast
    field_simp
  rwa [e] at w

/-! ### The numbers c_a and U -/

/-- "Let c_{a,a} = 0": the numbers c_{a,b} as reals, with 0 on the diagonal. -/
noncomputable def cz {g : ℕ} (c : Fin g → Fin g → ℕ) (a b : Fin g) : ℝ := if a = b then 0 else (c a b : ℝ)

/-- "c_a = Σ_{b ∈ [g]} c_{a,b}". -/
noncomputable def cs {g : ℕ} (c : Fin g → Fin g → ℕ) (a : Fin g) : ℝ := ∑ b, cz c a b

/-- "So that U = Σ_{a ∈ [g]} c_a". -/
noncomputable def tot {g : ℕ} (c : Fin g → Fin g → ℕ) : ℝ := ∑ a, cs c a

theorem cz_nonneg {g : ℕ} (c : Fin g → Fin g → ℕ) (a b : Fin g) : 0 ≤ cz c a b := by
  unfold cz; split_ifs
  · exact le_rfl
  · exact Nat.cast_nonneg _

theorem cs_nonneg {g : ℕ} (c : Fin g → Fin g → ℕ) (a : Fin g) : 0 ≤ cs c a := sum_nonneg fun b _ => cz_nonneg c a b

/-- c_a is the sum of c_{a,b} over the nodes b ≠ a. -/
theorem cs_eq {g : ℕ} (c : Fin g → Fin g → ℕ) (a : Fin g) : cs c a = ∑ b ∈ univ.erase a, (c a b : ℝ) := by
  rw [cs, ← sum_erase (univ : Finset (Fin g)) (a := a) (by simp [cz])]
  exact sum_congr rfl fun b hb => if_neg (ne_of_mem_erase hb).symm

/-- U is the sum of c_{a,b} over the ordered pairs of different nodes. -/
theorem tot_eq {g : ℕ} (c : Fin g → Fin g → ℕ) : tot c = ∑ a, ∑ b ∈ univ.erase a, (c a b : ℝ) := sum_congr rfl fun a _ => cs_eq c a

/-! ### The two kinds of events -/

/-- The event of the first kind, one for each group γ: "apply the inequality to Σ_{a ∈ G_γ} c_a,
with R = P and expectation U/K". The event Σ_{a ∈ G_γ} c_a ≥ (U + ζgP)/K has at most the
fraction exp(−2(g/K)ζ²) of all e. -/
theorem event_first_kind (hK : 1 ≤ K) (hn : 1 ≤ n) (c : Fin (K * n) → Fin (K * n) → ℕ) {P ζ : ℝ} (hζ : 0 ≤ ζ) (hP0 : 0 < P)
    (hP : ∀ a, cs c a ≤ P) (γ : Fin K) :
    (#{e : Equiv.Perm (Fin (K * n)) | (tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K ≤ ∑ a ∈ cls e γ, cs c a} : ℝ) ≤
      Real.exp (-(2 * n * ζ ^ 2)) * #(univ : Finset (Equiv.Perm (Fin (K * n)))) := by
  have w := group_tail hK hn (cs c) hP0 (fun a => ⟨cs_nonneg c a, hP a⟩) hζ γ
  have e : (tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K = (∑ a, cs c a) / K + ζ * n * P := by
    have hK0 : (K : ℝ) ≠ 0 := by positivity
    rw [tot]; push_cast; field_simp
  rwa [e]

/-- The event of the second kind, one for each node a and each group γ': "apply the inequality to
Σ_{b ∈ G_γ'} c_{a,b}, with R = P/g and expectation c_a/K". The event
Σ_{b ∈ G_γ'} c_{a,b} ≥ (c_a + ζP)/K has at most the fraction exp(−2(g/K)ζ²) of all e. -/
theorem event_second_kind (hK : 1 ≤ K) (hn : 1 ≤ n) (c : Fin (K * n) → Fin (K * n) → ℕ) {P ζ : ℝ} (hζ : 0 ≤ ζ) (hP0 : 0 < P)
    (hPg : ∀ a b, a ≠ b → (c a b : ℝ) ≤ P / ((K * n : ℕ) : ℝ)) (a : Fin (K * n)) (γ' : Fin K) :
    (#{e : Equiv.Perm (Fin (K * n)) | (cs c a + ζ * P) / K ≤ ∑ b ∈ cls e γ', cz c a b} : ℝ) ≤
      Real.exp (-(2 * n * ζ ^ 2)) * #(univ : Finset (Equiv.Perm (Fin (K * n)))) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hg0 : (0 : ℝ) < ((K * n : ℕ) : ℝ) := by push_cast; positivity
  have hR : 0 < P / ((K * n : ℕ) : ℝ) := div_pos hP0 hg0
  have w := group_tail hK hn (cz c a) hR (fun b => ⟨cz_nonneg c a b, by
    unfold cz; split_ifs with h
    · exact hR.le
    · exact hPg a b h⟩) hζ γ'
  have e : (cs c a + ζ * P) / K = (∑ b, cz c a b) / K + ζ * n * (P / ((K * n : ℕ) : ℝ)) := by
    rw [cs]; push_cast; field_simp
  rwa [e]

/-! ### The union bound -/

/-- "These are (g+1)K < 2gK events." -/
theorem card_events_lt {K g : ℕ} (hK : 1 ≤ K) (hg : 2 ≤ g) : (g + 1) * K < 2 * g * K :=
  Nat.mul_lt_mul_of_pos_right (by omega) hK

/-- "So for some χ none of them occurs. For this χ we have Σ_{a ∈ G_γ} c_a < (U + ζgP)/K and Σ_{b ∈
G_γ'} c_{a,b} < (c_a + ζP)/K for all γ, γ' and a." -/
theorem exists_no_event (hK : 1 ≤ K) (hn : 1 ≤ n) (hg : 2 ≤ K * n) (c : Fin (K * n) → Fin (K * n) → ℕ) {P ζ : ℝ} (hζ : 0 ≤ ζ) (hP0 : 0 < P)
    (hP : ∀ a, cs c a ≤ P) (hPg : ∀ a b, a ≠ b → (c a b : ℝ) ≤ P / ((K * n : ℕ) : ℝ))
    (hH : (K : ℝ) * Real.log (2 * ((K * n : ℕ) : ℝ) * K) ≤ 2 * ζ ^ 2 * ((K * n : ℕ) : ℝ)) :
    ∃ e : Equiv.Perm (Fin (K * n)), (∀ γ, ∑ a ∈ cls e γ, cs c a < (tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K) ∧
      ∀ a γ', ∑ b ∈ cls e γ', cz c a b < (cs c a + ζ * P) / K := by
  by_contra hno
  push Not at hno
  obtain ⟨ε, hε⟩ : ∃ ε, ε = Real.exp (-(2 * n * ζ ^ 2)) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = #(univ : Finset (Equiv.Perm (Fin (K * n)))) := ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast card_pos.2 univ_nonempty
  have hε0 : 0 < ε := by rw [hε]; exact Real.exp_pos _
  have hε1 : ε ≤ 1 / (2 * ((K * n : ℕ) : ℝ) * K) := by rw [hε]; exact exp_le_inv hK hn hH
  obtain ⟨E1, hE1⟩ : ∃ E1 : Fin K → Finset (Equiv.Perm (Fin (K * n))),
      ∀ γ, E1 γ = ({e | (tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K ≤ ∑ a ∈ cls e γ, cs c a} : Finset (Equiv.Perm (Fin (K * n)))) := ⟨_, fun _ => rfl⟩
  obtain ⟨E2, hE2⟩ : ∃ E2 : Fin (K * n) → Fin K → Finset (Equiv.Perm (Fin (K * n))),
      ∀ a γ', E2 a γ' = ({e | (cs c a + ζ * P) / K ≤ ∑ b ∈ cls e γ', cz c a b} : Finset (Equiv.Perm (Fin (K * n)))) := ⟨_, fun _ _ => rfl⟩
  have h1 : ∀ γ, (#(E1 γ) : ℝ) ≤ ε * N := fun γ => by rw [hE1, hε, hN]; exact event_first_kind hK hn c hζ hP0 hP γ
  have h2 : ∀ a γ', (#(E2 a γ') : ℝ) ≤ ε * N := fun a γ' => by rw [hE2, hε, hN]; exact event_second_kind hK hn c hζ hP0 hPg a γ'
  have hcover : (univ : Finset (Equiv.Perm (Fin (K * n)))) ⊆ (univ.biUnion E1) ∪ (univ.biUnion fun a => univ.biUnion (E2 a)) := by
    intro e _
    by_cases h : ∀ γ, ∑ a ∈ cls e γ, cs c a < (tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K
    · obtain ⟨a, γ', hb⟩ := hno e h
      exact mem_union_right _ (mem_biUnion.2 ⟨a, mem_univ _, mem_biUnion.2 ⟨γ', mem_univ _, by rw [hE2]; exact mem_filter.2 ⟨mem_univ _, hb⟩⟩⟩)
    · push Not at h
      obtain ⟨γ, hγ⟩ := h
      exact mem_union_left _ (mem_biUnion.2 ⟨γ, mem_univ _, by rw [hE1]; exact mem_filter.2 ⟨mem_univ _, hγ⟩⟩)
  have hcard : N ≤ ∑ γ, (#(E1 γ) : ℝ) + ∑ a, ∑ γ', (#(E2 a γ') : ℝ) := by
    have := (card_le_card hcover).trans ((card_union_le _ _).trans
      (Nat.add_le_add card_biUnion_le (card_biUnion_le.trans (sum_le_sum fun a _ => card_biUnion_le))))
    rw [hN]
    exact_mod_cast this
  have hb1 : ∑ γ, (#(E1 γ) : ℝ) ≤ K * (ε * N) := by
    calc ∑ γ, (#(E1 γ) : ℝ) ≤ ∑ _γ : Fin K, ε * N := sum_le_sum fun γ _ => h1 γ
      _ = K * (ε * N) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hb2 : ∑ a, ∑ γ', (#(E2 a γ') : ℝ) ≤ ((K * n : ℕ) : ℝ) * (K * (ε * N)) := by
    calc ∑ a, ∑ γ', (#(E2 a γ') : ℝ) ≤ ∑ _a : Fin (K * n), ∑ _γ : Fin K, ε * N := sum_le_sum fun a _ => sum_le_sum fun γ' _ => h2 a γ'
      _ = ((K * n : ℕ) : ℝ) * (K * (ε * N)) := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hev : (((K * n : ℕ) : ℝ) + 1) * K < 2 * ((K * n : ℕ) : ℝ) * K := by exact_mod_cast card_events_lt hK hg
  have hpos : (0 : ℝ) < 2 * ((K * n : ℕ) : ℝ) * K := lt_of_le_of_lt (by positivity) hev
  have h3 : (((K * n : ℕ) : ℝ) + 1) * K * ε < 1 := by
    calc (((K * n : ℕ) : ℝ) + 1) * K * ε < 2 * ((K * n : ℕ) : ℝ) * K * ε := mul_lt_mul_of_pos_right hev hε0
      _ ≤ 2 * ((K * n : ℕ) : ℝ) * K * (1 / (2 * ((K * n : ℕ) : ℝ) * K)) := mul_le_mul_of_nonneg_left hε1 hpos.le
      _ = 1 := mul_one_div_cancel hpos.ne'
  have h4 : N ≤ (((K * n : ℕ) : ℝ) + 1) * K * ε * N := by
    calc N ≤ K * (ε * N) + ((K * n : ℕ) : ℝ) * (K * (ε * N)) := hcard.trans (add_le_add hb1 hb2)
      _ = _ := by ring
  have h5 : (((K * n : ℕ) : ℝ) + 1) * K * ε * N < 1 * N := mul_lt_mul_of_pos_right h3 hN0
  linarith

/-! ### The display -/

/-- Y_{γ,γ'} for the groups of χ₀∘e: the sum of c_{a,b} over a ∈ G_γ and b ∈ G_γ'. -/
noncomputable def Yg (c : Fin (K * n) → Fin (K * n) → ℕ) (e : Equiv.Perm (Fin (K * n))) (γ γ' : Fin K) : ℝ := ∑ a ∈ cls e γ, ∑ b ∈ cls e γ', (c a b : ℝ)

/-- The first inequality of the display, "summing the second bound over the g/K nodes a ∈ G_γ, where
γ ≠ γ'": Y_{γ,γ'} < (1/K)·Σ_{a ∈ G_γ} c_a + (g/K)·(ζP/K). -/
theorem display_left (hn : 1 ≤ n) (c : Fin (K * n) → Fin (K * n) → ℕ) {P ζ : ℝ} (e : Equiv.Perm (Fin (K * n)))
    (h2 : ∀ a γ', ∑ b ∈ cls e γ', cz c a b < (cs c a + ζ * P) / K) {γ γ' : Fin K} (hne : γ ≠ γ') :
    Yg c e γ γ' < 1 / K * ∑ a ∈ cls e γ, cs c a + ((K * n : ℕ) : ℝ) / K * (ζ * P / K) := by
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact γ.elim0
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hY : Yg c e γ γ' = ∑ a ∈ cls e γ, ∑ b ∈ cls e γ', cz c a b :=
    sum_congr rfl fun a ha => sum_congr rfl fun b hb =>
      (if_neg fun h : a = b => disjoint_left.1 (disjoint_cls e hne) ha (h ▸ hb)).symm
  have hne' : (cls e γ).Nonempty := card_pos.1 (by rw [card_cls]; exact hn)
  calc Yg c e γ γ' < ∑ a ∈ cls e γ, (cs c a + ζ * P) / K := by rw [hY]; exact sum_lt_sum_of_nonempty hne' fun a _ => h2 a γ'
    _ = 1 / K * ∑ a ∈ cls e γ, cs c a + ((K * n : ℕ) : ℝ) / K * (ζ * P / K) := by
        rw [← sum_div, sum_add_distrib, sum_const, card_cls, nsmul_eq_mul]
        push_cast
        field_simp

/-- The second inequality of the display, "inserting the first": (1/K)·Σ_{a ∈ G_γ} c_a +
(g/K)·(ζP/K) < (U + 2ζgP)/K². -/
theorem display_right (c : Fin (K * n) → Fin (K * n) → ℕ) {P ζ : ℝ} (e : Equiv.Perm (Fin (K * n)))
    (h1 : ∀ γ, ∑ a ∈ cls e γ, cs c a < (tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K) (γ : Fin K) :
    1 / K * ∑ a ∈ cls e γ, cs c a + ((K * n : ℕ) : ℝ) / K * (ζ * P / K) < (tot c + 2 * ζ * ((K * n : ℕ) : ℝ) * P) / (K : ℝ) ^ 2 := by
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.2 fun h => by subst h; exact γ.elim0
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have h := mul_lt_mul_of_pos_left (h1 γ) (one_div_pos.2 hK0)
  have e1 : 1 / (K : ℝ) * ((tot c + ζ * ((K * n : ℕ) : ℝ) * P) / K) + ((K * n : ℕ) : ℝ) / K * (ζ * P / K) =
      (tot c + 2 * ζ * ((K * n : ℕ) : ℝ) * P) / (K : ℝ) ^ 2 := by
    field_simp
    ring
  linarith

end GeneralPieces.Group

namespace GeneralPieces

open Finset ClauseBound.Group.Grouping GeneralPieces.Group

/-- The existence claim in the proof of Lemma 8 (Appendix A), case (ii). -/
theorem stCaseII : StCaseII := by
  intro K g c P ζ hK hg hdvd hζ _ hP0 hP hPg hH
  obtain ⟨n, rfl⟩ := hdvd
  have hK1 : 1 ≤ K := by omega
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun h => by subst h; omega
  obtain ⟨e, h1, h2⟩ := exists_no_event hK1 hn hg c hζ.le hP0 (fun a => by rw [cs_eq]; exact hP a) hPg hH
  refine ⟨fun a => chi0 (e a), fun γ => ?_, fun γ γ' hne => ?_⟩
  · rw [card_group, Nat.mul_div_cancel_left n (by omega)]
  · rw [← tot_eq]
    simp only [← cls_eq]
    exact (display_left hn c e h2 hne).trans (display_right c e h1 γ)

end GeneralPieces
