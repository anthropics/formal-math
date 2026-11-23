/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Identity
import Nc.Cross.Data
import Nc.Price.Cross

/-!
# The paper, section "Two crossing wires": the inequality

The states are in Paper/States.lean (Lemma lem:count) and the identity is in Paper/Identity.lean (Proposition prop:identity).
-/

namespace Paper

open Finset Filter Ov Ov.Ten Nc.Price Nc.Cross

variable {K : Type} [Field K]

section Hubs

variable {I : Type} [Fintype I] [DecidableEq I] (F : Spec K I)

/-- Lemma lem:hubs, read for a spectral point φ: a tensor that is a sum of r products of a tensor on the legs in S and one on the
other legs has φ at most the product of the values of the wires to the hubs o₁, o₂ and of the wire ⟨r⟩ between them. -/
theorem prop_crossing_cut {A : Type} [Fintype A] [DecidableEq A] (π : A → I) (t : Ten K A) (S : A → Prop)
    [DecidablePred S] {r : ℕ} (g h : Fin r → (∀ a, t.ι a) → K)
    (hg : ∀ j x x', (∀ a, S a → x a = x' a) → g j x = g j x')
    (hh : ∀ j x x', (∀ a, ¬ S a → x a = x' a) → h j x = h j x')
    (hs : ∀ x, t.val x = ∑ j, g j x * h j x) (o₁ o₂ : I) :
    F.F (Ten.push π t) ≤ (∏ a, (Fintype.card (t.ι a) : ℝ) ^ F.e (π a) (if S a then o₁ else o₂)) *
      (r : ℝ) ^ F.e o₁ o₂ := by
  refine (F.mono (lem_hubs π t S g h hg hh hs o₁ o₂)).trans ?_
  rw [F.mul, F.prod]
  exact mul_le_mul (Finset.prod_le_prod (fun _ _ => F.nonneg _) fun a _ => F.wire_le _ _ _) (F.wire_le _ _ _)
    (F.nonneg _) (Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

variable {α β : Type} [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β]
  [Nonempty β]

/-- Proof of Proposition prop:crossing: "Lemma lem:hubs, with the hubs o, o′ for (c) …, bounds φ(Ψ_N)." The four legs are at
x, y, v, u, and f is a sum of R products of a function of the indices at x, y and one of those at v, u. -/
theorem prop_crossing_hubs_c {f : α → β → α → β → K} {R : ℕ} (h : SplitAB f R) (x y v u o o' : I) :
    F.F (Ten.push ![x, y, v, u] (four f)) ≤
      (Fintype.card α : ℝ) ^ (F.e x o + F.e v o') * (Fintype.card β : ℝ) ^ (F.e y o + F.e u o') *
        (R : ℝ) ^ F.e o o' := by
  obtain ⟨g, w, hf⟩ := h
  have h1 := prop_crossing_cut F ![x, y, v, u] (four f) (fun a => a = 0 ∨ a = 1)
    (fun t z => g t (z 0, z 1)) (fun t z => w t (z 2, z 3))
    (fun t z z' hz => by
      have h0 := hz 0 (Or.inl rfl)
      have h1 := hz 1 (Or.inr rfl)
      simp only [h0, h1])
    (fun t z z' hz => by
      have h0 := hz 2 (by decide)
      have h1 := hz 3 (by decide)
      simp only [h0, h1])
    (fun z => hf (z 0) (z 1) (z 2) (z 3)) o o'
  refine h1.trans (mul_le_mul_of_nonneg_right (le_of_eq ?_) (by positivity))
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  rw [Fin.prod_univ_four, Real.rpow_add hα, Real.rpow_add hβ]
  show (Fintype.card α : ℝ) ^ F.e x o * (Fintype.card β : ℝ) ^ F.e y o *
    (Fintype.card α : ℝ) ^ F.e v o' * (Fintype.card β : ℝ) ^ F.e u o' = _
  ring

/-- Proof of Proposition prop:crossing: "Lemma lem:hubs, with the hubs … w, w′ for (b), bounds φ(Ψ_N)." Here f is a sum of L
products of a function of the indices at x, u and one of those at y, v. -/
theorem prop_crossing_hubs_b {f : α → β → α → β → K} {L : ℕ} (h : SplitAD f L) (x y v u w w' : I) :
    F.F (Ten.push ![x, y, v, u] (four f)) ≤
      (Fintype.card α : ℝ) ^ (F.e x w + F.e v w') * (Fintype.card β : ℝ) ^ (F.e u w + F.e y w') *
        (L : ℝ) ^ F.e w w' := by
  obtain ⟨g, m, hf⟩ := h
  have h1 := prop_crossing_cut F ![x, y, v, u] (four f) (fun a => a = 0 ∨ a = 3)
    (fun t z => g t (z 0, z 3)) (fun t z => m t (z 1, z 2))
    (fun t z z' hz => by
      have h0 := hz 0 (Or.inl rfl)
      have h1 := hz 3 (Or.inr rfl)
      simp only [h0, h1])
    (fun t z z' hz => by
      have h0 := hz 1 (by decide)
      have h1 := hz 2 (by decide)
      simp only [h0, h1])
    (fun z => hf (z 0) (z 1) (z 2) (z 3)) w w'
  refine h1.trans (mul_le_mul_of_nonneg_right (le_of_eq ?_) (by positivity))
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  rw [Fin.prod_univ_four, Real.rpow_add hα, Real.rpow_add hβ]
  show (Fintype.card α : ℝ) ^ F.e x w * (Fintype.card β : ℝ) ^ F.e y w' *
    (Fintype.card α : ℝ) ^ F.e v w' * (Fintype.card β : ℝ) ^ F.e u w = _
  ring

/-- Proof of Proposition prop:crossing: "The product of the two wires is covered by the Θ+1 tensors Ψ_N of Proposition
prop:identity (a), φ is subadditive". The left side is the value of φ at the two wires, of dimensions |α| and |β|. -/
theorem prop_crossing_cover {J : Type} [Fintype J] (Ψ : J → α → β → α → β → K)
    (hΨ : ∀ a b c d, ∑ j, Ψ j a b c d = if a = c ∧ b = d then 1 else 0) (x y v u : I) :
    (Fintype.card α : ℝ) ^ F.e x v * (Fintype.card β : ℝ) ^ F.e y u ≤
      ∑ j, F.F (Ten.push ![x, y, v, u] (four (Ψ j))) := by
  refine (le_F_cross (K := K) (α := α) (β := β) F x y v u).trans ?_
  have h : SumRestr (four fun (a : α) (b : β) c d => if a = c ∧ b = d then (1 : K) else 0)
      fun j => four (Ψ j) :=
    SumRestr.of_withVal (four fun (a : α) (b : β) c d => if a = c ∧ b = d then (1 : K) else 0)
      (fun j z => Ψ j (z 0) (z 1) (z 2) (z 3)) fun z => (hΨ (z 0) (z 1) (z 2) (z 3)).symm
  exact F.le_sum _ _ (h.push ![x, y, v, u])

/-- Proof of Proposition prop:crossing: "so some N has ln φ(Ψ_N) ≥ (p|xv| + q|yu| − o(1))κ√n₀". Before logarithms: some φ(Ψ_N) is
at least the value of the two wires divided by the number Θ+1 of the tensors. -/
theorem prop_crossing_some {J : Type} [Fintype J] (Ψ : J → α → β → α → β → K)
    (hΨ : ∀ a b c d, ∑ j, Ψ j a b c d = if a = c ∧ b = d then 1 else 0) (x y v u : I) :
    ∃ j, (Fintype.card α : ℝ) ^ F.e x v * (Fintype.card β : ℝ) ^ F.e y u ≤
      Fintype.card J * F.F (Ten.push ![x, y, v, u] (four (Ψ j))) := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have h1 := prop_crossing_cover F Ψ hΨ x y v u
  have hJ : Nonempty J := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h1
    exact absurd h1 (not_le.2 (mul_pos (Real.rpow_pos_of_pos hα _) (Real.rpow_pos_of_pos hβ _)))
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image (Finset.univ : Finset J)
    (fun j => F.F (Ten.push ![x, y, v, u] (four (Ψ j)))) Finset.univ_nonempty
  refine ⟨j, h1.trans ?_⟩
  rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_le_sum fun i hi => hj i hi

/-- Proof of Proposition prop:crossing: "Lemma lem:hubs, with the hubs o, o′ for (c) and w, w′ for (b), bounds φ(Ψ_N) in both ways."
So for the N of the step before, in logarithms: ln|α|·|xv| + ln|β|·|yu| is at most ln(Θ+1) plus each of the two bounds through the
hubs, where Ψ_N is a sum of R_N products as in (c) and of L_N products as in (b). -/
theorem prop_crossing_term {J : Type} [Fintype J] (Ψ : J → α → β → α → β → K) (R L : J → ℕ)
    (hR : ∀ j, SplitAB (Ψ j) (R j))
    (hL : ∀ j, SplitAD (Ψ j) (L j))
    (hΨ : ∀ a b c d, ∑ j, Ψ j a b c d = if a = c ∧ b = d then 1 else 0)
    (x y v u o o' w w' : I) :
    ∃ j, Real.log (Fintype.card α) * F.e x v + Real.log (Fintype.card β) * F.e y u ≤
      Real.log (Fintype.card J) +
      min (Real.log (Fintype.card α) * (F.e x o + F.e v o') +
          Real.log (Fintype.card β) * (F.e y o + F.e u o') + Real.log (R j) * F.e o o')
        (Real.log (Fintype.card α) * (F.e x w + F.e v w') +
          Real.log (Fintype.card β) * (F.e u w + F.e y w') + Real.log (L j) * F.e w w') := by
  have hα : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hβ : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  obtain ⟨j, hj⟩ := prop_crossing_some F Ψ hΨ x y v u
  have hJ0 : (0 : ℝ) < Fintype.card J := by
    have : Nonempty J := ⟨j⟩
    exact_mod_cast Fintype.card_pos
  refine ⟨j, ?_⟩
  have hexp : ∀ (s s' : ℝ) (n : ℕ) (e : ℝ), (Fintype.card α : ℝ) ^ s * (Fintype.card β : ℝ) ^ s' * (n : ℝ) ^ e ≤
      Real.exp (Real.log (Fintype.card α) * s + Real.log (Fintype.card β) * s' + Real.log n * e) := by
    intro s s' n e
    rw [Real.rpow_def_of_pos hα, Real.rpow_def_of_pos hβ, Real.exp_add, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (rpow_le_exp n e) (by positivity)
  have hc := (prop_crossing_hubs_c F (hR j) x y v u o o').trans (hexp _ _ _ _)
  have hb := (prop_crossing_hubs_b F (hL j) x y v u w w').trans (hexp _ _ _ _)
  have hm := le_min hc hb
  rw [← Real.exp_monotone.map_min] at hm
  have h2 := hj.trans (mul_le_mul_of_nonneg_left hm hJ0.le)
  rw [Real.rpow_def_of_pos hα, Real.rpow_def_of_pos hβ, ← Real.exp_add] at h2
  nth_rewrite 1 [← Real.exp_log hJ0] at h2
  rw [← Real.exp_add, Real.exp_le_exp] at h2
  exact h2

end Hubs

/-- Proof of Proposition prop:crossing: "By pigeonhole some classes Σ_i of energy e_i ≤ E_i contain at least a fraction (E_i+1)⁻²,
and of course at most all, of the states of energy at most E_i." -/
theorem prop_crossing_classes (E : ℕ) : ∃ μ e, e ≤ E ∧ stateCount E ≤ (E + 1) ^ 2 * (states μ e).card ∧
    (states μ e).card ≤ stateCount E := by
  classical
  set S := range (E + 1) ×ˢ range (E + 1) with hS
  have hmaps : ∀ s ∈ pairs E, (s.1.card, en s.1 + en s.2) ∈ S := by
    intro s hs
    obtain ⟨h1, h2⟩ := mem_pairs.1 hs
    have h3 : s.1.card ≤ en s.1 := by
      rw [en, Finset.card_eq_sum_ones]
      exact Finset.sum_le_sum fun i _ => by omega
    rw [hS, mem_product, mem_range, mem_range]
    exact ⟨by simp only; omega, by simp only; omega⟩
  obtain ⟨z, hz, hmax⟩ := Finset.exists_max_image S (fun z => (states z.1 z.2).card) ⟨(0, 0), by simp [hS]⟩
  have hzE : z.2 ≤ E := by
    have := (mem_product.1 hz).2
    rw [mem_range] at this
    omega
  refine ⟨z.1, z.2, hzE, ?_, card_le_card ((filter_subset _ _).trans (pairs_mono hzE))⟩
  show (pairs E).card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc ∑ b ∈ S, ((pairs E).filter fun s => (s.1.card, en s.1 + en s.2) = b).card
      ≤ ∑ b ∈ S, (states b.1 b.2).card := by
        refine Finset.sum_le_sum fun b _ => Finset.card_le_card fun s hs => ?_
        obtain ⟨h1, h2⟩ := mem_filter.1 hs
        obtain ⟨h3, h4⟩ := mem_pairs.1 h1
        rw [← h2]
        exact mem_filter.2 ⟨mem_pairs.2 ⟨h3, le_rfl⟩, rfl, h3.symm, rfl⟩
    _ ≤ ∑ _b ∈ S, (states z.1 z.2).card := Finset.sum_le_sum fun b hb => hmax b hb
    _ = (E + 1) ^ 2 * (states z.1 z.2).card := by
        rw [Finset.sum_const, smul_eq_mul, hS, card_product, card_range, pow_two]

/-- Proof of Proposition prop:crossing: "so, in units of κ√n₀, their logarithms are p + o(1) and q + o(1) by Lemma lem:count."
Here κ is a constant with the two properties of Lemma lem:count, n is the paper's n₀, and the class Σ of size μ and energy
e ≤ E = ⌊p²n⌋ is the one found by pigeonhole. -/
theorem prop_crossing_class_size {κ : ℝ} (hκ : 0 < κ) (hup : ∀ E : ℕ, Real.log (stateCount E) ≤ κ * √E)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ᶠ E : ℕ in atTop, (κ - ε) * √E ≤ Real.log (stateCount E)) {p : ℝ} (hp : 0 ≤ p)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∃ μ e, e ≤ ⌊p ^ 2 * n⌋₊ ∧ 0 < (states μ e).card ∧
      |Real.log (states μ e).card - p * (κ * √n)| ≤ δ * (κ * √n) := by
  have hlow' : ∀ ε > 0, ∃ E₀ : ℕ, ∀ E, E₀ ≤ E → (κ - ε) * √E ≤ lp E := fun ε hε => eventually_atTop.1 (hlow ε hε)
  filter_upwards [lower_bound hκ hlow' hp (η := δ * κ) (by positivity)] with n hn
  obtain ⟨μ, e, he, hcard, hle⟩ := prop_crossing_classes ⌊p ^ 2 * n⌋₊
  set E := ⌊p ^ 2 * n⌋₊ with hE
  have hpos : 0 < (states μ e).card := by
    rcases Nat.eq_zero_or_pos (states μ e).card with h0 | h0
    · rw [h0, mul_zero] at hcard
      exact absurd (pairs_pos E) (by simpa [stateCount] using hcard)
    · exact h0
  have h0 : (0 : ℝ) < (states μ e).card := by exact_mod_cast hpos
  have hlower : lp E - 2 * Real.log ((E : ℝ) + 1) ≤ Real.log (states μ e).card := by
    have h1 : ((pairs E).card : ℝ) ≤ ((E : ℝ) + 1) ^ 2 * (states μ e).card := by exact_mod_cast hcard
    have h2 := Real.log_le_log (by exact_mod_cast pairs_pos E) h1
    rw [Real.log_mul (by positivity) h0.ne', Real.log_pow] at h2
    rw [Nc.Cross.lp]
    push_cast at h2
    linarith
  have hupper : Real.log (states μ e).card ≤ κ * √(E : ℝ) :=
    (Real.log_le_log h0 (by exact_mod_cast hle)).trans (hup E)
  have hv := mul_le_mul_of_nonneg_left (sqrt_floor_le hp n) hκ.le
  have hd : 0 ≤ δ * (κ * √(n : ℝ)) := by positivity
  refine ⟨μ, e, he, hpos, abs_le.2 ⟨?_, ?_⟩⟩
  · linarith
  · linarith

/-- Proof of Proposition prop:crossing: "In the same units the logarithm of the number of products in (b) is at most l + o(1) and
that in (c) at most r + o(1), with l² = N/n₀, r² = (Θ−N)/n₀". Here M stands for N and for Θ − N, which are at most Θ ≤ An, and
(M+1)P(M) is the number of products. -/
theorem prop_crossing_products {κ : ℝ} (hκ : 0 < κ) (hup : ∀ E : ℕ, Real.log (stateCount E) ≤ κ * √E) {A : ℝ}
    (hA : 0 ≤ A) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ M : ℕ, (M : ℝ) ≤ A * n →
      Real.log (((M + 1) * stateCount M : ℕ) : ℝ) ≤ (√(M : ℝ) / √(n : ℝ) + δ) * (κ * √n) := by
  filter_upwards [log_small hA (η := δ * κ) (by positivity), eventually_ge_atTop 1] with n hlog hn M hM
  have hsn : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have h2 : Real.log ((M : ℝ) + 1) ≤ δ * κ * √(n : ℝ) :=
    (Real.log_le_log (by positivity) (by linarith)).trans hlog
  have h4 : Real.log (((M + 1) * stateCount M : ℕ) : ℝ) = Real.log ((M : ℝ) + 1) + Real.log (stateCount M) := by
    push_cast
    exact Real.log_mul (by positivity) (by exact_mod_cast (pairs_pos M).ne')
  have h5 : (√(M : ℝ) / √(n : ℝ) + δ) * (κ * √(n : ℝ)) = κ * √(M : ℝ) + δ * κ * √(n : ℝ) := by
    field_simp
  rw [h5, h4]
  linarith [hup M]

/-- Proof of Proposition prop:crossing, the tensors: for every δ > 0 there are s > 0 and finite sets α, β (in the proof: the
paper's κ√n₀ and the classes of states, by pigeonhole and Lemma lem:count) with ln|α| = (p ± δ)s and ln|β| = (q ± δ)s, and
at most e^(δs) tensors Ψ_N with sum the two wires (Proposition prop:identity (a)), where Ψ_N is a sum of at most e^((r+δ)s) products as in (c) and of at most e^((l+δ)s)
products as in (b), with r² + l² ≤ 2(p² + q²). -/
theorem prop_crossing_tensors (K : Type) [Field K] {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (α β J : Type) (_ : Fintype α) (_ : DecidableEq α) (_ : Nonempty α)
      (_ : Fintype β) (_ : DecidableEq β) (_ : Nonempty β) (_ : Fintype J)
      (Ψ : J → α → β → α → β → K) (R L : J → ℕ) (s : ℝ), 0 < s ∧
      (∀ j, SplitAB (Ψ j) (R j)) ∧ (∀ j, SplitAD (Ψ j) (L j)) ∧
      (∀ a b c d, ∑ j, Ψ j a b c d = if a = c ∧ b = d then 1 else 0) ∧
      Real.log (Fintype.card J) ≤ δ * s ∧ |Real.log (Fintype.card α) - p * s| ≤ δ * s ∧
      |Real.log (Fintype.card β) - q * s| ≤ δ * s ∧
      ∀ j, ∃ r l : ℝ, 0 ≤ r ∧ 0 ≤ l ∧ r ^ 2 + l ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) ∧
        Real.log (R j) ≤ (r + δ) * s ∧ Real.log (L j) ≤ (l + δ) * s := by
  obtain ⟨c, hc, hup, hlow⟩ := lem_count
  set A : ℝ := 2 * (p ^ 2 + q ^ 2) with hA
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨n, ⟨⟨μ, e₁, he₁, hpos₁, hsize₁⟩, ⟨ν, e₂, he₂, hpos₂, hsize₂⟩⟩, hnum, hlog, hn⟩ :=
    (((prop_crossing_class_size hc hup hlow hp hδ).and (prop_crossing_class_size hc hup hlow hq hδ)).and
      ((prop_crossing_products hc hup hA0 hδ).and
        ((log_small hA0 (η := δ * c) (by positivity)).and (eventually_ge_atTop 1)))).exists
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  obtain ⟨Ψ, hΨ, hL, hR⟩ := prop_identity μ ν e₁ e₂
  have hH : ((2 * (e₁ + e₂) : ℕ) : ℝ) ≤ A * n := by
    have h1 : ((e₁ : ℕ) : ℝ) ≤ (⌊p ^ 2 * n⌋₊ : ℕ) := by exact_mod_cast he₁
    have h2 : ((e₂ : ℕ) : ℝ) ≤ (⌊q ^ 2 * n⌋₊ : ℕ) := by exact_mod_cast he₂
    have h3 := floor_le' (p := p) n
    have h4 := floor_le' (p := q) n
    push_cast
    rw [hA]
    linarith
  have hnum' : ∀ M : ℕ, M ≤ 2 * (e₁ + e₂) →
      Real.log (((M + 1) * stateCount M : ℕ) : ℝ) ≤ (Real.sqrt M / Real.sqrt n + δ) * (c * Real.sqrt n) :=
    fun M hM => hnum M (le_trans (by exact_mod_cast hM) hH)
  refine ⟨↥(states μ e₁), ↥(states ν e₂), Fin (2 * (e₁ + e₂) + 1), inferInstance, inferInstance,
    ?_, inferInstance, inferInstance, ?_, inferInstance, fun N a b c d => ((Ψ N a b c d : ℤ) : K),
    fun N => (2 * (e₁ + e₂) - N + 1) * stateCount (2 * (e₁ + e₂) - N), fun N => (N + 1) * stateCount N,
    c * Real.sqrt n, by positivity, fun N => ?_, fun N => ?_, fun a b c d => ?_, ?_, ?_, ?_, fun N => ?_⟩
  · exact (Finset.card_pos.1 hpos₁).to_subtype
  · exact (Finset.card_pos.1 hpos₂).to_subtype
  · obtain ⟨g, h, hgh⟩ := hR N _ rfl
    refine ⟨fun k z => ((g k z : ℤ) : K), fun k z => ((h k z : ℤ) : K), fun a b c d => ?_⟩
    simp only
    rw [hgh]
    push_cast
    rfl
  · obtain ⟨g, h, hgh⟩ := hL N
    refine ⟨fun k z => ((g k z : ℤ) : K), fun k z => ((h k z : ℤ) : K), fun a b c d => ?_⟩
    simp only
    rw [hgh]
    push_cast
    rfl
  · rw [← Int.cast_sum, hΨ, ite_and]
    split_ifs <;> simp
  · rw [Fintype.card_fin]
    push_cast
    push_cast at hH
    have h1 : Real.log (2 * ((e₁ : ℝ) + e₂) + 1) ≤ Real.log (A * n + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  · rw [Fintype.card_coe]
    exact hsize₁
  · rw [Fintype.card_coe]
    exact hsize₂
  · have hN : (N : ℕ) ≤ 2 * (e₁ + e₂) := by omega
    refine ⟨Real.sqrt ((2 * (e₁ + e₂) - N : ℕ) : ℝ) / Real.sqrt n, Real.sqrt ((N : ℕ) : ℝ) / Real.sqrt n,
      by positivity, by positivity, ?_, hnum' _ (Nat.sub_le _ _), hnum' _ hN⟩
    rw [div_pow, div_pow, Real.sq_sqrt (Nat.cast_nonneg (2 * (e₁ + e₂) - N)),
      Real.sq_sqrt (Nat.cast_nonneg (N : ℕ)), Real.sq_sqrt hn0.le, ← add_div, div_le_iff₀ hn0, Nat.cast_sub hN, sub_add_cancel]
    exact hH

/-- Proof of Proposition prop:crossing: "So it suffices to treat d_φ for a spectral point φ"; this is the statement for d_φ. "A limit
of (r, l) along a subsequence proves the first statement." -/
theorem prop_crossing_spectral {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) {I : Type} [Fintype I]
    [DecidableEq I] (F : Spec K I) (x y v u o o' w w' : I) :
    ∃ z ∈ quarter (2 * (p ^ 2 + q ^ 2)), p * F.e x v + q * F.e y u ≤
      min (p * F.e x o + q * F.e y o + p * F.e v o' + q * F.e u o' + z.1 * F.e o o')
        (p * F.e x w + q * F.e u w + q * F.e y w' + p * F.e v w' + z.2 * F.e w w') := by
  refine exists_quarter (by positivity) fun δ hδ => ?_
  obtain ⟨α, β, J, _, _, _, _, _, _, _, Ψ, R, L, s, hs, hR, hL, hΨ, hJ, hα, hβ, hrl⟩ :=
    prop_crossing_tensors K hp hq (δ := δ / 8) (by positivity)
  obtain ⟨j, hj⟩ := prop_crossing_term F Ψ R L hR hL hΨ x y v u o o' w w'
  obtain ⟨r, l, hr, hl, hrl, h1, h2⟩ := hrl j
  refine ⟨(r, l), ⟨hr, hl, hrl⟩, ?_⟩
  set A := Real.log (Fintype.card α) with hA
  set B := Real.log (Fintype.card β) with hB
  obtain ⟨hα1, hα2⟩ := abs_le.1 hα
  obtain ⟨hβ1, hβ2⟩ := abs_le.1 hβ
  have hi : ∀ (a b : I) {Z c : ℝ}, Z ≤ c * s + δ / 8 * s → Z * F.e a b ≤ (c * F.e a b + δ / 8) * s := by
    intro a b Z c h
    have e0 := F.e_nonneg a b
    have e1 := F.e_le_one a b
    have h3 := mul_le_mul_of_nonneg_right h e0
    have h4 : δ / 8 * s * F.e a b ≤ δ / 8 * s := mul_le_of_le_one_right (by positivity) e1
    nlinarith
  have lo : ∀ (a b : I) {Z c : ℝ}, c * s - δ / 8 * s ≤ Z → (c * F.e a b - δ / 8) * s ≤ Z * F.e a b := by
    intro a b Z c h
    have e0 := F.e_nonneg a b
    have e1 := F.e_le_one a b
    have h3 := mul_le_mul_of_nonneg_right h e0
    have h4 : δ / 8 * s * F.e a b ≤ δ / 8 * s := mul_le_of_le_one_right (by positivity) e1
    nlinarith
  have b1 := lo x v (Z := A) (c := p) (by linarith)
  have b2 := lo y u (Z := B) (c := q) (by linarith)
  rw [← min_add_add_right]
  refine le_min ?_ ?_
  · have hj1 := hj.trans (add_le_add le_rfl (min_le_left _ _))
    have c1 := hi x o (Z := A) (c := p) (by linarith)
    have c2 := hi y o (Z := B) (c := q) (by linarith)
    have c3 := hi v o' (Z := A) (c := p) (by linarith)
    have c4 := hi u o' (Z := B) (c := q) (by linarith)
    have c5 := hi o o' (Z := Real.log (R j)) (c := r) (by linarith)
    refine le_of_mul_le_mul_right ?_ hs
    simp only
    nlinarith
  · have hj1 := hj.trans (add_le_add le_rfl (min_le_right _ _))
    have c1 := hi x w (Z := A) (c := p) (by linarith)
    have c2 := hi u w (Z := B) (c := q) (by linarith)
    have c3 := hi v w' (Z := A) (c := p) (by linarith)
    have c4 := hi y w' (Z := B) (c := q) (by linarith)
    have c5 := hi w w' (Z := Real.log (L j)) (c := l) (by linarith)
    refine le_of_mul_le_mul_right ?_ hs
    simp only
    nlinarith

/-- Proposition prop:crossing, the first statement. "Pull the price back to eight distinct points; this covers coincidences. Both
inequalities are homogeneous in the distances, and the pairs (r, l) lie in a compact set, so they pass to limits." -/
theorem prop_crossing_first {Y : Type} {d : Y → Y → ℝ} (hd : IsPrice K d) (x v y u o o' w w' : Y)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    ∃ r l : ℝ, 0 ≤ r ∧ 0 ≤ l ∧ r ^ 2 + l ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) ∧
      p * d x v + q * d y u ≤ p * d x o + q * d y o + p * d v o' + q * d u o' + r * d o o' ∧
      p * d x v + q * d y u ≤ p * d x w + q * d u w + q * d y w' + p * d v w' + l * d w w' := by
  set ρ := 2 * (p ^ 2 + q ^ 2) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  obtain ⟨z, ⟨h1, h2, h3⟩, h⟩ : ∃ z ∈ quarter ρ, p * d x v + q * d y u ≤
      min (p * d x o + q * d y o + p * d v o' + q * d u o' + z.1 * d o o')
        (p * d x w + q * d u w + q * d y w' + p * d v w' + z.2 * d w w') := by
    refine exists_quarter hρ0 fun δ hδ => ?_
    set T := 3 * (p + q) + ρ + 1 with hT
    have hT0 : 0 < T := by positivity
    set η := δ / T with hη
    have hη0 : 0 < η := by positivity
    have hηT : η * T = δ := by rw [hη]; field_simp
    obtain ⟨F, c, hc, hF⟩ := hd.exists_spec ![x, y, v, u, o, o', w, w'] hη0
    obtain ⟨z, hz, h⟩ := prop_crossing_spectral hp hq F 0 1 2 3 4 5 6 7
    refine ⟨z, hz, ?_⟩
    obtain ⟨hz1, hz2, hz3⟩ := hz
    have q1 : z.1 ≤ ρ + 1 := by nlinarith [sq_nonneg (z.1 - 1)]
    have q2 : z.2 ≤ ρ + 1 := by nlinarith [sq_nonneg (z.2 - 1)]
    have lo : ∀ (i j : Fin 8) {t : ℝ}, 0 ≤ t →
        t * (c * F.e i j) ≤ t * d (![x, y, v, u, o, o', w, w'] i) (![x, y, v, u, o, o', w, w'] j) +
          t * η := by
      intro i j t ht
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith [(abs_lt.1 (hF i j)).1]) ht
    have hi : ∀ (i j : Fin 8) {t : ℝ}, 0 ≤ t →
        t * d (![x, y, v, u, o, o', w, w'] i) (![x, y, v, u, o, o', w, w'] j) ≤
          t * (c * F.e i j) + t * η := by
      intro i j t ht
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith [(abs_lt.1 (hF i j)).2]) ht
    have a1 : p * d x v ≤ p * (c * F.e 0 2) + p * η := hi 0 2 hp
    have a2 : q * d y u ≤ q * (c * F.e 1 3) + q * η := hi 1 3 hq
    have a3 : p * (c * F.e 0 4) ≤ p * d x o + p * η := lo 0 4 hp
    have a4 : q * (c * F.e 1 4) ≤ q * d y o + q * η := lo 1 4 hq
    have a5 : p * (c * F.e 2 5) ≤ p * d v o' + p * η := lo 2 5 hp
    have a6 : q * (c * F.e 3 5) ≤ q * d u o' + q * η := lo 3 5 hq
    have a7 : z.1 * (c * F.e 4 5) ≤ z.1 * d o o' + z.1 * η := lo 4 5 hz1
    have a8 : p * (c * F.e 0 6) ≤ p * d x w + p * η := lo 0 6 hp
    have a9 : q * (c * F.e 3 6) ≤ q * d u w + q * η := lo 3 6 hq
    have b1 : q * (c * F.e 1 7) ≤ q * d y w' + q * η := lo 1 7 hq
    have b2 : p * (c * F.e 2 7) ≤ p * d v w' + p * η := lo 2 7 hp
    have b3 : z.2 * (c * F.e 6 7) ≤ z.2 * d w w' + z.2 * η := lo 6 7 hz2
    have c1 : z.1 * η ≤ (ρ + 1) * η := mul_le_mul_of_nonneg_right q1 hη0.le
    have c2 : z.2 * η ≤ (ρ + 1) * η := mul_le_mul_of_nonneg_right q2 hη0.le
    have hsum : 3 * (p * η) + 3 * (q * η) + (ρ + 1) * η = δ := by rw [← hηT, hT]; ring
    rw [← min_add_add_right]
    refine le_min ?_ ?_
    · have h4 := mul_le_mul_of_nonneg_left (h.trans (min_le_left _ _)) hc
      linarith
    · have h4 := mul_le_mul_of_nonneg_left (h.trans (min_le_right _ _)) hc
      linarith
  exact ⟨z.1, z.2, h1, h2, h3, le_min_iff.1 h⟩

/-- **Paper: Proposition prop:crossing.** "Let x, v, y, u, o, o′, w, w′ be points of a price and p, q ≥ 0. There are r, l ≥ 0 with
r² + l² ≤ 2(p² + q²) such that p|xv| + q|yu| is at most each of p|xo| + q|yo| + p|vo′| + q|uo′| + r|oo′|, p|xw| + q|uw| + q|yw′| + p|vw′| + l|ww′|.
In particular, for every τ > 0," the inequality (eq:Q) holds. The first statement is prop_crossing_first; for the second,
"add the two bounds and use rλ ≤ (τ/2)r² + λ²/(2τ)". -/
theorem prop_crossing {Y : Type} {d : Y → Y → ℝ} (hd : IsPrice K d) (x v y u o o' w w' : Y)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (∃ r l : ℝ, 0 ≤ r ∧ 0 ≤ l ∧ r ^ 2 + l ^ 2 ≤ 2 * (p ^ 2 + q ^ 2) ∧
      p * d x v + q * d y u ≤ p * d x o + q * d y o + p * d v o' + q * d u o' + r * d o o' ∧
      p * d x v + q * d y u ≤ p * d x w + q * d u w + q * d y w' + p * d v w' + l * d w w') ∧
    ∀ τ : ℝ, 0 < τ → 2 * (p * d x v + q * d y u) ≤
      p * (d x o + d v o' + d x w + d v w') + q * (d y o + d u o' + d u w + d y w') +
        τ * (p ^ 2 + q ^ 2) + (d o o' ^ 2 + d w w' ^ 2) / (2 * τ) := by
  refine ⟨prop_crossing_first hd x v y u o o' w w' hp hq, fun τ hτ => ?_⟩
  obtain ⟨r, l, hr, hl, hrl, h1, h2⟩ := prop_crossing_first hd x v y u o o' w w' hp hq
  have am : ∀ a b : ℝ, a * b ≤ τ / 2 * a ^ 2 + b ^ 2 / (2 * τ) := by
    intro a b
    have e : τ / 2 * a ^ 2 + b ^ 2 / (2 * τ) - a * b = (τ * a - b) ^ 2 / (2 * τ) := by
      field_simp
      ring
    nlinarith [div_nonneg (sq_nonneg (τ * a - b)) (by positivity : (0 : ℝ) ≤ 2 * τ)]
  have a1 := am r (d o o')
  have a2 := am l (d w w')
  have a3 : τ / 2 * (r ^ 2 + l ^ 2) ≤ τ / 2 * (2 * (p ^ 2 + q ^ 2)) :=
    mul_le_mul_of_nonneg_left hrl (by positivity)
  rw [add_div]
  nlinarith

/-- **Paper: display eq:Q.** "In particular, for every τ > 0, 2(p|xv| + q|yu|) ≤ p(|xo| + |vo′| + |xw| + |vw′|) +
q(|yo| + |uo′| + |uw| + |yw′|) + τ(p² + q²) + (|oo′|² + |ww′|²)/(2τ)." This is the second statement of Proposition prop:crossing. -/
theorem eq_Q {Y : Type} {d : Y → Y → ℝ} (hd : IsPrice K d) (x v y u o o' w w' : Y)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (τ : ℝ) (hτ : 0 < τ) :
    2 * (p * d x v + q * d y u) ≤
      p * (d x o + d v o' + d x w + d v w') + q * (d y o + d u o' + d u w + d y w') +
        τ * (p ^ 2 + q ^ 2) + (d o o' ^ 2 + d w w' ^ 2) / (2 * τ) :=
  (prop_crossing hd x v y u o o' w w' hp hq).2 τ hτ

end Paper
