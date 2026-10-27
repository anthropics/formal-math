/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Family.Pairwise
public import VariableBound.Family.SmallBias

/-! # Lemma 13 (Family of checks)

The end of the printed proof, one theorem for each of its steps, with fractions cleared: a
probability is a number of quadruples u = (u₁, u₂, u₃, u₄) ∈ 𝔽⁴, out of |𝔽|⁴.
Throughout, 𝔽 is a finite field, `bits` writes its elements as strings of s bits (linearly over the
field with two elements), ϑ gives the m clauses distinct elements of 𝔽, and v = 2^a.

* `card_odd`: as (u₃, u₄) is independent of (u₁, u₂), |Γ_u ∩ V| is odd with probability at least 2/3
  · 15/32 = 5/16.
* `card_mem`: a clause lies in Γ_u with probability at most 1/v.
* `markov`: |Γ_u| > 16m/v with probability at most 1/16.
* `card_Om`: |Ω| ≥ (15/16)·|𝔽|⁴.
* `card_Om_lt`, `part_a`, `part_b`, `part_c`: |Ω| < (32m)⁴ and the parts (a), (b), (c) of the lemma.
* `lemFamily`: Lemma 13 without its claim that the sets can be listed in time polynomial in m (that
  claim is `VariableBound.Fld.StCertFamD`, proof/variables/VariableBound/Field/Defs.lean), with 0 < |Ω|
  added. -/

public section

namespace VariableBound

open Finset AppVariables VariableBound.Pairwise

namespace Family

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {m s : ℕ}

omit [Field F] [DecidableEq F] [Algebra (ZMod 2) F] in
/-- Proof of Lemma 13 (Family of checks): (u₃, u₄) is independent of (u₁, u₂). The quadruples u with
a property of the two pairs are counted pair by pair. -/
theorem card_quad (R : F × F → F × F → Prop) [∀ p r, Decidable (R p r)] :
    #{u : F × F × F × F | R (u.1, u.2.1) (u.2.2.1, u.2.2.2)} = ∑ p : F × F, #{r : F × F | R p r} := by
  simp_rw [card_filter]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine sum_congr rfl fun u₁ _ => ?_
  rw [Fintype.sum_prod_type]

omit [Field F] [DecidableEq F] [Algebra (ZMod 2) F] in
/-- 𝔽⁴ has |𝔽|⁴ elements. -/
theorem card_univ_quad : #(univ : Finset (F × F × F × F)) = Fintype.card F ^ 4 := by
  simp only [card_univ, Fintype.card_prod]
  ring

omit [Fintype F] [DecidableEq F] in
/-- A clause E lies in Γ_u if and only if H_E holds for the pair (u₁, u₂) and ⟨u₃^E, u₄⟩ = 1 for the
pair (u₃, u₄). This is the definition of Γ_u, written with the two pairs. -/
theorem mem_Gam (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (u : F × F × F × F) (E : Fin m) :
    E ∈ Gam bits ϑ a u ↔ H bits ϑ a (u.1, u.2.1) E ∧ ip (bits ((u.2.2.1, u.2.2.2).1 ^ E.val)) (bits (u.2.2.1, u.2.2.2).2) = 1 := by
  simp [Gam, H]

/-- Proof of Lemma 13 (Family of checks): |Γ_u ∩ V| is odd with probability at least 2/3 · 15/32 =
5/16, for a set V of more than v = 2^a clauses, if 1 ≤ a, a − 1 ≤ s and 16m ≤ 2^s:
16 times the number of these u is at least 5·|𝔽|⁴. -/
theorem card_odd (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (h16 : 16 * m ≤ 2 ^ s)
    (V : Finset (Fin m)) (hV : 2 ^ a < #V) :
    5 * Fintype.card F ^ 4 ≤ 16 * #{u : F × F × F × F | Odd #(Gam bits ϑ a u ∩ V)} := by
  have h1 : ∀ u : F × F × F × F, Gam bits ϑ a u ∩ V
      = {E ∈ {E ∈ V | H bits ϑ a (u.1, u.2.1) E} | ip (bits ((u.2.2.1, u.2.2.2).1 ^ E.val)) (bits (u.2.2.1, u.2.2.2).2) = 1} := by
    intro u
    ext E
    rw [mem_inter, mem_Gam, mem_filter, mem_filter]
    tauto
  simp_rw [h1]
  rw [card_quad fun p r => Odd #{E ∈ {E ∈ V | H bits ϑ a p E} | ip (bits (r.1 ^ E.val)) (bits r.2) = 1}]
  have h2 := second_moment bits ϑ a ha1 ha V hV
  set A : Finset (F × F) := {p : F × F | ∃ E ∈ V, H bits ϑ a p E} with hA
  have h3 : #A * (15 * Fintype.card F ^ 2)
      ≤ 32 * ∑ p : F × F, #{r : F × F | Odd #{E ∈ {E ∈ V | H bits ϑ a p E} | ip (bits (r.1 ^ E.val)) (bits r.2) = 1}} := by
    rw [mul_sum, ← smul_eq_mul, ← sum_const]
    refine (sum_le_sum fun p hp => SmallBias.small_bias bits h16 {E ∈ V | H bits ϑ a p E} ?_).trans (sum_le_sum_of_subset (subset_univ A))
    obtain ⟨E, hE, hH⟩ := (mem_filter.1 hp).2
    exact ⟨E, mem_filter.2 ⟨hE, hH⟩⟩
  generalize (∑ p : F × F, #{r : F × F | Odd #{E ∈ {E ∈ V | H bits ϑ a p E} | ip (bits (r.1 ^ E.val)) (bits r.2) = 1}}) = N at *
  have h4 : 2 * Fintype.card F ^ 2 * (15 * Fintype.card F ^ 2) ≤ 3 * #A * (15 * Fintype.card F ^ 2) := Nat.mul_le_mul_right _ h2.le
  have h5 : Fintype.card F ^ 4 = Fintype.card F ^ 2 * Fintype.card F ^ 2 := by ring
  rw [h5]
  generalize Fintype.card F ^ 2 = Q at *
  generalize hQQ : Q * Q = QQ at *
  have h6 : 2 * Q * (15 * Q) = 30 * QQ := by rw [← hQQ]; ring
  have h7 : 3 * #A * (15 * Q) = 3 * (#A * (15 * Q)) := by ring
  omega

/-- Proof of Lemma 13 (Family of checks): a clause lies in Γ_u with probability at most 1/v, v =
2^a, if 1 ≤ a and a − 1 ≤ s: v times the number of these u is at most |𝔽|⁴. -/
theorem card_mem (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (E : Fin m) :
    2 ^ a * #{u : F × F × F × F | E ∈ Gam bits ϑ a u} ≤ Fintype.card F ^ 4 := by
  simp_rw [mem_Gam]
  rw [card_quad fun p r => H bits ϑ a p E ∧ ip (bits (r.1 ^ E.val)) (bits r.2) = 1]
  have h1 : ∀ p : F × F, #{r : F × F | H bits ϑ a p E ∧ ip (bits (r.1 ^ E.val)) (bits r.2) = 1}
      = if H bits ϑ a p E then #{r : F × F | ip (bits (r.1 ^ E.val)) (bits r.2) = 1} else 0 := by
    intro p
    by_cases h : H bits ϑ a p E <;> simp [h]
  simp_rw [h1]
  rw [← sum_filter, sum_const, smul_eq_mul]
  calc 2 ^ a * (#{p : F × F | H bits ϑ a p E} * #{r : F × F | ip (bits (r.1 ^ E.val)) (bits r.2) = 1})
      = (2 ^ (a - 1) * #{p : F × F | H bits ϑ a p E}) * (2 * #{r : F × F | ip (bits (r.1 ^ E.val)) (bits r.2) = 1}) := by
        rw [show 2 ^ a = 2 ^ (a - 1) * 2 by rw [← pow_succ, Nat.sub_add_cancel ha1]]
        ring
    _ ≤ Fintype.card F ^ 2 * Fintype.card F ^ 2 := by
        rw [card_H bits ϑ a ha E]
        exact Nat.mul_le_mul_left _ (SmallBias.half bits E)
    _ = Fintype.card F ^ 4 := by ring

/-- Proof of Lemma 13 (Family of checks): |Γ_u| > 16m/v with probability at most 1/16, v = 2^a, if 1
≤ a, a − 1 ≤ s and 1 ≤ m: 16 times the number of these u is at most |𝔽|⁴. -/
theorem markov (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (hm : 1 ≤ m) :
    16 * #{u : F × F × F × F | ¬ 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m} ≤ Fintype.card F ^ 4 := by
  have h1 : ∑ u : F × F × F × F, 2 ^ a * #(Gam bits ϑ a u) ≤ m * Fintype.card F ^ 4 := by
    have h2 : ∀ u : F × F × F × F, #(Gam bits ϑ a u) = ∑ E : Fin m, if E ∈ Gam bits ϑ a u then 1 else 0 := by
      intro u
      simp
    simp_rw [h2]
    rw [← mul_sum, sum_comm, mul_sum]
    simp_rw [← card_filter]
    refine (sum_le_sum fun E _ => card_mem bits ϑ a ha1 ha E).trans ?_
    simp
  have h3 : #{u : F × F × F × F | ¬ 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m} * (16 * m) ≤ ∑ u : F × F × F × F, 2 ^ a * #(Gam bits ϑ a u) := by
    rw [← smul_eq_mul, ← sum_const]
    refine (sum_le_sum fun u hu => ?_).trans (sum_le_sum_of_subset (subset_univ _))
    exact (not_le.1 (mem_filter.1 hu).2).le
  refine Nat.le_of_mul_le_mul_right ?_ hm
  calc 16 * #{u : F × F × F × F | ¬ 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m} * m
      = #{u : F × F × F × F | ¬ 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m} * (16 * m) := by ring
    _ ≤ m * Fintype.card F ^ 4 := h3.trans h1
    _ = Fintype.card F ^ 4 * m := by ring

omit [DecidableEq F] in
/-- Ω and the set of the u with |Γ_u| > 16m/v together are 𝔽⁴. -/
theorem card_Om_add (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) :
    #(Om bits ϑ a) + #{u : F × F × F × F | ¬ 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m} = Fintype.card F ^ 4 := by
  rw [Om, card_filter_add_card_filter_not, card_univ_quad]

/-- Proof of Lemma 13 (Family of checks): |Ω| ≥ (15/16)·|𝔽|⁴, if 1 ≤ a, a − 1 ≤ s and 1 ≤ m. -/
theorem card_Om (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (hm : 1 ≤ m) :
    15 * Fintype.card F ^ 4 ≤ 16 * #(Om bits ϑ a) := by
  have h1 := markov bits ϑ a ha1 ha hm
  have h2 := card_Om_add bits ϑ a
  omega

omit [DecidableEq F] in
/-- Lemma 13 (Family of checks): |Ω| < (32m)⁴, if 2^s < 32m, because |Ω| ≤ |𝔽|⁴ = 2^(4s). -/
theorem card_Om_lt (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (h32 : 2 ^ s < 32 * m) : #(Om bits ϑ a) < (32 * m) ^ 4 :=
  calc #(Om bits ϑ a) ≤ Fintype.card F ^ 4 := (Nat.le_add_right _ _).trans_eq (card_Om_add bits ϑ a)
    _ = (2 ^ s) ^ 4 := by rw [card_F bits]
    _ < (32 * m) ^ 4 := Nat.pow_lt_pow_left h32 (by norm_num)

omit [DecidableEq F] in
/-- Lemma 13 (Family of checks), part (a): |Γ_u| ≤ 16m/v for all u ∈ Ω, v = 2^a. This is the
definition of Ω. -/
theorem part_a (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (u : F × F × F × F) (hu : u ∈ Om bits ϑ a) :
    2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m :=
  (mem_filter.1 hu).2

/-- Lemma 13 (Family of checks), part (b): every clause lies in Γ_u for at most (16/(15v))·|Ω|
indices u ∈ Ω, v = 2^a, if 1 ≤ a, a − 1 ≤ s and 1 ≤ m. -/
theorem part_b (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (hm : 1 ≤ m) (E : Fin m) :
    15 * 2 ^ a * #{u ∈ Om bits ϑ a | E ∈ Gam bits ϑ a u} ≤ 16 * #(Om bits ϑ a) := by
  have h : #{u ∈ Om bits ϑ a | E ∈ Gam bits ϑ a u} ≤ #{u : F × F × F × F | E ∈ Gam bits ϑ a u} :=
    card_le_card (filter_subset_filter _ (subset_univ _))
  calc 15 * 2 ^ a * #{u ∈ Om bits ϑ a | E ∈ Gam bits ϑ a u} = 15 * (2 ^ a * #{u ∈ Om bits ϑ a | E ∈ Gam bits ϑ a u}) := by ring
    _ ≤ 15 * (2 ^ a * #{u : F × F × F × F | E ∈ Gam bits ϑ a u}) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h)
    _ ≤ 15 * Fintype.card F ^ 4 := Nat.mul_le_mul_left _ (card_mem bits ϑ a ha1 ha E)
    _ ≤ 16 * #(Om bits ϑ a) := card_Om bits ϑ a ha1 ha hm

/-- Lemma 13 (Family of checks), part (c): for every set V of more than v = 2^a clauses, |Γ_u ∩ V|
is odd for at least |Ω|/4 indices u ∈ Ω, if 1 ≤ a, a − 1 ≤ s, 1 ≤ m and 16m ≤ 2^s;
because 5/16 − 1/16 = 1/4. -/
theorem part_c (bits : F ≃ₗ[ZMod 2] (Fin s → ZMod 2)) (ϑ : Fin m ↪ F) (a : ℕ) (ha1 : 1 ≤ a) (ha : a - 1 ≤ s) (hm : 1 ≤ m) (h16 : 16 * m ≤ 2 ^ s)
    (V : Finset (Fin m)) (hV : 2 ^ a < #V) :
    #(Om bits ϑ a) ≤ 4 * #{u ∈ Om bits ϑ a | Odd #(Gam bits ϑ a u ∩ V)} := by
  have h1 := card_odd bits ϑ a ha1 ha h16 V hV
  have h2 : #{u : F × F × F × F | Odd #(Gam bits ϑ a u ∩ V)}
      ≤ #{u ∈ Om bits ϑ a | Odd #(Gam bits ϑ a u ∩ V)} + #{u : F × F × F × F | ¬ 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m} := by
    rw [← card_filter_add_card_filter_not (s := {u : F × F × F × F | Odd #(Gam bits ϑ a u ∩ V)}) fun u => 2 ^ a * #(Gam bits ϑ a u) ≤ 16 * m]
    refine Nat.add_le_add (card_le_card fun u hu => ?_) (card_le_card fun u hu => ?_)
    · simp only [mem_filter, mem_univ, true_and, Om] at hu ⊢
      exact ⟨hu.2, hu.1⟩
    · simp only [mem_filter, mem_univ, true_and] at hu ⊢
      exact hu.2
  have h3 := markov bits ϑ a ha1 ha hm
  have h4 := card_Om_add bits ϑ a
  omega

end Family

open Family in
/-- Lemma 13 (Family of checks), without its claim that the sets can be listed in time polynomial in
m: for v = 2^a with 2 ≤ v ≤ m and a field 𝔽 with 2^s elements, 16m ≤ 2^s < 32m, the sets Γ_u, u ∈ Ω,
have 0 < |Ω| < (32m)⁴ and (a), (b), (c). -/
theorem lemFamily : AppVariables.LemFamily := by
  intro F _ _ _ _ m s a bits ϑ ha1 hvm h16 h32
  have hm : 1 ≤ m := Nat.one_le_two_pow.trans hvm
  have ha : a - 1 ≤ s := by
    have h : 2 ^ a < 2 ^ s := by omega
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 h
    omega
  refine ⟨?_, card_Om_lt bits ϑ a h32, ?_, part_b bits ϑ a ha1 ha hm, part_c bits ϑ a ha1 ha hm h16⟩
  · have h1 := card_Om bits ϑ a ha1 ha hm
    have h2 : 0 < Fintype.card F ^ 4 := pow_pos Fintype.card_pos 4
    omega
  · intro u hu
    rw [Fintype.card_fin]
    exact part_a bits ϑ a u hu

end VariableBound
