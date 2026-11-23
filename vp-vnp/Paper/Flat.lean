/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Alternative
import Paper.Grids
import Nc.CaseI.Lower
import Nc.Vp.Main

/-!
# The paper, section "The flat case"
-/

namespace Paper

open Finset MvPolynomial Nc Nc.Price Nc.CaseI Ov

/-! ### The polynomial of the complete network -/

/-- The polynomial f_{k,ℓ}: the sum over the strings σ on the pairs of the product of the variables x_{a,σ_a}; and as a
tensor on the ends it is the product of the wires on the pairs. -/
theorem fkl_eq (F : Type) [Field F] (k ℓ : ℕ) :
    fkl F k ℓ = ∑ σ : Pr k → Fin ℓ → Bool, ∏ a, X (a, asm (fun e _ => σ e) a) ∧
      ∀ x : Pr k → Fin 2 → Fin ℓ → Bool, cf univ (fkl F k ℓ) (asm x) = if ∀ e, x e 0 = x e 1 then 1 else 0 :=
  ⟨rfl, cf_fkl⟩

/-- The other end of a pair. -/
def pairOf {k : ℕ} (a b : Fin k) (h : b ≠ a) : Pr k :=
  if hab : a < b then ⟨(a, b), hab⟩ else ⟨(b, a), lt_of_le_of_ne (not_lt.1 hab) h⟩

theorem asm_pairOf {k ℓ : ℕ} (σ : Pr k → Fin ℓ → Bool) (a b : Fin k) (h : b ≠ a) :
    asm (fun e _ => σ e) a b = σ (pairOf a b h) := by
  unfold asm pairOf
  split_ifs with h1 h2
  · rfl
  · rfl
  · exact absurd (le_antisymm (not_lt.1 h1) (not_lt.1 h2)) h

theorem asm_self {k ℓ : ℕ} (σ : Pr k → Fin ℓ → Bool) (a : Fin k) :
    asm (fun e _ => σ e) a a = fun _ => false := by
  simp [asm]

/-- A value of σ_a: a table with no string for a itself. -/
abbrev Val (k ℓ : ℕ) := {κ : Fin k × Ix k ℓ // κ.2 κ.1 = fun _ => false}

/-- The literals of the clause σ_a = ρ. -/
noncomputable def fklLits {k ℓ : ℕ} (κ : Val k ℓ) : List ((Pr k × Fin ℓ) × Bool) :=
  (univ : Finset ({b : Fin k // b ≠ κ.1.1} × Fin ℓ)).toList.map fun p =>
    ((pairOf κ.1.1 p.1.1 p.1.2, p.2), κ.1.2 p.1.1 p.2)

/-- The weight x_{a,ρ} of the clause σ_a = ρ. -/
noncomputable def fklWt (F : Type) [Field F] {k ℓ : ℕ} (κ : Val k ℓ) : MvPolynomial (Fin k × Ix k ℓ) F := X κ.1

theorem forall_fklLits {k ℓ : ℕ} (κ : Val k ℓ) (x : Pr k × Fin ℓ → Bool) :
    (∀ l ∈ fklLits κ, x l.1 = l.2) ↔ asm (fun e _ i => x (e, i)) κ.1.1 = κ.1.2 := by
  obtain ⟨⟨a, t⟩, ht⟩ := κ
  constructor
  · intro h
    funext b
    by_cases hb : b = a
    · subst hb
      exact (asm_self (fun e i => x (e, i)) b).trans ht.symm
    · refine (asm_pairOf (fun e i => x (e, i)) a b hb).trans (funext fun i => ?_)
      exact h ((pairOf a b hb, i), t b i) (List.mem_map.2 ⟨(⟨b, hb⟩, i), by simp, rfl⟩)
  · intro h l hl
    obtain ⟨⟨⟨b, hb⟩, i⟩, -, rfl⟩ := List.mem_map.1 hl
    show x (pairOf a b hb, i) = t b i
    exact (congrFun (asm_pairOf (fun e i => x (e, i)) a b hb) i).symm.trans
      (congrFun (congrFun (h : asm (fun e _ i => x (e, i)) a = t) b) i)

/-- "It is the clause sum over the bits of σ in which, for every a and every value ρ of σ_a, the clause saying σ_a = ρ
has the weight x_{a,ρ}." -/
theorem lem_fkl_perm_clauseSum (F : Type) [Field F] (k ℓ : ℕ) :
    clauseSum (fklLits (k := k) (ℓ := ℓ)) (fklWt F) = fkl F k ℓ := by
  classical
  unfold clauseSum fkl
  refine Fintype.sum_equiv (Equiv.curry (Pr k) (Fin ℓ) Bool) _ _ fun x => ?_
  simp only [forall_fklLits, fklWt]
  rw [← Finset.prod_filter]
  refine Finset.prod_bij' (fun κ _ => κ.1.1)
    (fun a _ => ⟨(a, asm (fun e _ i => x (e, i)) a), asm_self (fun e i => x (e, i)) a⟩) ?_ ?_ ?_ ?_ ?_
  · intros
    exact mem_univ _
  · intro a _
    exact mem_filter.2 ⟨mem_univ _, rfl⟩
  · intro κ hκ
    exact Subtype.ext (Prod.ext rfl (mem_filter.1 hκ).2)
  · intros
    rfl
  · intro κ hκ
    exact congrArg X (Prod.ext rfl (mem_filter.1 hκ).2.symm)

theorem fklLits_ne {k ℓ : ℕ} (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) (κ : Val k ℓ) : fklLits κ ≠ [] := by
  have h1 : Fintype.card {b : Fin k // b ≠ κ.1.1} = k - 1 := by simp
  have h2 : 0 < (fklLits κ).length := by
    simp only [fklLits, List.length_map, Finset.length_toList, card_univ, Fintype.card_prod, h1, Fintype.card_fin]
    exact Nat.mul_pos (by omega) (by omega)
  exact List.length_pos_iff.1 h2

theorem fklLits_occ {k ℓ : ℕ} (b : Pr k × Fin ℓ) : ∃ κ : Val k ℓ, ∃ l ∈ fklLits κ, l.1 = b := by
  obtain ⟨⟨⟨a, c⟩, hac⟩, i⟩ := b
  refine ⟨⟨(a, fun _ _ => false), rfl⟩, ((pairOf a c (ne_of_gt hac), i), false),
    List.mem_map.2 ⟨(⟨c, ne_of_gt hac⟩, i), by simp, rfl⟩, ?_⟩
  simp only [pairOf, dif_pos (show a < c from hac)]

theorem fklLits_count {k ℓ : ℕ} (hk : 2 ≤ k) : ∑ κ : Val k ℓ, (fklLits κ).length ≤ k ^ 3 * ℓ * 2 ^ (k * ℓ) := by
  have h1 : ∀ κ : Val k ℓ, (fklLits κ).length ≤ k * ℓ := fun κ => by
    simp only [fklLits, List.length_map, Finset.length_toList, card_univ, Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ ((Fintype.card_subtype_le _).trans_eq (Fintype.card_fin k))
  have h2 : Fintype.card (Val k ℓ) ≤ k * 2 ^ (k * ℓ) := by
    refine (Fintype.card_subtype_le _).trans (le_of_eq ?_)
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    rw [← pow_mul, mul_comm ℓ k]
  calc ∑ κ : Val k ℓ, (fklLits κ).length ≤ ∑ _κ : Val k ℓ, k * ℓ := Finset.sum_le_sum fun κ _ => h1 κ
    _ = Fintype.card (Val k ℓ) * (k * ℓ) := by rw [sum_const, card_univ, smul_eq_mul]
    _ ≤ k * 2 ^ (k * ℓ) * (k * ℓ) := Nat.mul_le_mul_right _ h2
    _ = k ^ 2 * ℓ * 2 ^ (k * ℓ) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega)))

/-- The form of Lemma lem:fkl-perm for every family that is complete for grid sums: if M ≥ κk³ℓ2^(kℓ), then f_{k,ℓ} is a
projection of G_M with affine entries. -/
theorem fkl_complete {F : Type} [Field F] {G : ∀ M, MvPolynomial (Fin M × Fin M) F} {κ : ℕ}
    (hG : GridComplete F G κ) {k ℓ : ℕ} (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) {M : ℕ}
    (hM : κ * k ^ 3 * ℓ * 2 ^ (k * ℓ) ≤ M) :
    ∃ E : Fin M × Fin M → MvPolynomial (Fin k × Ix k ℓ) F, (∀ q, IsAffine (E q)) ∧ aeval E (G M) = fkl F k ℓ := by
  obtain ⟨E, hE, he⟩ := clauses_of_complete hG fklLits (fklLits_ne hk hℓ) fklLits_occ (fklWt F)
    (fun κ => Or.inl ⟨κ.1, rfl⟩) (S := M) (le_trans (le_trans (Nat.mul_le_mul_left _ (fklLits_count hk))
      (le_of_eq (by ring))) hM)
  exact ⟨E, hE, he.trans (lem_fkl_perm_clauseSum F k ℓ)⟩

/-- **Paper: Lemma lem:fkl-perm.** "If PERM_M has a circuit over k with s gates and M ≥ 3k³ℓ2^(kℓ), then f_{k,ℓ} has
one with 5s gates." (2 ≠ 0 is a standing hypothesis of the section.) -/
theorem lem_fkl_perm {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {k ℓ : ℕ} (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) {S s : ℕ}
    (hS : 3 * k ^ 3 * ℓ * 2 ^ (k * ℓ) ≤ S) (hs : Computes (genPerm F S) s) : Computes (fkl F k ℓ) (5 * s) := by
  obtain ⟨M, hM, hp⟩ := cor_clauses h2 fklLits (fklLits_ne hk hℓ) fklLits_occ (fklWt F)
    (fun κ => Or.inl ⟨κ.1, rfl⟩) (S := S) (le_trans (le_trans (Nat.mul_le_mul_left _ (fklLits_count hk))
      (le_of_eq (by ring))) hS)
  rw [← lem_fkl_perm_clauseSum, ← hp, ← aeval_genPerm]
  exact hs.aeval _ fun q => hM q.1 q.2

/-- f_{k,ℓ} with exactly the variables that occur, k blocks of 2^((k-1)ℓ) variables, as printed. -/
noncomputable def fklExact (F : Type) [Field F] (k ℓ : ℕ) : MvPolynomial (Val k ℓ) F :=
  ∑ σ : Pr k → Fin ℓ → Bool, ∏ a, X ⟨(a, asm (fun e _ => σ e) a), asm_self σ a⟩

theorem rename_fklExact (F : Type) [Field F] (k ℓ : ℕ) : rename Subtype.val (fklExact F k ℓ) = fkl F k ℓ := by
  simp only [fklExact, fkl, map_sum, map_prod, rename_X]

/-- The unused variables of f_{k,ℓ} are harmless: the polynomial with exactly the occurring variables has the same
circuit sizes. -/
theorem fklExact_computes {F : Type} [Field F] {k ℓ s : ℕ} :
    Computes (fklExact F k ℓ) s ↔ Computes (fkl F k ℓ) s := by
  classical
  refine ⟨fun h => rename_fklExact F k ℓ ▸ h.rename Subtype.val, fun h => ?_⟩
  let φ : MvPolynomial (Fin k × Ix k ℓ) F →ₐ[F] MvPolynomial (Val k ℓ) F :=
    aeval fun κ => if h : κ.2 κ.1 = fun _ => false then X ⟨κ, h⟩ else C 0
  have e : φ (fkl F k ℓ) = fklExact F k ℓ := by
    simp only [φ, fkl, fklExact, map_sum, map_prod, aeval_X]
    exact Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun a _ => dif_pos (asm_self σ a)
  obtain ⟨l, hl, j, hj, hje⟩ := h
  refine ⟨fun i => φ (l i), fun i hi => ?_, j, hj, (congrArg φ hje).trans e⟩
  rcases hl i hi with ⟨κ, hx⟩ | ⟨c, hc⟩ | ⟨a, ha, b, hb, hab⟩ | ⟨a, ha, b, hb, hab⟩
  · show IsStep (fun i => φ (l i)) i
    have hv : φ (l i) = if h : κ.2 κ.1 = fun _ => false then X ⟨κ, h⟩ else C 0 := by rw [hx]; simp [φ]
    by_cases h : κ.2 κ.1 = fun _ => false
    · exact Or.inl ⟨⟨κ, h⟩, hv.trans (dif_pos h)⟩
    · exact Or.inr (Or.inl ⟨0, hv.trans (dif_neg h)⟩)
  · exact Or.inr (Or.inl ⟨c, by simp [φ, hc]⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a, ha, b, hb, by simp [hab]⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a, ha, b, hb, by simp [hab]⟩))

/-- **Paper: Lemma lem:fkl-perm**, for f_{k,ℓ} with exactly the printed variables. -/
theorem lem_fkl_perm_printed {F : Type} [Field F] (h2 : (2 : F) ≠ 0) {k ℓ : ℕ} (hk : 2 ≤ k) (hℓ : 1 ≤ ℓ) {S s : ℕ}
    (hS : 3 * k ^ 3 * ℓ * 2 ^ (k * ℓ) ≤ S) (hs : Computes (genPerm F S) s) : Computes (fklExact F k ℓ) (5 * s) :=
  fklExact_computes.2 (lem_fkl_perm h2 hk hℓ hS hs)

/-! ### Balanced products -/

/-- A polynomial that is linear in each block of S and contains no other variables, by its coefficients. -/
noncomputable def linearIn {R T : Type} [CommSemiring R] [Fintype T] {k : ℕ} (S : Finset (Fin k))
    (c : (S → T) → R) : MvPolynomial (Fin k × T) R :=
  ∑ y : S → T, C (c y) * ∏ a : S, X ((a : Fin k), y a)

/-- The part of a polynomial that is linear in each block. -/
noncomputable def linearPart {R T : Type} [CommSemiring R] [Fintype T] [DecidableEq T] {k : ℕ}
    (P : MvPolynomial (Fin k × T) R) : MvPolynomial (Fin k × T) R :=
  ∑ x : Fin k → T, C (cf univ P x) * ∏ a, X (a, x a)

theorem linearPart_cf {R T : Type} [CommSemiring R] [Fintype T] [DecidableEq T] {k : ℕ}
    (c : (Fin k → T) → R) (y : Fin k → T) :
    cf univ (∑ x : Fin k → T, C (c x) * ∏ a, X (a, x a)) y = c y := by
  classical
  have e : ∀ x : Fin k → T, (∏ a, X (a, x a) : MvPolynomial (Fin k × T) R) = monomial (mono univ x) 1 := fun x => by
    rw [mono, monomial_sum_one]
    rfl
  rw [cf, coeff_sum, Finset.sum_eq_single y]
  · rw [e, coeff_C_mul, coeff_monomial, if_pos rfl, mul_one]
  · intro x _ hx
    rw [e, coeff_C_mul, coeff_monomial, if_neg, mul_zero]
    intro h
    refine hx (funext fun a => ?_)
    have h1 := DFunLike.congr_fun h (a, x a)
    rw [mono_apply, mono_apply, if_pos ⟨mem_univ _, rfl⟩] at h1
    by_contra hne
    rw [if_neg fun h2 => hne h2.2.symm] at h1
    exact one_ne_zero' _ h1
  · exact fun h => absurd (mem_univ _) h

/-- A product gh, g linear in each block of S and h in each other block, by its coefficients. -/
theorem linearIn_mul {R T : Type} [CommSemiring R] [Fintype T] [DecidableEq T] {k : ℕ} (S : Finset (Fin k))
    (g : (S → T) → R) (h : ((Sᶜ : Finset (Fin k)) → T) → R) :
    linearIn S g * linearIn Sᶜ h =
      ∑ x : Fin k → T, C (g (fun a => x a) * h fun a => x a) * ∏ a, X (a, x a) := by
  classical
  rw [linearIn, linearIn, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine (Finset.sum_bij' (fun x _ => ((fun a : S => x a), fun a : (Sᶜ : Finset (Fin k)) => x a))
    (fun p _ a => if ha : a ∈ S then p.1 ⟨a, ha⟩ else p.2 ⟨a, mem_compl.2 ha⟩) (fun _ _ => mem_univ _)
    (fun _ _ => mem_univ _) (fun x _ => ?_) (fun p _ => ?_) (fun x _ => ?_)).symm
  · funext a
    by_cases ha : a ∈ S <;> simp [ha]
  · refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
    · simp [a.2]
    · simp [mem_compl.1 a.2]
  · simp only [map_mul]
    rw [← Finset.prod_mul_prod_compl S fun a => (X (a, x a) : MvPolynomial (Fin k × T) R),
      ← Finset.prod_coe_sort S, ← Finset.prod_coe_sort Sᶜ]
    ring

/-- **Paper: Lemma lem:balanced.** "If a polynomial has a circuit with L gates, its part f that is linear in each of
k ≥ 2 blocks of variables of equal size is a sum of products gh: for every set S with k ≤ 3|S| ≤ 2k at most L products
in which g is linear in each block of S, h in each other block, and neither contains other variables." The blocks are
{a} × T, and R is any commutative semiring, so it holds for approximating circuits too. -/
theorem lem_balanced {R T : Type} [CommSemiring R] [Fintype T] [DecidableEq T] {k : ℕ}
    {P : MvPolynomial (Fin k × T) R} {L : ℕ} (h : Computes P L) (hk : 2 ≤ k) :
    ∃ (g : ∀ S : Finset (Fin k), Fin L → (S → T) → R) (q : ∀ S : Finset (Fin k), Fin L → ((Sᶜ : Finset (Fin k)) → T) → R),
      linearPart P = ∑ S ∈ (univ : Finset (Finset (Fin k))).filter (fun S => k ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * k),
        ∑ δ, linearIn S (g S δ) * linearIn Sᶜ (q S δ) := by
  classical
  obtain ⟨l, hl, γ, hγ, rfl⟩ := h
  -- the induction on the circuit, for the output and all blocks
  obtain ⟨q, hq, he⟩ := dec_gate hl hk γ hγ univ (by rw [Finset.card_univ, Fintype.card_fin]; omega)
  rcases isEmpty_or_nonempty T with hT | hT
  · have : IsEmpty (Fin k → T) := ⟨fun x => hT.false (x ⟨0, by omega⟩)⟩
    refine ⟨fun _ _ _ => 0, fun _ _ _ => 0, ?_⟩
    simp [linearPart, linearIn]
  let t₀ : T := Classical.arbitrary T
  let ext : ∀ S : Finset (Fin k), (S → T) → Fin k → T := fun S y a => if ha : a ∈ S then y ⟨a, ha⟩ else t₀
  refine ⟨fun S δ y => cf S (l δ) (ext S y), fun S δ z => q δ S (ext Sᶜ z), ?_⟩
  have hbal : bal (univ : Finset (Fin k)) = univ.filter fun S => k ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * k := by
    ext S
    simp [mem_bal]
  rw [← hbal]
  simp only [linearIn_mul]
  have e1 : ∀ S δ (x : Fin k → T), cf S (l δ) (ext S fun a : S => x a) = cf S (l δ) x := fun S δ x =>
    cf_congr _ fun a ha => by simp [ext, ha]
  have e2 : ∀ S δ (x : Fin k → T), q δ S (ext Sᶜ fun a : (Sᶜ : Finset (Fin k)) => x a) = q δ S x := fun S δ x =>
    hq δ S _ _ fun a ha => by simp [ext, (Finset.mem_sdiff.1 ha).2]
  simp only [e1, e2]
  simp only [linearPart, he, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_comm (s := bal _)]
  exact Finset.sum_congr rfl fun δ _ => Finset.sum_comm

/-- Lemma lem:balanced for the coefficients: the coefficient of ∏ x_{a,y_a} is a sum of products. -/
theorem lem_balanced_cf {R T : Type} [CommSemiring R] [Fintype T] [DecidableEq T] {k : ℕ}
    {P : MvPolynomial (Fin k × T) R} {L : ℕ} (h : Computes P L) (hk : 2 ≤ k) :
    ∃ (g : ∀ S : Finset (Fin k), Fin L → (S → T) → R)
      (q : ∀ S : Finset (Fin k), Fin L → ((Sᶜ : Finset (Fin k)) → T) → R),
      ∀ y, cf univ P y = ∑ S ∈ bal univ, ∑ δ, g S δ (fun a => y a) * q S δ fun a => y a := by
  obtain ⟨g, q, he⟩ := lem_balanced h hk
  refine ⟨g, q, fun y => ?_⟩
  have hbal : bal (univ : Finset (Fin k)) = univ.filter fun S => k ≤ 3 * S.card ∧ 3 * S.card ≤ 2 * k := by
    ext S
    simp [mem_bal]
  rw [← linearPart_cf (fun x => cf univ P x) y, show (∑ x : Fin k → T, C (cf univ P x) * ∏ a, X (a, x a)) =
    linearPart P from rfl, he, ← hbal, cf, coeff_sum]
  simp only [linearIn_mul, coeff_sum]
  exact Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun δ _ => by
    rw [← coeff_sum]; exact linearPart_cf _ y

/-! ### The tensor of f_{k,ℓ} -/

/-- The numbers below 2^ℓ are the strings of ℓ bits. -/
noncomputable def strEquiv (ℓ : ℕ) : Fin (2 ^ ℓ) ≃ (Fin ℓ → Bool) :=
  (Fintype.equivFinOfCardEq (by simp)).symm

/-- The tensor of f_{k,ℓ} on the ends: the product of the wires of dimension 2^ℓ on the pairs. -/
noncomputable def fklTen (K : Type) [Field K] (k ℓ : ℕ) : Ten K (End k) :=
  Ten.outer fun _ : Pr k => Ten.unit K (Fin 2) (2 ^ ℓ)

/-- The strings at the tables for an entry of the tensor. -/
noncomputable def tables {k ℓ : ℕ} (z : End k → Fin (2 ^ ℓ)) : Fin k → Ix k ℓ :=
  asm fun e i => strEquiv ℓ (z ⟨e, i⟩)

/-- "As a tensor on the ends it is the product of the wires on the pairs." -/
theorem fklTen_val (K : Type) [Field K] {k ℓ : ℕ} (z : End k → Fin (2 ^ ℓ)) :
    (fklTen K k ℓ).val z = cf univ (fkl K k ℓ) (tables z) := by
  rw [tables, cf_fkl]
  refine (Ten.outer_val (fun _ : Pr k => Ten.unit K (Fin 2) (2 ^ ℓ)) z).trans ?_
  rw [
    Finset.prod_congr rfl fun e _ => unit_two_val' (strEquiv ℓ) fun i => z ⟨e, i⟩, Finset.prod_ite_zero]
  simp

theorem fklTen_price {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (φ : Spec K I) {k : ℕ} (ℓ : ℕ)
    (π : End k → I) :
    φ.F (Ten.push π (fklTen K k ℓ)) = (2 : ℝ) ^ ((ℓ : ℝ) * ∑ e : Pr k, φ.e (π ⟨e, 0⟩) (π ⟨e, 1⟩)) := by
  rw [fklTen, φ.congr (Ten.Equi.push_outer π _), φ.prod, Finset.mul_sum, Real.rpow_sum_of_pos (by norm_num)]
  refine Finset.prod_congr rfl fun e _ => ?_
  have : (fun i => π ⟨e, i⟩) = ![π ⟨e, 0⟩, π ⟨e, 1⟩] := by
    funext i
    fin_cases i <;> rfl
  rw [this, show Ten.push ![π ⟨e, 0⟩, π ⟨e, 1⟩] (Ten.unit K (Fin 2) (2 ^ ℓ)) =
    Ten.wire K (2 ^ ℓ) (π ⟨e, 0⟩) (π ⟨e, 1⟩) from rfl, φ.wire_eq _ _ Nat.one_le_two_pow,
    Real.rpow_mul (by norm_num)]
  simp

/-- The hub of an end for the set S. -/
def hubOf {I : Type} {k : ℕ} (hub : Finset (Fin k) → Bool → I) (S : Finset (Fin k)) (a : End k) : I :=
  hub S (decide (endNode a.1 a.2 ∈ S))

/-- The product of the wires from the ends to their hubs for S and a wire of dimension L between the hubs. -/
noncomputable def hubTen (K : Type) [Field K] {I : Type} [Fintype I] [DecidableEq I] {k : ℕ} (ℓ L : ℕ)
    (π : End k → I) (hub : Finset (Fin k) → Bool → I) (S : Finset (Fin k)) : Ten K I :=
  Ten.prod (fun a => Ten.wire K (2 ^ ℓ) (π a) (hubOf hub S a)) * Ten.wire K L (hub S true) (hub S false)

/-- What the set S costs: ℓ times the wires from the ends to their hubs, and the wire between the hubs. -/
noncomputable def hubCost {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (φ : Spec K I) {k : ℕ} (ℓ L : ℕ)
    (π : End k → I) (hub : Finset (Fin k) → Bool → I) (S : Finset (Fin k)) : ℝ :=
  ℓ * ∑ e : Pr k, ∑ i, φ.e (π ⟨e, i⟩) (hubOf hub S ⟨e, i⟩) + φ.e (hub S true) (hub S false) * Real.logb 2 L

theorem hubTen_price {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (φ : Spec K I) {k : ℕ} (ℓ : ℕ) {L : ℕ}
    (hL : 1 ≤ L) (π : End k → I) (hub : Finset (Fin k) → Bool → I) (S : Finset (Fin k)) :
    φ.F (hubTen K ℓ L π hub S) = (2 : ℝ) ^ hubCost φ ℓ L π hub S := by
  rw [hubTen, φ.mul, φ.prod, hubCost, Real.rpow_add (by norm_num), φ.wire_eq _ _ hL, Finset.mul_sum,
    Real.rpow_sum_of_pos (by norm_num), mul_comm (φ.e _ _), Real.rpow_mul (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hL), Fintype.prod_sigma]
  refine congrArg₂ _ (Finset.prod_congr rfl fun e _ => ?_) rfl
  rw [Finset.mul_sum, Real.rpow_sum_of_pos (by norm_num)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [φ.wire_eq _ _ Nat.one_le_two_pow, Real.rpow_mul (by norm_num)]
  simp

/-- "By Lemma lem:balanced the tensor of f_{k,ℓ} is a sum of at most 2^k tensors, one for each S, each of which Lemma
lem:hubs leads through ±o_S with a wire of dimension L between them." (At most 2^k: card_bal_le.) The tensor here is that of the part linear in
each block of any polynomial with L gates. -/
theorem prop_flat_lower_sum {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] {k : ℕ} (hk : 2 ≤ k)
    {ℓ L : ℕ} {P : MvPolynomial (Fin k × Ix k ℓ) K} (hP : Computes P L) (π : End k → I)
    (hub : Finset (Fin k) → Bool → I) :
    Ten.SumRestr (Ten.push π ((fklTen K k ℓ).withVal fun z => cf univ P (tables z)))
      fun S : bal (univ : Finset (Fin k)) => hubTen K ℓ L π hub S := by
  classical
  obtain ⟨g, q, he⟩ := lem_balanced_cf hP hk
  let part : bal (univ : Finset (Fin k)) → (End k → Fin (2 ^ ℓ)) → K := fun S z =>
    ∑ δ, g S.1 δ (fun a => tables z a) * q S.1 δ fun a => tables z a
  have hsum : Ten.SumRestr ((fklTen K k ℓ).withVal fun z => cf univ P (tables z))
      fun S => ((fklTen K k ℓ).withVal fun z => cf univ P (tables z)).withVal (part S) :=
    Ten.SumRestr.of_withVal _ _ fun z => (he (tables z)).trans (Finset.sum_coe_sort _ _).symm
  refine (hsum.push π).mono fun S => ?_
  have hcongr : ∀ (z z' : End k → Fin (2 ^ ℓ)) (a : Fin k),
      (∀ x : End k, endNode x.1 x.2 = a → z x = z' x) → tables z a = tables z' a := fun z z' a h =>
    asm_congr fun e i hei => by rw [h ⟨e, i⟩ hei]
  have h := lem_hubs π ((fklTen K k ℓ).withVal (part S)) (fun x => endNode x.1 x.2 ∈ S.1)
    (fun δ z => g S.1 δ fun a => tables z a) (fun δ z => q S.1 δ fun a => tables z a)
    (fun δ z z' hz => congrArg (g S.1 δ) (funext fun a => hcongr z z' a fun x hx => hz x (hx ▸ a.2)))
    (fun δ z z' hz => congrArg (q S.1 δ)
      (funext fun a => hcongr z z' a fun x hx => hz x (hx ▸ mem_compl.1 a.2)))
    (fun z => rfl) (hub S.1 true) (hub S.1 false)
  refine h.trans ?_
  refine Eq.subst (motive := fun t => Ten.Restr t _) ?_ (Ten.Restr.refl _)
  unfold hubTen
  congr 2
  funext a
  rw [show Fintype.card (((fklTen K k ℓ).withVal (part S)).ι a) = 2 ^ ℓ from Fintype.card_fin _]
  congr 1
  unfold hubOf
  split_ifs with ha <;> simp [ha]

theorem card_bal_le (k : ℕ) : Fintype.card (bal (univ : Finset (Fin k))) ≤ 2 ^ k := by
  have h1 := Fintype.card_subtype_le (fun S => S ∈ bal (univ : Finset (Fin k)))
  simpa using h1

theorem bal_nonempty {k : ℕ} (hk : 2 ≤ k) : Nonempty (bal (univ : Finset (Fin k))) := by
  have hc : #(univ.filter fun a : Fin k => a.1 < k / 2) = k / 2 := by
    rw [Fin.card_filter_val_lt]
    omega
  exact ⟨⟨_, mem_bal.2 ⟨Finset.subset_univ (univ.filter fun a : Fin k => a.1 < k / 2), by rw [hc]; omega,
    by rw [hc]; omega⟩⟩⟩

/-! ### The lower bound -/

/-- The estimate of the proof of Proposition prop:flat-lower: with the ends at ½u_{ab}, the hubs ±o of length 1/(6√k)
can be chosen so that "the lengths add up to at most N − k/12". -/
theorem prop_flat_lower_lengths {k : ℕ} (hk : 1 ≤ k) (A : Finset (Fin k)) (h1 : k ≤ 3 * A.card) (h2 : 3 * A.card ≤ 2 * k) :
    ∃ x : EuclideanSpace ℝ (Fin k), ‖x‖ = 1 / (6 * √k) ∧
      ∑ a, ∑ b, (if a = b then 0 else dist (pvec a b) (if a ∈ A then x else -x)) ≤
        (k : ℝ) * (k - 1) / 2 - k / 12 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs1 : (k : ℝ) ≤ 3 * A.card := by exact_mod_cast h1
  have hs2 : 3 * (A.card : ℝ) ≤ 2 * k := by exact_mod_cast h2
  set s : ℝ := ((A.card : ℕ) : ℝ) with hs
  have hsk : 2 / 9 * (k : ℝ) ^ 2 ≤ s * (k - s) := by nlinarith
  have hQ : 2 / 9 * (k : ℝ) ^ 3 ≤ qnum A := by
    have e : (2 : ℝ) / 9 * (k : ℝ) ^ 3 = 2 / 9 * (k : ℝ) ^ 2 * k := by ring
    rw [qnum, e]
    exact mul_le_mul_of_nonneg_right hsk hk0.le
  have hQ0 : 0 < qnum A := lt_of_lt_of_le (by positivity) hQ
  set η : ℝ := 1 / (6 * √k) with hη
  have hη0 : 0 < η := by positivity
  have hηsq : η ^ 2 = 1 / (36 * k) := by
    rw [hη, div_pow, mul_pow, Real.sq_sqrt hk0.le]
    norm_num
  set z : ℝ := η / √(qnum A) with hz
  have hz0 : 0 < z := by positivity
  have hnorm : ‖z • vvec A‖ = η := by
    have h3 : ‖vvec A‖ = √(qnum A) := by rw [← norm_vvec, Real.sqrt_sq (norm_nonneg _)]
    rw [norm_smul, h3, Real.norm_of_nonneg hz0.le, hz]
    exact div_mul_cancel₀ _ (Real.sqrt_pos.2 hQ0).ne'
  refine ⟨z • vvec A, hnorm, ?_⟩
  have hterm : ∀ a b, (if a = b then 0 else dist (pvec a b) (if a ∈ A then z • vvec A else -(z • vvec A))) ≤
      (if a = b then (0 : ℝ) else 1 / 2 + η ^ 2) -
        z * (√2)⁻¹ * (sg A a * (vvec A a - vvec A b)) := by
    intro a b
    by_cases hab : a = b
    · rw [if_pos hab, if_pos hab, hab]
      simp
    · rw [if_neg hab, if_neg hab, pvec]
      have h4 := dist_half_le (norm_uvec hab) (if a ∈ A then z • vvec A else -(z • vvec A))
      refine h4.trans (le_of_eq ?_)
      rw [sg]
      split_ifs with ha
      · rw [real_inner_smul_right, inner_uvec, hnorm]
        ring
      · rw [inner_neg_right, real_inner_smul_right, inner_uvec, norm_neg, hnorm]
        ring
  have h5 : ∑ a : Fin k, ∑ b : Fin k, (if a = b then (0 : ℝ) else 1 / 2 + η ^ 2) =
      k * (k - 1) * (1 / 2 + η ^ 2) := by
    have h6 : ∀ a : Fin k, ∑ b : Fin k, (if a = b then (0 : ℝ) else 1 / 2 + η ^ 2) =
        (k - 1) * (1 / 2 + η ^ 2) := by
      intro a
      have h7 : ∀ b : Fin k, (if a = b then (0 : ℝ) else 1 / 2 + η ^ 2) =
          (1 / 2 + η ^ 2) - if a = b then (1 / 2 + η ^ 2) else 0 := by
        intro b
        split_ifs <;> ring
      simp only [h7]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ _), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    simp only [h6]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  refine (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b).trans ?_
  simp only [Finset.sum_sub_distrib]
  rw [h5]
  have h8 : ∑ a, ∑ b, z * (√2)⁻¹ * (sg A a * (vvec A a - vvec A b)) = z * (√2)⁻¹ * (2 * qnum A) := by
    rw [← sum_sg, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [Finset.mul_sum]
  rw [h8]
  -- the saving
  have h9 : k / 9 ≤ z * (√2)⁻¹ * (2 * qnum A) := by
    have e1 : z * (√2)⁻¹ * (2 * qnum A) = η * √(2 * qnum A) := by
      have hq : qnum A = √(qnum A) * √(qnum A) := (Real.mul_self_sqrt hQ0.le).symm
      have ht : (2 : ℝ) = √2 * √2 := (Real.mul_self_sqrt (by norm_num)).symm
      rw [Real.sqrt_mul (by norm_num), hz]
      have h2' : √2 ≠ 0 := by positivity
      have hq' : √(qnum A) ≠ 0 := by positivity
      field_simp
      nlinarith [Real.sq_sqrt hQ0.le, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [e1]
    have e2 : 2 / 3 * k * √k ≤ √(2 * qnum A) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [mul_pow, mul_pow, Real.sq_sqrt hk0.le]
      nlinarith
    calc (k : ℝ) / 9 = η * (2 / 3 * k * √k) := by
          rw [hη]
          have : √(k : ℝ) ≠ 0 := by positivity
          field_simp
          norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left e2 hη0.le
  have h10 : (k : ℝ) * (k - 1) * η ^ 2 ≤ k / 36 := by
    rw [hηsq]
    have : (k : ℝ) * (k - 1) * (1 / (36 * k)) = (k - 1) / 36 := by field_simp
    rw [this]
    linarith
  nlinarith


/-- The end (a, b) or (b, a) of a pair. -/
noncomputable def lowerPos {k : ℕ} (a : End k) : EuclideanSpace ℝ (Fin k) :=
  if a.2 = 0 then pvec a.1.1.1 a.1.1.2 else pvec a.1.1.2 a.1.1.1

/-- **Paper: Proposition prop:flat-lower.** "In the flat case, for every k ≥ 2 there is ℓ₀ such that for ℓ ≥ ℓ₀ every
circuit over k for f_{k,ℓ} has at least 2^(ℓk^(3/2)/6) gates." -/
theorem prop_flat_lower {K : Type} [Field K] (hK : Flat K) {k : ℕ} (hk : 2 ≤ k) :
    ∃ ℓ₀ : ℕ, ∀ ℓ, ℓ₀ ≤ ℓ → ∀ s : ℕ, Computes (fkl K k ℓ) s →
      (2 : ℝ) ^ ((ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 6) ≤ s := by
  classical
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hhub : ∀ A : Finset (Fin k), ∃ x : EuclideanSpace ℝ (Fin k), A ∈ bal (univ : Finset (Fin k)) →
      ‖x‖ = 1 / (6 * √k) ∧
      ∑ a, ∑ b, (if a = b then 0 else dist (pvec a b) (if a ∈ A then x else -x)) ≤
        (k : ℝ) * (k - 1) / 2 - k / 12 := by
    intro A
    by_cases hA : A ∈ bal (univ : Finset (Fin k))
    · obtain ⟨-, h1, h2⟩ := mem_bal.1 hA
      obtain ⟨x, hx⟩ := prop_flat_lower_lengths (by omega) A h1 h2
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hA⟩
  choose x hx using hhub
  let pos : RPt k → EuclideanSpace ℝ (Fin k) := Sum.elim lowerPos fun z => if z.2 then x z.1 else -x z.1
  set δ : ℝ := 1 / (150 * k) with hδ
  obtain ⟨φ, c, hc, hφ⟩ := (hK k (RPt k) pos).exists_spec id (show 0 < δ by positivity)
  obtain ⟨ℓ₀, hℓ₀⟩ := exists_nat_ge (100 * c)
  refine ⟨ℓ₀, fun ℓ hℓ s hcomp => ?_⟩
  have hs : 1 ≤ s := by
    obtain ⟨l, -, a, ha, -⟩ := hcomp
    omega
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hlog : 0 ≤ Real.logb 2 s := Real.logb_nonneg (by norm_num) (by exact_mod_cast hs)
  -- apply φ to the sum and take the largest term
  let π : End k → RPt k := Sum.inl
  let hub : Finset (Fin k) → Bool → RPt k := fun S b => Sum.inr (S, b)
  have hsum := prop_flat_lower_sum hk hcomp π hub
  rw [show ((fklTen K k ℓ).withVal fun z => cf univ (fkl K k ℓ) (tables z)) = fklTen K k ℓ from
    congrArg _ (funext fun z => (fklTen_val K z).symm)] at hsum
  have := bal_nonempty hk
  obtain ⟨A, -, hA⟩ := Finset.exists_max_image (univ : Finset (bal (univ : Finset (Fin k))))
    (fun S => hubCost φ ℓ s π hub S) univ_nonempty
  have key : (2 : ℝ) ^ ((ℓ : ℝ) * ∑ e : Pr k, φ.e (π ⟨e, 0⟩) (π ⟨e, 1⟩)) ≤
      2 ^ ((k : ℝ) + hubCost φ ℓ s π hub A) := by
    rw [← fklTen_price φ ℓ π]
    refine (φ.le_sum _ _ hsum).trans ?_
    calc ∑ S, φ.F (hubTen K ℓ s π hub S.1) ≤ ∑ _S : bal (univ : Finset (Fin k)), (2 : ℝ) ^ hubCost φ ℓ s π hub A :=
          Finset.sum_le_sum fun S hS => by
            rw [hubTen_price φ ℓ hs]
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (hA S hS)
      _ = Fintype.card (bal (univ : Finset (Fin k))) * (2 : ℝ) ^ hubCost φ ℓ s π hub A := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ _ := by
          rw [Real.rpow_add (by norm_num), Real.rpow_natCast]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_bal_le k) (by positivity)
  have h1 := (Real.rpow_le_rpow_left_iff (show (1 : ℝ) < 2 by norm_num)).1 key
  obtain ⟨hxn, hxs⟩ := hx A A.2
  set N : ℝ := k * (k - 1) / 2 with hN
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hk0, Real.rpow_one, ← Real.sqrt_eq_rpow,
    ← Real.le_logb_iff_rpow_le (by norm_num) hs0]
  refine lower_numbers hk1 (Nat.cast_nonneg ℓ) hc hN hδ hlog (hℓ₀.trans (by exact_mod_cast hℓ)) ?_ ?_ ?_
    (S1 := ∑ e : Pr k, φ.e (π ⟨e, 0⟩) (π ⟨e, 1⟩))
    (S2 := ∑ e : Pr k, ∑ i, φ.e (π ⟨e, i⟩) (hubOf hub A ⟨e, i⟩))
    (S3 := φ.e (hub A true) (hub A false)) (by simpa only [hubCost, add_assoc] using h1)
  · have e1 : N * (1 - δ) = ∑ _e : Pr k, (1 - δ) := by
      rw [hN, ← sum_pairs_one, Finset.sum_mul]
      simp
    rw [e1, Finset.mul_sum]
    refine Finset.sum_le_sum fun e _ => ?_
    have h2 := (abs_lt.1 (hφ (Sum.inl ⟨e, 0⟩) (Sum.inl ⟨e, 1⟩))).2
    have h3 : dist (pos (Sum.inl ⟨e, 0⟩)) (pos (Sum.inl ⟨e, 1⟩)) = 1 := by simp [pos, lowerPos, dist_pvec e.2.ne]
    simp only [id, h3] at h2
    show 1 - δ ≤ c * φ.e (Sum.inl _) (Sum.inl _)
    linarith
  · have h2 : ∀ (e : Pr k) (i : Fin 2), c * φ.e (π ⟨e, i⟩) (hubOf hub A ⟨e, i⟩) ≤
        dist (lowerPos ⟨e, i⟩) (if endNode e i ∈ A.1 then x A else -x A) + δ := by
      intro e i
      have h3 := (abs_lt.1 (hφ (Sum.inl ⟨e, i⟩) (Sum.inr (A.1, decide (endNode e i ∈ A.1))))).1
      simp only [id, pos, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq] at h3
      show c * φ.e (Sum.inl _) (Sum.inr (_, _)) ≤ _
      linarith
    rw [Finset.mul_sum]
    calc ∑ e : Pr k, c * ∑ i, φ.e (π ⟨e, i⟩) (hubOf hub A ⟨e, i⟩) ≤
        ∑ e : Pr k, ((dist (pvec e.1.1 e.1.2) (if e.1.1 ∈ A.1 then x A else -x A) + δ) +
          (dist (pvec e.1.2 e.1.1) (if e.1.2 ∈ A.1 then x A else -x A) + δ)) := by
          refine Finset.sum_le_sum fun e _ => ?_
          rw [Fin.sum_univ_two, mul_add]
          exact (add_le_add (h2 e 0) (h2 e 1)).trans (le_of_eq (by simp [lowerPos, endNode]))
      _ = _ := sum_pairs_add (fun a b => dist (pvec a b) (if a ∈ A.1 then x A else -x A)) δ
      _ ≤ _ := by rw [← hN]; linarith
  · have h2 := (abs_lt.1 (hφ (Sum.inr (A.1, true)) (Sum.inr (A.1, false)))).1
    simp only [id, pos, Sum.elim_inr, if_true, Bool.false_eq_true, if_false] at h2
    have h3 : dist (x A) (-x A) = 1 / (3 * √k) := by
      rw [dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ, norm_smul, hxn]
      norm_num
      ring
    rw [h3] at h2
    show c * φ.e (Sum.inr _) (Sum.inr _) ≤ _
    linarith

/-- **Paper: Proposition prop:flat-lower**, for f_{k,ℓ} with exactly the printed variables. -/
theorem prop_flat_lower_printed {K : Type} [Field K] (hK : Flat K) {k : ℕ} (hk : 2 ≤ k) :
    ∃ ℓ₀ : ℕ, ∀ ℓ, ℓ₀ ≤ ℓ → ∀ s : ℕ, Computes (fklExact K k ℓ) s →
      (2 : ℝ) ^ ((ℓ : ℝ) * (k : ℝ) ^ (3 / 2 : ℝ) / 6) ≤ s := by
  obtain ⟨ℓ₀, h⟩ := prop_flat_lower hK hk
  exact ⟨ℓ₀, fun ℓ hℓ s hs => h ℓ hℓ s (fklExact_computes.1 hs)⟩

/-- **Paper: Theorem thm:flat-simple.** "In the flat case, for every C there is m₀ such that PERM_m has no circuit
over k with m^C gates for m ≥ m₀." -/
theorem thm_flat_simple {K : Type} [Field K] (hK : Flat K) (h2 : (2 : K) ≠ 0) (C : ℕ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ¬ Computes (genPerm K m) (m ^ C) := by
  -- √k = 30 (C + 1)
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = (30 * (C + 1)) ^ 2 := ⟨_, rfl⟩
  have hk3 : 3 ≤ k := hk ▸ le_trans (by omega) (Nat.le_self_pow two_ne_zero (30 * (C + 1)))
  obtain ⟨ℓ₀, hℓ₀⟩ := prop_flat_lower hK (show 2 ≤ k by omega)
  obtain ⟨ℓ₁, hℓ₁⟩ : ∃ ℓ₁, ℓ₁ = ℓ₀ + 3 * k ^ 3 + k + 1 := ⟨_, rfl⟩
  let size : ℕ → ℕ := fun ℓ => 3 * k ^ 3 * ℓ * 2 ^ (k * ℓ)
  refine ⟨size ℓ₁, fun m hm hcomp => ?_⟩
  have hle : ∀ ℓ, ℓ ≤ size ℓ := fun ℓ => by
    show ℓ ≤ 3 * k ^ 3 * ℓ * 2 ^ (k * ℓ)
    calc ℓ = 1 * ℓ * 1 := by simp
      _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_right _ (by nlinarith [Nat.one_le_pow 3 k (by omega)])) Nat.one_le_two_pow
  obtain ⟨ℓ, hℓd⟩ : ∃ ℓ, ℓ = Nat.findGreatest (fun ℓ => size ℓ ≤ m) m := ⟨_, rfl⟩
  have hℓ1 : ℓ₁ ≤ ℓ := hℓd ▸ Nat.le_findGreatest ((hle ℓ₁).trans hm) hm
  have hℓm : size ℓ ≤ m := by
    rw [hℓd]
    exact Nat.findGreatest_spec (P := fun ℓ => size ℓ ≤ m) ((hle ℓ₁).trans hm) hm
  have hnext : m < size (ℓ + 1) := by
    by_contra hh
    push Not at hh
    have h := Nat.le_findGreatest (P := fun ℓ => size ℓ ≤ m) ((hle (ℓ + 1)).trans hh) hh
    omega
  -- log m ≤ 2kℓ
  have hm2 : m ≤ 2 ^ (2 * (k * ℓ)) := by
    refine hnext.le.trans ?_
    show 3 * k ^ 3 * (ℓ + 1) * 2 ^ (k * (ℓ + 1)) ≤ _
    have a1 : 3 * k ^ 3 ≤ 2 ^ ℓ := le_trans (by omega) (Nat.lt_two_pow_self (n := ℓ)).le
    have a2 : ℓ + 1 ≤ 2 ^ ℓ := Nat.lt_two_pow_self
    calc 3 * k ^ 3 * (ℓ + 1) * 2 ^ (k * (ℓ + 1)) ≤ 2 ^ ℓ * 2 ^ ℓ * 2 ^ (k * ℓ + ℓ) :=
          Nat.mul_le_mul (Nat.mul_le_mul a1 a2) (Nat.pow_le_pow_right (by norm_num) (by rw [Nat.mul_succ]; omega))
      _ = 2 ^ (3 * ℓ + k * ℓ) := by rw [← pow_add, ← pow_add]; congr 1; ring
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hup : 5 * m ^ C ≤ 2 ^ (3 + 2 * (k * ℓ) * C) := by
    calc 5 * m ^ C ≤ 2 ^ 3 * (2 ^ (2 * (k * ℓ))) ^ C := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hm2 C)
      _ = _ := by rw [← pow_mul, ← pow_add]
  have hlow := hℓ₀ ℓ (by omega) _ (lem_fkl_perm h2 (by omega) (by omega) hℓm hcomp)
  have h4 := hlow.trans ((Nat.cast_le (α := ℝ)).2 hup)
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast 2 (3 + _),
    Real.rpow_le_rpow_left_iff (by norm_num)] at h4
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsqrt : √(k : ℝ) = 30 * (C + 1) := by
    rw [hk, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)]
    push_cast
    ring
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hk0, Real.rpow_one, ← Real.sqrt_eq_rpow, hsqrt] at h4
  push_cast at h4
  have hkl : (3 : ℝ) ≤ (k : ℝ) * ℓ := by
    exact_mod_cast (le_trans hk3 (Nat.le_mul_of_pos_right k (by omega)) : 3 ≤ k * ℓ)
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ (k : ℝ) * ℓ by linarith) (Nat.cast_nonneg C)]

end Paper
