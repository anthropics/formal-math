/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Fields
import Paper.ApproxScales
import Nc.Rate.Circuit

/-!
# The paper, appendix "Approximate computation"
-/

namespace Paper

open Finset MvPolynomial Nc Nc.Price Nc.CaseI Ov

universe u

/-- VP closure: like VP, with approximating circuits. -/
def VPBar (F : Type u) [Field F] : Set (Family F) :=
  {f | ∃ C : ℕ, ∀ n, Fintype.card (f.X n) ≤ n ^ C + C ∧ (f.poly n).totalDegree ≤ n ^ C + C ∧
    Approximates (f.poly n) (n ^ C + C)}

/-- **Paper: Definition def:approx.** "A circuit over k((ε)) approximates a polynomial f over the field k if its output
is f + εg with all coefficients of g in k[[ε]]. The closure of VP is defined like VP with approximating circuits."
Coefficientwise: no negative powers of ε, and the part of ε⁰ is f. -/
theorem def_approx {F : Type u} {X : Type*} [Field F] (f : MvPolynomial X F) (s : ℕ) :
    Approximates f s ↔ ∃ p : MvPolynomial X (LaurentSeries F), Computes p s ∧
      ∀ d : X →₀ ℕ, (∀ i : ℤ, i < 0 → (coeff d p).coeff i = 0) ∧ (coeff d p).coeff 0 = coeff d f := by
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, fun d => ⟨fun i hi => by rw [h d i hi.le, if_neg hi.ne], by rw [h d 0 le_rfl, if_pos rfl]⟩⟩
  · rintro ⟨p, hp, h⟩
    refine ⟨p, hp, fun d i hi => ?_⟩
    rcases eq_or_lt_of_le hi with rfl | hlt
    · rw [if_pos rfl, (h d).2]
    · rw [if_neg hlt.ne, (h d).1 i hlt]

theorem coeff_mul_T {R : Type} [CommRing R] (f : LaurentPolynomial R) (N i : ℤ) :
    (f * LaurentPolynomial.T N).coeff i = f.coeff (i - N) := by
  classical
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq]
  | C_mul_T n a =>
    rw [LaurentPolynomial.mul_T_assoc, ← LaurentPolynomial.single_eq_C_mul_T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    congr 1
    exact propext ⟨fun h => by omega, fun h => by omega⟩

theorem coeff_toLaurent_natCast {R : Type} [CommRing R] (f : Polynomial R) (i : ℕ) :
    (Polynomial.toLaurent f).coeff (i : ℤ) = f.coeff i := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply Nat.castEmbedding.injective _ i

open Ten in
/-- **Paper: Lemma lem:few-approx.** "The lemma on sums with few terms remains true if f_j has coefficients in
k[ε,ε⁻¹] and t is the part of ε⁰ of the sum, no negative powers occurring." -/
theorem lem_few_approx {K : Type} [Field K] {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (φ : Spec K V)
    (P : Finset V) (t : Ten K V) (ht : ∀ q, q ∉ P → Subsingleton (t.ι q)) {J : ℕ} [NeZero J] (T : Fin J → Ten K V)
    (f : ∀ j p, t.ι p → (T j).ι p → LaurentPolynomial K)
    (h : ∀ x (i : ℤ), i ≤ 0 →
      (∑ j, ∑ y : ∀ p, (T j).ι p, (∏ p, f j p (x p) (y p)) * LaurentPolynomial.C ((T j).val y)).coeff i =
        if i = 0 then t.val x else 0) :
    φ.F t ≤ (J : ℝ) ^ hexp φ (Subtype.val : P → V) * univ.sup' univ_nonempty fun j => φ.F (T j) := by
  classical
  choose e g hg using fun (z : Σ (j : Fin J) (p : V), t.ι p × (T j).ι p) =>
    LaurentPolynomial.exists_T_pow (f z.1 z.2.1 z.2.2.1 z.2.2.2)
  let Δ : ℕ := univ.sup e
  let L : ∀ j p, t.ι p → (T j).ι p → Polynomial K := fun j p a b =>
    g ⟨j, p, a, b⟩ * Polynomial.X ^ (Δ - e ⟨j, p, a, b⟩)
  have hL : ∀ j p a b, Polynomial.toLaurent (L j p a b) = f j p a b * LaurentPolynomial.T (Δ : ℤ) := by
    intro j p a b
    have hle : e ⟨j, p, a, b⟩ ≤ Δ := Finset.le_sup (mem_univ _)
    simp only [L, map_mul, Polynomial.toLaurent_X_pow, hg, LaurentPolynomial.mul_T_assoc]
    congr 2
    omega
  have hB : BSum (Fintype.card V * Δ) t T := by
    refine ⟨L, fun x i hi => ?_⟩
    have e1 : Polynomial.toLaurent (∑ j, ∑ y : ∀ p, (T j).ι p, (∏ p, L j p (x p) (y p)) * Polynomial.C ((T j).val y)) =
        (∑ j, ∑ y : ∀ p, (T j).ι p, (∏ p, f j p (x p) (y p)) * LaurentPolynomial.C ((T j).val y)) *
          LaurentPolynomial.T ((Fintype.card V * Δ : ℕ) : ℤ) := by
      simp only [map_sum, map_mul, map_prod, Polynomial.toLaurent_C, hL, Finset.prod_mul_distrib, Finset.prod_const,
        card_univ, LaurentPolynomial.T_pow, Finset.sum_mul, Nat.cast_mul]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [← coeff_toLaurent_natCast, e1, coeff_mul_T, h x _ (by omega)]
    by_cases hid : i = Fintype.card V * Δ
    · rw [if_pos hid, if_pos (by omega)]
    · rw [if_neg hid, if_neg (by omega)]
  have := few φ (Subtype.val : P → V) t (fun q hq => ht q fun hmem => hq ⟨⟨q, hmem⟩, rfl⟩) hB
    (M := univ.sup' univ_nonempty fun j => φ.F (T j)) (fun j => Finset.le_sup' (fun j => φ.F (T j)) (mem_univ j))
  rwa [Fintype.card_fin] at this

/-- "Cut the constants off": finitely many series can be replaced by Laurent polynomials so that the products of
n of them keep the coefficients of ε^i, i ≤ 0. -/
theorem exists_cut_off {K : Type} [Field K] {ι V : Type} [Fintype ι] [Fintype V] (c : ι → LaurentSeries K) :
    ∃ q : ι → LaurentPolynomial K, ∀ (w : V → ι) (i : ℤ), i ≤ 0 →
      (∏ p, laurentToSeries K (q (w p))).coeff i = (∏ p, c (w p)).coeff i := by
  classical
  let Δ : ℤ := ((univ.sup fun a => (c a).order.natAbs : ℕ) : ℤ)
  have hΔ : 0 ≤ Δ := Int.natCast_nonneg _
  have hc : ∀ a, ∀ i < -Δ, (c a).coeff i = 0 := fun a i hi => HahnSeries.coeff_eq_zero_of_lt_order (by
    have : (c a).order.natAbs ≤ univ.sup fun a => (c a).order.natAbs :=
      Finset.le_sup (f := fun a => (c a).order.natAbs) (mem_univ a)
    omega)
  let N : ℤ := (Fintype.card V : ℤ) * Δ + 1
  choose q hq using fun a => exists_laurentPolynomial_coeff (c a) N
  have hN : -Δ ≤ N := by
    have : 0 ≤ (Fintype.card V : ℤ) * Δ := by positivity
    omega
  refine ⟨q, fun w i hi => ?_⟩
  have key : ∀ S : Finset V,
      (∀ i < -(S.card : ℤ) * Δ, (∏ p ∈ S, c (w p)).coeff i = 0) ∧
      (∀ i < -(S.card : ℤ) * Δ, (∏ p ∈ S, laurentToSeries K (q (w p))).coeff i = 0) ∧
      ∀ i < N - (S.card : ℤ) * Δ, (∏ p ∈ S, laurentToSeries K (q (w p)) - ∏ p ∈ S, c (w p)).coeff i = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      simp only [card_empty, Nat.cast_zero, neg_zero, zero_mul, prod_empty, sub_self, HahnSeries.coeff_zero,
        implies_true, and_true]
      exact ⟨fun i hi => by simp [HahnSeries.coeff_one, hi.ne], fun i hi => by simp [HahnSeries.coeff_one, hi.ne]⟩
    | insert a S ha ih =>
      obtain ⟨hC, hQ, hD⟩ := ih
      have hqa : ∀ i < -Δ, (laurentToSeries K (q (w a))).coeff i = 0 := fun i hi => by
        rw [coeff_laurentToSeries, hq (w a) i (by omega)]
        exact hc _ i hi
      have hd : ∀ i < N, (laurentToSeries K (q (w a)) - c (w a)).coeff i = 0 := fun i hi => by
        rw [HahnSeries.coeff_sub, coeff_laurentToSeries, hq (w a) i hi, sub_self]
      simp only [prod_insert ha, card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
      refine ⟨fun i hi => coeff_mul_eq_zero (hc (w a)) hC (by linarith), fun i hi => coeff_mul_eq_zero hqa hQ (by linarith),
        fun i hi => ?_⟩
      rw [show laurentToSeries K (q (w a)) * (∏ p ∈ S, laurentToSeries K (q (w p))) - c (w a) * ∏ p ∈ S, c (w p) =
        (laurentToSeries K (q (w a)) - c (w a)) * (∏ p ∈ S, laurentToSeries K (q (w p))) +
          c (w a) * (∏ p ∈ S, laurentToSeries K (q (w p)) - ∏ p ∈ S, c (w p)) by ring, HahnSeries.coeff_add,
        coeff_mul_eq_zero hd hQ (by linarith), coeff_mul_eq_zero (hc (w a)) hD (by linarith), add_zero]
  have h := (key univ).2.2 i (by rw [card_univ]; omega)
  rwa [HahnSeries.coeff_sub, sub_eq_zero] at h

/-- A wire over the Laurent series is the one over k. -/
theorem wire_series {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] (n : ℕ) (p q : I)
    (y : ∀ r, (Ten.wire K n p q).ι r) :
    (Ten.wire (LaurentSeries K) n p q).val y = HahnSeries.C ((Ten.wire K n p q).val y) := by
  unfold Ten.wire Ten.push Ten.unit
  dsimp only
  split_ifs <;> simp

/-- The hub tensors over the Laurent series are those over k. -/
theorem hubTen_series {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I] {k ℓ L : ℕ} (π : End k → I)
    (hub : Finset (Fin k) → Bool → I) (S : Finset (Fin k)) (y : ∀ p, (hubTen K ℓ L π hub S).ι p) :
    (hubTen (LaurentSeries K) ℓ L π hub S).val y = HahnSeries.C ((hubTen K ℓ L π hub S).val y) := by
  show (∏ a, (Ten.wire (LaurentSeries K) (2 ^ ℓ) (π a) (hubOf hub S a)).val fun p => (y p).1 a) *
      (Ten.wire (LaurentSeries K) L (hub S true) (hub S false)).val (fun p => (y p).2) =
    HahnSeries.C ((∏ a, (Ten.wire K (2 ^ ℓ) (π a) (hubOf hub S a)).val fun p => (y p).1 a) *
      (Ten.wire K L (hub S true) (hub S false)).val fun p => (y p).2)
  rw [map_mul, map_prod]
  exact congrArg₂ (· * ·) (Finset.prod_congr rfl fun a _ => wire_series (2 ^ ℓ) (π a) (hubOf hub S a) fun p => (y p).1 a)
    (wire_series L (hub S true) (hub S false) fun p => (y p).2)

/-- The hub decomposition over the Laurent series: the coefficient of an entry is a sum over the balanced sets of the
hub tensors over k, with functionals in k((ε)). -/
theorem hubs_series {K : Type} [Field K] {k ℓ s : ℕ} (hk : 2 ≤ k)
    {Q : MvPolynomial (Fin k × Ix k ℓ) (LaurentSeries K)} (hQ : Computes Q s) (π : End k → RPt k) :
    ∃ M : ∀ (j : Fin (Fintype.card (bal (univ : Finset (Fin k))))) (p : RPt k),
        (Ten.push π (fklTen K k ℓ)).ι p → (hubTen K ℓ s π hubPt (balEnum k j).1).ι p → LaurentSeries K,
      ∀ x : ∀ p, (Ten.push π (fklTen K k ℓ)).ι p, cf univ Q (tables fun a => x (π a) ⟨a, rfl⟩) =
        ∑ j, ∑ y : ∀ p, (hubTen K ℓ s π hubPt (balEnum k j).1).ι p,
          (∏ p, M j p (x p) (y p)) * HahnSeries.C ((hubTen K ℓ s π hubPt (balEnum k j).1).val y) := by
  obtain ⟨M, hM⟩ := (prop_flat_lower_sum hk hQ π hubPt).reindex (balEnum k)
  refine ⟨fun j p a b => M j p a b, fun x => ?_⟩
  have h1 := hM x
  refine Eq.trans ?_ (h1.trans (Finset.sum_congr rfl fun j _ => ?_))
  · rfl
  refine Fintype.sum_equiv (Equiv.refl _) _ _ fun y => ?_
  refine congrArg₂ (· * ·) rfl ?_
  exact hubTen_series (K := K) π hubPt _ _

/-- "So Proposition prop:flat-rate holds for approximating circuits: cut the constants off, and note that Lemma
lem:balanced holds over every commutative ring." -/
theorem flat_rate_approximating {K : Type} [Field K] (hK : Flat K) {k : ℕ} (hk : 2 ≤ k) {ℓ s : ℕ}
    (hℓ : 100 * √k ≤ (ℓ : ℝ)) (hcomp : Approximates (fkl K k ℓ) s) :
    (ℓ : ℝ) * (k * √k) / 14 ≤ Real.logb 2 s := by
  classical
  obtain ⟨Q, hQ, hQf⟩ := hcomp
  have hs : 1 ≤ s := by
    obtain ⟨l, -, a, ha, -⟩ := hQ
    omega
  refine rate_of_someSetPays hK hk hℓ hs fun φ => ?_
  have := bal_nonempty hk
  have : NeZero (Fintype.card (bal (univ : Finset (Fin k)))) := ⟨Fintype.card_ne_zero⟩
  have : Nonempty (RPt k) := ⟨hubPt ∅ true⟩
  let π : End k → RPt k := Sum.inl
  let T : Fin (Fintype.card (bal (univ : Finset (Fin k)))) → Ten K (RPt k) := fun j =>
    hubTen K ℓ s π hubPt (balEnum k j).1
  -- the hub decomposition over the Laurent series
  obtain ⟨M, hM⟩ := hubs_series hk hQ π
  -- and with the functionals cut off
  obtain ⟨q, hq⟩ := exists_cut_off (V := RPt k)
    fun e : Σ j, Σ p : RPt k, (Ten.push π (fklTen K k ℓ)).ι p × (T j).ι p => M e.1 e.2.1 e.2.2.1 e.2.2.2
  refine someSetPays_of_few φ hs (lem_few_approx φ _ _ (fklTen_onEnds K k ℓ) T
    (fun j p a b => q ⟨j, p, a, b⟩) fun x i hi => ?_)
  -- the cut-off functionals give the same coefficients of ε^i, i ≤ 0
  have hterm : ∀ (j) (y : ∀ p, (T j).ι p), (laurentToSeries K ((∏ p, q ⟨j, p, x p, y p⟩) *
      LaurentPolynomial.C ((T j).val y))).coeff i =
        ((∏ p, M j p (x p) (y p)) * HahnSeries.C ((T j).val y)).coeff i := by
    intro j y
    have eC : laurentToSeries K (LaurentPolynomial.C ((T j).val y)) = HahnSeries.C ((T j).val y) := by
      ext n
      rw [coeff_laurentToSeries, ← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_single, HahnSeries.C_apply,
        HahnSeries.coeff_single, Finsupp.single_apply]
      simp only [eq_comm]
      congr
    rw [map_mul, map_prod, eC, mul_comm _ (HahnSeries.C _), mul_comm _ (HahnSeries.C _),
      HahnSeries.C_mul_eq_smul, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.coeff_smul,
      hq (fun p => ⟨j, p, x p, y p⟩) i hi]
  have e : (Ten.push π (fklTen K k ℓ)).val x = cf univ (fkl K k ℓ) (tables fun a => x (π a) ⟨a, rfl⟩) :=
    fklTen_val K fun a => x (π a) ⟨a, rfl⟩
  have hx : (cf univ Q (tables fun a => x (π a) ⟨a, rfl⟩)) =
      ∑ j, ∑ y : ∀ p, (T j).ι p, (∏ p, M j p (x p) (y p)) * HahnSeries.C ((T j).val y) := hM x
  rw [e, ← coeff_laurentToSeries]
  refine Eq.trans ?_ (hQf (mono univ (tables fun a => x (π a) ⟨a, rfl⟩)) i hi)
  rw [show coeff (mono univ (tables fun a => x (π a) ⟨a, rfl⟩)) Q = cf univ Q (tables fun a => x (π a) ⟨a, rfl⟩) from rfl,
    hx]
  simp only [map_sum, HahnSeries.coeff_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun y _ => hterm j y

/-- "… and with it Theorem thm:flat-rate", for every family that is complete for grid sums. -/
theorem flat_rate_approx_complete (κ : ℕ) : ∃ m₀ : ℕ, ∀ (K : Type) [Field K], Flat K →
    ∀ G : ∀ S : ℕ, MvPolynomial (Fin S × Fin S) K, GridComplete K G κ →
    ∀ m ≥ m₀, ∀ s : ℕ, Approximates (G m) s → (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨m₀, h⟩ := rate_of_projection κ
  refine ⟨m₀, fun K _ hK G hG => h _ fun k ℓ m s hk hℓ hℓk hm hs => ?_⟩
  obtain ⟨E, hE, he⟩ := fkl_complete hG hk hℓ hm
  have hap : Approximates (fkl K k ℓ) (5 * s) := he ▸ hs.aeval E hE
  refine rate_pow hk ?_ (flat_rate_approximating hK hk hℓk hap)
  obtain ⟨Q, ⟨l, -, a, ha, -⟩, -⟩ := hap
  omega

/-- The contracting case with the calculation of Theorem thm:contracting. -/
theorem contracting_approx_rate {K : Type} [Field K] (hK : Contracting K)
    {G : ∀ S, MvPolynomial (Fin S × Fin S) K} {κ : ℕ} (hG : GridComplete K G κ) :
    ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, Approximates (G m) s →
      (2 : ℝ) ^ (c * Real.logb 2 m ^ 2 / Real.logb 2 (Real.logb 2 m)) < s := by
  obtain ⟨C, M₁, h⟩ := contracting_approx_complete hK hG
  exact quasi_of_exponents (P := fun m s => Approximates (G m) s)
    (fun _ _ _ hst ⟨Q, hQ, hQf⟩ => ⟨Q, Computes.mono hQ hst, hQf⟩) h

/-- Both cases over KK, for circuits with constants in KK[ε,ε⁻¹]. -/
theorem approx_rate_closed {K : Type} [Field K] {G : ∀ S, MvPolynomial (Fin S × Fin S) K} {κ : ℕ}
    (hG : GridComplete K G κ) :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, ∀ P : MvPolynomial (Fin m × Fin m) (LaurentPolynomial K), Computes P s →
      (∀ d, (∀ i : ℤ, i < 0 → (coeff d P).coeff i = 0) ∧ (coeff d P).coeff 0 = coeff d (G m)) →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
  obtain ⟨m₀, h⟩ : ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ s, Approximates (G m) s →
      (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
    rcases thm_alt K with hK | hK
    · obtain ⟨m₀, h⟩ := flat_rate_approx_complete κ
      exact ⟨m₀, h K hK _ hG⟩
    · exact thm_allfields_exceeds (contracting_approx_rate hK hG)
  refine ⟨m₀, fun m hm s P hP hc => h m hm s (Approximates.of_laurentPolynomial hP fun d i hi => ?_)⟩
  rcases eq_or_lt_of_le hi with rfl | hlt
  · rw [if_pos rfl, (hc d).2]
  · rw [if_neg hlt.ne, (hc d).1 i hlt]

/-- **Paper: Theorem thm:approx.** "The theorem on all fields holds for circuits that approximate HC_m, respectively
PERM_m. In particular VNP is not contained in the closure of VP over every field." -/
theorem thm_approx :
    (∃ c : ℝ, 0 < c ∧ ∀ p : ℕ, p = 0 ∨ p.Prime → ∃ m₀ : ℕ, ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
      (Approximates (genHC F m) s → (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) ∧
      (p ≠ 2 → Approximates (genPerm F m) s → (m : ℝ) ^ (c * Real.logb 2 m ^ (1 / 3 : ℝ)) < s)) ∧
    ∀ (F : Type u) [Field F], ¬ VNP F ⊆ VPBar F := by
  have main : ∀ p : ℕ, p = 0 ∨ p.Prime → ∃ m₀ : ℕ, ∀ (F : Type u) [Field F] [CharP F p], ∀ m ≥ m₀, ∀ s : ℕ,
      (Approximates (genHC F m) s → (m : ℝ) ^ (1 / 1600 ^ 2 * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) ∧
      (p ≠ 2 → Approximates (genPerm F m) s → (m : ℝ) ^ (1 / 1600 ^ 2 * Real.logb 2 m ^ (1 / 3 : ℝ)) < s) := by
    intro p hp
    obtain ⟨K, _, _, _⟩ := exists_closed p hp
    obtain ⟨M₁, h1⟩ := approx_rate_closed (gridComplete_hc K)
    obtain ⟨M₂, h2⟩ : ∃ M₂ : ℕ, p ≠ 2 → ∀ m ≥ M₂, ∀ s, ∀ P : MvPolynomial (Fin m × Fin m) (LaurentPolynomial K),
        Computes P s → (∀ d, (∀ i : ℤ, i < 0 → (coeff d P).coeff i = 0) ∧ (coeff d P).coeff 0 = coeff d (genPerm K m)) →
        (2 : ℝ) ^ (Real.logb 2 m ^ (4 / 3 : ℝ) / 1600 ^ 2) < s := by
      by_cases hne : p = 2
      · exact ⟨0, fun h => absurd hne h⟩
      · obtain ⟨M₂, h⟩ := approx_rate_closed (gridComplete_perm (two_ne_zero_of_char K p hp hne))
        exact ⟨M₂, fun _ => h⟩
    refine ⟨M₁ + M₂ + 2, fun F _ _ m hm s => ⟨fun hs => ?_, fun hne hs => ?_⟩⟩
    · rw [← map_genHC (Int.castRingHom F)] at hs
      obtain ⟨P, hP, hc⟩ := lem_transfer_approx (KK := K) p (genHC ℤ m) hs
      rw [map_genHC] at hc
      exact beyond_of_rate (by omega) (h1 m (by omega) s P hP hc)
    · rw [← map_permInt] at hs
      obtain ⟨P, hP, hc⟩ := lem_transfer_approx (KK := K) p (permInt m) hs
      rw [map_permInt] at hc
      exact beyond_of_rate (by omega) (h2 hne m (by omega) s P hP hc)
  refine ⟨⟨1 / 1600 ^ 2, by norm_num, main⟩, fun F _ h => ?_⟩
  obtain ⟨C, hC⟩ := h (hc_mem_VNP F)
  obtain ⟨p, _⟩ := CharP.exists F
  obtain ⟨m₀, hlow⟩ := main p (CharP.char_is_prime_or_zero F p).symm
  obtain ⟨m, hm1, hm2⟩ := exists_beyond_poly (show (0 : ℝ) < 1 / 1600 ^ 2 by norm_num) m₀ C
  exact hm2 ((hlow F m hm1 _).1 (hC m).2.2)

end Paper
