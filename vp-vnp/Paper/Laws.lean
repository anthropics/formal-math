/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Groups
import Nc.Vp.Main
import Nc.Tow.FromPriceK

/-!
# The paper, section "Exchange identities"
-/

namespace Paper

open Finset Nc.Price Nc.Tow Nc.Vp Ov Ov.Ten
open Nc.Tower (U x NN ee card_U sum_NN npair npair_sym x_mul_self x_ne_one)

/-- **Paper: Definition def:law.** "A law on U_h over a commutative ring A consists of a finite family of pairs of
distinct elements (its slots), counted by a load σ, a finite nonempty index set with an injective code by λ ≥ 1 bits, a
load len_i on near pairs for every i, and for every i and every element g a table with values in A that depends on the
bits at g, such that ∏_e [the σ_e bits agree at both ends of e] = ∑_i ∑_y ∏_g (table of (i,g))." In the project a law
is an Nc.G.Law; this theorem lists what it carries. The two side conditions (nonempty, λ ≥ 1) are supplied by thm_laws. -/
theorem def_law {A : Type} [CommRing A] (L : Nc.G.Law A) :
    Function.Injective L.lab ∧ (∀ e, L.a e ≠ L.b e) ∧
      ∀ X : L.Ro → L.Sl → Bool, (if ∀ e, X (L.a e) e = X (L.b e) e then (1 : A) else 0) =
        ∑ i, ∑ y : ∀ ν, Fin (L.len i ν) → Bool, ∏ p, L.tab p i (fun e => X p e) (fun ν => y ν) :=
  ⟨L.lab_inj, L.ab, L.law⟩

/-- "Since the near pairs connect U_h, indices that agree along channels agree everywhere." -/
theorem indices_agree {h : ℕ} [NeZero h] {I : Type} (f : U h → I) (hf : ∀ ν : NN h, f (cNear ν) = f (dNear ν))
    (p q : U h) : f p = f q := by
  refine Nc.Flag.const_of_x f (fun l k => ?_) p q
  have h1 := npair_sym l k
  have h2 := hf (npair l k)
  rw [Sym2.eq_iff] at h1
  rcases h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact (congrArg f e2).trans (h2.symm.trans (congrArg f e1.symm))
  · exact (congrArg f e2).trans (h2.trans (congrArg f e1.symm))

/-- "The laws are finitely many polynomial identities with coefficients in A, so they hold over every commutative
A-algebra." -/
theorem laws_over_algebras {A : Type} [CommRing A] (L : Nc.G.Law A) (R : Type) [CommRing R] [Algebra A R]
    (X : L.Ro → L.Sl → Bool) : (if ∀ e, X (L.a e) e = X (L.b e) e then (1 : R) else 0) =
      ∑ i, ∑ y : ∀ ν, Fin (L.len i ν) → Bool,
        ∏ p, algebraMap A R (L.tab p i (fun e => X p e) (fun ν => y ν)) := by
  simpa only [apply_ite (algebraMap A R), map_one, map_zero, map_sum, map_prod] using
    congrArg (algebraMap A R) (L.law X)

/-- The opening of the section: "Replacing C₀ by an integer that is at least 2C₀+1, Theorem thm:poincare reads: the mean
of |e|² over all pairs is at most C₀ times 2/b times the sum of |e|² over near pairs, for every price", where h is a
multiple of u with h ≥ 2u and b = |U_h|. C is the constant of the theorem and C₀ the integer. -/
theorem thm_laws_poincare {K : Type} [Field K] (hK : Contracting K) :
    ∃ u : ℕ, 2 ≤ u ∧ ∃ (C : ℝ) (C₀ : ℕ), 0 ≤ C ∧ PoincareBound K u C ∧ 2 * C + 1 ≤ (C₀ : ℝ) ∧
      ∀ (h : ℕ) [NeZero h], u ∣ h → 2 * u ≤ h → ∀ w : U h → U h → ℝ, IsPrice K w →
        (∑ p, ∑ q, w p q ^ 2) / ((Fintype.card (U h) : ℝ) * ((Fintype.card (U h) : ℝ) - 1)) ≤
          (C₀ : ℝ) * (2 / (Fintype.card (U h) : ℝ) * ∑ ν : NN h, w (cNear ν) (dNear ν) ^ 2) := by
  obtain ⟨u, hu, C, hC, hP⟩ := thm_poincare hK
  obtain ⟨C₀, hC₀⟩ := exists_nat_ge (2 * C + 1)
  refine ⟨u, hu, C, C₀, hC, hP, hC₀, fun h _ hdvd hle w hw => ?_⟩
  obtain ⟨l, rfl⟩ := dvd_iff_exists_eq_mul_left.1 hdvd
  have h1 := hP l (Nat.le_of_mul_le_mul_right hle (by omega)) w hw
  set b : ℝ := (Fintype.card (U (l * u)) : ℝ) with hb
  have hb2 : (2 : ℝ) ≤ b := by
    have : 2 ≤ Fintype.card (U (l * u)) :=
      Fintype.one_lt_card_iff.2 ⟨x (l * u) ⟨0, by omega⟩, 1, x_ne_one _⟩
    rw [hb]
    exact_mod_cast this
  have h2 : ∑ g, ∑ k, w k (g * k) ^ 2 = ∑ p, ∑ q, w p q ^ 2 := by
    rw [Finset.sum_comm]
    exact sum_congr rfl fun k _ => Equiv.sum_comp (Equiv.mulRight k) fun q => w k q ^ 2
  have h3 : ∑ j, ∑ k, w k (x (l * u) j * k) ^ 2 = 2 * ∑ ν : NN (l * u), w (cNear ν) (dNear ν) ^ 2 := by
    rw [sum_NN (fun j k => w k (x (l * u) j * k) ^ 2) (fun j k => by
      rw [← mul_assoc, x_mul_self, one_mul, hw.symm]), two_mul]
  rw [h2, ← Finset.sum_div, h3] at h1
  obtain ⟨P, hP'⟩ : ∃ P : ℝ, P = ∑ ν : NN (l * u), w (cNear ν) (dNear ν) ^ 2 := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ∑ p, ∑ q, w p q ^ 2 := ⟨_, rfl⟩
  rw [← hP', ← hQ] at h1 ⊢
  have hP0 : 0 ≤ P := by rw [hP']; exact sum_nonneg fun _ _ => sq_nonneg _
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < b ^ 2)] at h1
  rw [div_le_iff₀ (mul_pos (by linarith) (by linarith))]
  have e1 : C * (2 * P / b) * b ^ 2 = C * b * (2 * P) := by field_simp
  have e2 : (C₀ : ℝ) * (2 / b * P) * (b * (b - 1)) = (C₀ : ℝ) * (b - 1) * (2 * P) := by field_simp
  rw [e1] at h1
  rw [e2]
  refine h1.trans (mul_le_mul_of_nonneg_right ?_ (by linarith))
  calc C * b ≤ (2 * C + 1) * (b - 1) := by nlinarith
    _ ≤ (C₀ : ℝ) * (b - 1) := mul_le_mul_of_nonneg_right hC₀ (by linarith)

/-- The proof of Theorem thm:laws: "For every price the Cauchy–Schwarz inequality, twice, and the Poincaré inequality
give ∑_e σ_e|e| ≤ max_β ∑_{near e} β_e|e|", over rounded loads β = ⌈y⌉ with ‖y‖_* ≤ √C₀·‖σ‖. Here the two norms are
those of the weights α and β, and the quadratic inequality between them is the hypothesis. -/
theorem thm_laws_loads {E N : Type} [Fintype E] [Fintype N] (α : E → ℝ) (hα : ∀ e, 0 < α e) (β : N → ℝ)
    (hβ : ∀ ν, 0 < β ν) {C : ℝ} (hC : 0 < C) (w : E → ℝ) (w' : N → ℝ) (hw' : ∀ ν, 0 ≤ w' ν)
    (h : ∑ e, α e * w e ^ 2 ≤ C * ∑ ν, β ν * w' ν ^ 2) (σ : E → ℕ) {R : ℝ} (hR : 0 < R)
    (hσ : nrm α (fun e => (σ e : ℝ)) ≤ R) :
    ∃ ld : N → ℕ, nrm β (fun ν => (ld ν : ℝ)) ≤ √C * R + nrm β (fun _ => 1) ∧
      ∑ e, (σ e : ℝ) * w e ≤ ∑ ν, (ld ν : ℝ) * w' ν := by
  have hsc : 0 < √C := Real.sqrt_pos.2 hC
  have e : ∀ n : N → ℝ, nrm β n = √C * nrm (fun ν => C * β ν) n := by
    intro n
    rw [nrm, nrm, ← Real.sqrt_mul hC.le, Finset.mul_sum]
    congr 1
    refine sum_congr rfl fun ν _ => ?_
    have := (hβ ν).ne'
    field_simp
  set Z := nrm (fun ν => C * β ν) (fun _ : N => (1 : ℝ)) with hZ
  have hZ0 : 0 ≤ Z := nrm_nonneg _ _
  obtain ⟨ld, h1, h2⟩ := exists_load α hα (fun ν => C * β ν) (fun ν => mul_pos hC (hβ ν)) w w' hw'
    (h.trans (le_of_eq (by simp only [Finset.mul_sum, mul_assoc]))) σ hR.le
    (η := Z / R) (by positivity) hσ 1 (by rw [Nat.cast_one, one_mul, div_mul_cancel₀ _ hR.ne'])
  refine ⟨ld, ?_, by simpa using h2⟩
  rw [e, e, ← mul_add]
  refine mul_le_mul_of_nonneg_left (h1.trans (le_of_eq ?_)) hsc.le
  rw [Nat.cast_one, mul_one, add_mul, one_mul, div_mul_cancel₀ _ hR.ne']

/-- The proof of Theorem thm:laws: "φ(W^σ) = 2^(∑ σ_e d_φ(e)), and d_φ is a price; so φ(W^σ) ≤ max φ(W^β). So duality
(Theorem thm:duality) covers W^(qσ) by at most 2^(εq) tensors W^β, with sums β of q elements of the given loads, for
every large q." The cover is given as an identity between functions of bits. -/
theorem thm_laws_cover {K : Type} [Field K] {V E N B : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype E] [DecidableEq E] [Fintype N] [DecidableEq N] [Fintype B] [DecidableEq B] (a b : E → V) (c d : N → V)
    (σ : E → ℕ) (ℬ : B → N → ℕ)
    (h : ∀ w : V → V → ℝ, IsPrice K w → ∃ β,
      ∑ e, (σ e : ℝ) * w (a e) (b e) ≤ ∑ ν, (ℬ β ν : ℝ) * w (c ν) (d ν)) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∃ (m : ℕ) (v : Fin m → B → ℕ), (m : ℝ) ≤ 2 ^ (ε * q) ∧ (∀ i, ∑ β, v i β = q) ∧
      ∃ tab, BitId K (fun s : Σ e, Fin (q * σ e) => a s.1) (fun s : Σ e, Fin (q * σ e) => b s.1) c d
        (fun i ν => ∑ β, v i β * ℬ β ν) tab := by
  classical
  obtain ⟨β₀, -⟩ := h _ isPrice_zero
  have nz : ∀ {E : Type} [Fintype E] [DecidableEq E] (a b : E → V) (n : E → ℕ),
      ∃ y, (wires K a b fun e => 2 ^ n e).val y ≠ 0 := by
    intro E _ _ a b n
    refine ⟨fun p e j => (⟨0, Nat.two_pow_pos _⟩ : Fin (2 ^ n e)), Finset.prod_ne_zero_iff.2 fun e _ => ?_⟩
    have h : (unit K (Fin 2) (2 ^ n e)).val (fun _ => (⟨0, Nat.two_pow_pos _⟩ : Fin (2 ^ n e))) ≠ 0 := by
      rw [unit_val_of fun _ _ => rfl]
      exact one_ne_zero
    exact h
  let eB := Fintype.equivFin B
  obtain ⟨q₀, hq⟩ := thm_duality (A := fun j => wires K c d fun ν => 2 ^ ℬ (eB.symm j) ν)
    (nz a b σ) ⟨eB β₀, nz c d _⟩ (fun φ => by
      obtain ⟨β, hβ⟩ := h φ.e (isPrice_spec φ)
      refine ⟨eB β, ?_⟩
      rw [F_wires_two, F_wires_two, Equiv.symm_apply_apply]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ) hε
  refine ⟨q₀, fun q hq' => ?_⟩
  obtain ⟨m, v, hm, hv, hs⟩ := hq q hq'
  obtain ⟨tab, htab⟩ := exists_wireId
    (((Equi.wires_kpow a b σ q).2.trans_sum hs).mono fun i =>
      (Equi.wires_prod c d (fun j => ℬ (eB.symm j)) (v i)).1)
  have key : ∀ len len' : Fin m → N → ℕ, len = len' →
      (∃ tab, BitId K (fun s : Σ e, Fin (q * σ e) => a s.1) (fun s : Σ e, Fin (q * σ e) => b s.1) c d len tab) →
      ∃ tab, BitId K (fun s : Σ e, Fin (q * σ e) => a s.1) (fun s : Σ e, Fin (q * σ e) => b s.1) c d len' tab := by
    rintro _ _ rfl h
    exact h
  refine ⟨m, fun i β => v i (eB β), hm, fun i => (Equiv.sum_comp eB (v i)).trans (hv i), ?_⟩
  refine key (fun i ν => ∑ j, v i j * ℬ (eB.symm j) ν) (fun i ν => ∑ β, v i (eB β) * ℬ β ν) ?_ ⟨_, htab.bitId⟩
  funext i ν
  exact Fintype.sum_equiv eB.symm _ _ fun j => by rw [Equiv.apply_symm_apply]

/-- The proof of Theorem thm:laws: "The tables are the entries of the finitely many linear maps; let A be generated
by them and −1." -/
theorem thm_laws_ring {K : Type} [CommRing K] {Di : Type} [Finite Di] (L : Di → Nc.G.Law K) :
    ∃ (A : Subring K) (_ : Algebra.FiniteType ℤ A), ∀ d p i y g, (L d).tab p i y g ∈ A := by
  classical
  let S : Set K := ⋃ d, entries (L d)
  have hS : S.Finite := Set.finite_iUnion fun d => entries_finite (L d)
  refine ⟨Subring.closure S, ?_, fun d p i y g => Subring.subset_closure (Set.mem_iUnion.2 ⟨d, p, i, y, g, rfl⟩)⟩
  have h2 : Algebra.FiniteType ℤ (Algebra.adjoin ℤ S) :=
    (Subalgebra.fg_iff_finiteType _).1 ⟨hS.toFinset, by simp⟩
  have hmem : ∀ y, y ∈ Algebra.adjoin ℤ S ↔ y ∈ Subring.closure S := fun y => by
    rw [Algebra.adjoin_int]
    exact Iff.rfl
  let f : Algebra.adjoin ℤ S →+* Subring.closure S :=
    { toFun := fun y => ⟨y.1, (hmem y.1).1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact Algebra.FiniteType.of_surjective f.toIntAlgHom fun y => ⟨⟨y.1, (hmem y.1).2 y.2⟩, rfl⟩

/-- The proof of Theorem thm:laws up to the choice of the ring: for one h and a Poincaré inequality with the integer
C₀, finitely many laws over K with the clauses (a) and (b). "Let a be a large integer", the loads σ_x = ⌈ax⌉, then
duality with one q, codes of λ ≤ εq+2 bits, and a₁ = aq. -/
theorem thm_laws_over_field {K : Type} [Field K] {h : ℕ} [NeZero h] (h2 : 2 ≤ h) {C₀ : ℕ} (hC₀ : 1 ≤ C₀)
    (hP : ∀ w : U h → U h → ℝ, IsPrice K w →
      (∑ p, ∑ q, w p q ^ 2) / ((Fintype.card (U h) : ℝ) * ((Fintype.card (U h) : ℝ) - 1)) ≤
        (C₀ : ℝ) * (2 / (Fintype.card (U h) : ℝ) * ∑ ν : NN h, w (cNear ν) (dNear ν) ^ 2)) :
    ∃ (a₁ : ℕ) (Di : Type) (_ : Fintype Di) (L : Di → Nc.G.Law K)
      (ro : ∀ d, (L d).Ro ≃ U h) (cn : ∀ d, (L d).Cn ≃ NN h), 0 < a₁ ∧
      (∀ d ν, s(ro d ((L d).c ν), ro d ((L d).d ν)) = s(cNear (cn d ν), dNear (cn d ν))) ∧
      (∀ d, 1 ≤ (L d).lam ∧ Nonempty (L d).I) ∧
      (∀ (n : Sym2 (U h) → ℕ) (t : ℕ),
        √(((Fintype.card (U h) : ℝ) * ((Fintype.card (U h) : ℝ) - 1) / 2) *
            ∑ q : Sym2 (U h), if q.IsDiag then 0 else (n q : ℝ) ^ 2) ≤ a₁ * t →
        ∃ d, ∀ q : Sym2 (U h), ¬ q.IsDiag →
          n q ≤ (univ.filter fun e : (L d).Sl => s(ro d ((L d).a e), ro d ((L d).b e)) = q).card * t) ∧
      ∀ d i, √((Fintype.card (U h) : ℝ) / 2 * ∑ ν, (((L d).lam + (L d).len i ν : ℕ) : ℝ) ^ 2) ≤
        √(4 * (C₀ : ℝ)) * a₁ := by
  classical
  have hbN : 2 ≤ Fintype.card (U h) :=
    Fintype.one_lt_card_iff.2 ⟨x h ⟨0, by omega⟩, 1, x_ne_one _⟩
  set b : ℝ := (Fintype.card (U h) : ℝ) with hb
  have hb0 : 0 < b := by rw [hb]; exact_mod_cast (by omega : 0 < Fintype.card (U h))
  have hb1 : 0 < b - 1 := by
    have : (2 : ℝ) ≤ b := by rw [hb]; exact_mod_cast hbN
    linarith
  -- the pairs and the two norms
  let E : Type := {q : Sym2 (U h) // ¬ q.IsDiag}
  let ea : E → U h := fun q => q.1.out.1
  let eb : E → U h := fun q => q.1.out.2
  have hE : ∀ f : Sym2 (U h) → ℝ, ∑ q : E, f q.1 = ∑ q : Sym2 (U h), if q.IsDiag then 0 else f q := by
    intro f
    rw [← Finset.sum_subtype (Finset.univ.filter fun q : Sym2 (U h) => ¬ q.IsDiag) (by simp) f, Finset.sum_filter]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hq : q.IsDiag <;> simp [hq]
  let α : E → ℝ := fun _ => 2 / (b * (b - 1))
  let β : NN h → ℝ := fun _ => 2 / b
  have hα : ∀ e, 0 < α e := fun _ => by positivity
  have hβ : ∀ ν, 0 < β ν := fun _ => by positivity
  have hquad : ∀ w : U h → U h → ℝ, IsPrice K w →
      ∑ e, α e * w (ea e) (eb e) ^ 2 ≤ (C₀ : ℝ) * ∑ ν, β ν * w (cNear ν) (dNear ν) ^ 2 := by
    intro w hw
    have h6 : ∑ p, ∑ q, w p q ^ 2 =
        2 * ∑ q : Sym2 (U h), if q.IsDiag then 0 else w q.out.1 q.out.2 ^ 2 := by
      rw [← sum_off]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      by_cases hpq : p = q
      · rw [if_pos hpq, hpq, hw.self]
        norm_num
      · rw [if_neg hpq]
        have h7 := out_mk s(p, q)
        rw [Sym2.eq_iff] at h7
        rcases h7 with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2]
        · rw [e1, e2, hw.symm]
    simp only [α, β, ea, eb]
    rw [← Finset.mul_sum, ← Finset.mul_sum, hE fun q => w q.out.1 q.out.2 ^ 2]
    refine le_trans (le_of_eq ?_) (hP w hw)
    rw [h6]
    ring
  -- a large integer a; the loads σ and the loads of ℬ
  set c := √(C₀ : ℝ) with hc
  have hc1 : 1 ≤ c := by
    rw [hc, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hC₀)
  set Z₁ := nrm α (fun _ : E => (1 : ℝ)) with hZ₁
  set Z₂ := nrm β (fun _ : NN h => (1 : ℝ)) with hZ₂
  have hZ₁0 : 0 ≤ Z₁ := nrm_nonneg _ _
  have hZ₂0 : 0 ≤ Z₂ := nrm_nonneg _ _
  obtain ⟨a, ha⟩ := exists_nat_ge (4 * (Z₁ + Z₂) + 1)
  have ha1 : (1 : ℝ) ≤ a := by linarith
  have := finite_loads α hα ((a : ℝ) + Z₁)
  let _ : Fintype (Loads α ((a : ℝ) + Z₁)) := Fintype.ofFinite _
  have := finite_loads β hβ (c * ((a : ℝ) + Z₁) + Z₂)
  let _ : Fintype (Loads β (c * ((a : ℝ) + Z₁) + Z₂)) := Fintype.ofFinite _
  have hmax : ∀ t : Loads α ((a : ℝ) + Z₁), ∀ w : U h → U h → ℝ, IsPrice K w →
      ∃ ld : Loads β (c * ((a : ℝ) + Z₁) + Z₂),
        ∑ e, (t.1 e : ℝ) * w (ea e) (eb e) ≤ ∑ ν, (ld.1 ν : ℝ) * w (cNear ν) (dNear ν) := by
    intro t w hw
    obtain ⟨ld, h1, h2⟩ := thm_laws_loads α hα β hβ (C := (C₀ : ℝ)) (by exact_mod_cast hC₀)
      (fun e => w (ea e) (eb e)) (fun ν => w (cNear ν) (dNear ν)) (fun ν => hw.nonneg _ _) (hquad w hw)
      t.1 (R := (a : ℝ) + Z₁) (by linarith) t.2
    exact ⟨⟨ld, h1⟩, h2⟩
  -- ε small, then q large, one q for all loads
  obtain ⟨ε, hε, hεZ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * Z₂ ≤ (a : ℝ) / 4 := by
    refine ⟨(a : ℝ) / (4 * (Z₂ + 1)), by positivity, ?_⟩
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  choose q₀ hq₀ using fun t : Loads α ((a : ℝ) + Z₁) =>
    thm_laws_cover (K := K) ea eb cNear dNear t.1 (fun ld : Loads β (c * ((a : ℝ) + Z₁) + Z₂) => ld.1) (hmax t) hε
  set q := ∑ t, q₀ t + 1 with hq
  have hq1 : (1 : ℝ) ≤ q := by rw [hq]; push_cast; linarith [show (0 : ℝ) ≤ ∑ t, (q₀ t : ℝ) from by positivity]
  choose m v hm hv tab htab using fun t => hq₀ t q
    ((Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)).trans (Nat.le_succ _))
  set lam : ℕ := ⌈ε * q⌉₊ + 1 with hlam
  have hlab : ∀ t, ∃ f : Fin (m t) → Fin lam → Bool, Function.Injective f := by
    intro t
    have h1 : (m t : ℝ) ≤ 2 ^ ((⌈ε * q⌉₊ : ℕ) : ℝ) :=
      (hm t).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _))
    rw [Real.rpow_natCast] at h1
    have h2 : m t ≤ 2 ^ ⌈ε * q⌉₊ := by exact_mod_cast h1
    have hcard : Fintype.card (Fin (m t)) ≤ Fintype.card (Fin lam → Bool) := by
      simpa using h2.trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ _))
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hcard
    exact ⟨f, f.injective⟩
  choose lab hlab using hlab
  have hm0 : ∀ t, 0 < m t := by
    intro t
    by_contra h0
    have h1 : IsEmpty (Fin (m t)) := by
      rw [show m t = 0 by omega]
      infer_instance
    have h2 := htab t fun _ _ => false
    rw [if_pos fun _ => rfl, Finset.univ_eq_empty, Finset.sum_empty] at h2
    exact one_ne_zero h2
  let L : Loads α ((a : ℝ) + Z₁) → Nc.G.Law K := fun t =>
    { Ro := U h
      Sl := Σ e : E, Fin (q * t.1 e)
      Cn := NN h
      I := Fin (m t)
      a := fun s => ea s.1
      b := fun s => eb s.1
      ab := fun s hs => s.1.2 (by
        rw [← out_mk s.1.1]
        exact Sym2.mk_isDiag_iff.2 hs)
      c := cNear
      d := dNear
      cd := fun ν e => x_ne_one ν.1.1 (by simpa using e.symm)
      lam := lam
      lab := lab t
      lab_inj := hlab t
      len := fun i ν => ∑ ld, v t i ld * ld.1 ν
      tab := tab t
      law := htab t
      conn := fun ι hι p p' => indices_agree ι hι p p' }
  have hqa : (0 : ℝ) < (a : ℝ) * q := by positivity
  refine ⟨a * q, _, inferInstance, L, fun _ => Equiv.refl _, fun _ => Equiv.refl _, by exact_mod_cast hqa,
    fun _ _ => rfl, fun t => ⟨Nat.le_add_left _ _, ⟨⟨0, hm0 t⟩⟩⟩, ?_, ?_⟩
  · -- (a)
    intro n t ht
    have hnrm : nrm α (fun e => (n e.1 : ℝ)) =
        √((b * (b - 1) / 2) * ∑ q : Sym2 (U h), if q.IsDiag then 0 else (n q : ℝ) ^ 2) := by
      rw [nrm, hE fun q => (n q : ℝ) ^ 2 / (2 / (b * (b - 1))), Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      split_ifs
      · rw [mul_zero]
      · field_simp
    rw [← hnrm] at ht
    push_cast at ht
    have hcard : ∀ (d : Loads α ((a : ℝ) + Z₁)) (e : E), (univ.filter fun s : (L d).Sl =>
        s((Equiv.refl (L d).Ro) ((L d).a s), (Equiv.refl (L d).Ro) ((L d).b s)) = e.1).card = q * d.1 e := by
      intro d e
      have e1 : (univ.filter fun s : (Σ e : E, Fin (q * d.1 e)) => s(s.1.1.out.1, s.1.1.out.2) = e.1) =
          Finset.univ.map ⟨fun j : Fin (q * d.1 e) => (⟨e, j⟩ : Σ e : E, Fin (q * d.1 e)),
            fun i j hij => by simpa using hij⟩ := by
        ext ⟨e', j⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, out_mk]
        constructor
        · intro he
          obtain rfl : e' = e := Subtype.ext he
          exact ⟨j, rfl⟩
        · rintro ⟨i, hi⟩
          rw [← (Sigma.mk.inj_iff.1 hi).1]
      refine Eq.trans ?_ ((congrArg Finset.card e1).trans (by simp))
      rfl
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · refine ⟨⟨fun _ => 0, by simp only [Nat.cast_zero, nrm_zero]; positivity⟩, fun p hp => ?_⟩
      have h0 := le_nrm α hα (fun e => (n e.1 : ℝ)) ⟨p, hp⟩
      rw [Nat.cast_zero, mul_zero] at ht
      have h1 : (n p : ℝ) ≤ 0 := h0.trans (mul_nonpos_of_nonpos_of_nonneg ht (Real.sqrt_nonneg _))
      have : n p = 0 := by exact_mod_cast le_antisymm h1 (Nat.cast_nonneg _)
      omega
    · have ht1 : (0 : ℝ) < t := by exact_mod_cast ht0
      set xx : E → ℝ := fun e => ((a : ℝ) * q * t)⁻¹ * n e.1 with hxx
      have hx0 : ∀ e, 0 ≤ xx e := fun e => by positivity
      have hx1 : nrm α xx ≤ 1 := by
        rw [hxx, nrm_smul _ (by positivity), inv_mul_le_iff₀ (by positivity), mul_one]
        exact ht
      have hσ : nrm α (fun e => ((⌈(a : ℝ) * xx e⌉₊ : ℕ) : ℝ)) ≤ (a : ℝ) + Z₁ := by
        refine (nrm_mono α hα (fun e => Nat.cast_nonneg _) fun e =>
          (Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg a) (hx0 e))).le).trans ?_
        refine (nrm_add_le α hα _ _).trans (add_le_add ?_ le_rfl)
        rw [nrm_smul α (Nat.cast_nonneg a)]
        exact mul_le_of_le_one_right (Nat.cast_nonneg a) hx1
      refine ⟨⟨_, hσ⟩, fun p hp => le_trans ?_ (Nat.mul_le_mul_right t (hcard ⟨_, hσ⟩ ⟨p, hp⟩).ge)⟩
      have h6 : (n p : ℝ) ≤ ((q * ⌈(a : ℝ) * xx ⟨p, hp⟩⌉₊ * t : ℕ) : ℝ) := by
        have e2 : (q : ℝ) * ((a : ℝ) * xx ⟨p, hp⟩) * t = n p := by
          rw [hxx]
          field_simp
        rw [← e2]
        push_cast
        gcongr
        exact Nat.le_ceil _
      exact_mod_cast h6
  · -- (b)
    intro t i
    have e0 : √(b / 2 * ∑ ν, (((L t).lam + (L t).len i ν : ℕ) : ℝ) ^ 2) =
        nrm β (fun ν => (lam : ℝ) * 1 + ∑ ld, (v t i ld : ℝ) * (ld.1 ν : ℝ)) := by
      rw [nrm, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun ν _ => ?_
      simp only [L, β]
      push_cast
      field_simp
    rw [e0]
    refine (nrm_add_le β hβ _ _).trans ?_
    have h1 : nrm β (fun ν => ∑ ld, (v t i ld : ℝ) * (ld.1 ν : ℝ)) ≤ (q : ℝ) * (c * ((a : ℝ) + Z₁) + Z₂) := by
      refine (nrm_sum_le _ β hβ _).trans ?_
      calc ∑ ld, nrm β (fun ν => (v t i ld : ℝ) * ((ld : Loads β (c * ((a : ℝ) + Z₁) + Z₂)).1 ν : ℝ)) ≤
          ∑ ld, (v t i ld : ℝ) * (c * ((a : ℝ) + Z₁) + Z₂) := by
            refine Finset.sum_le_sum fun ld _ => ?_
            rw [nrm_smul β (Nat.cast_nonneg _)]
            exact mul_le_mul_of_nonneg_left ld.2 (Nat.cast_nonneg _)
        _ = _ := by rw [← Finset.sum_mul, ← Nat.cast_sum, hv]
    rw [nrm_smul β (Nat.cast_nonneg _)]
    refine (add_le_add le_rfl h1).trans ?_
    have h2 : (lam : ℝ) ≤ ε * q + 2 := by
      have := (Nat.ceil_lt_add_one (show 0 ≤ ε * (q : ℝ) by positivity)).le
      rw [hlam]
      push_cast
      linarith
    have h3 : √(4 * (C₀ : ℝ)) = 2 * c := by
      rw [hc, Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← hZ₂, h3]
    push_cast
    have hqa' : (a : ℝ) ≤ (a : ℝ) * q := le_mul_of_one_le_right (Nat.cast_nonneg a) hq1
    have h4 : (lam : ℝ) * Z₂ ≤ 3 / 4 * (c * ((a : ℝ) * q)) := by
      calc (lam : ℝ) * Z₂ ≤ (ε * q + 2) * Z₂ := mul_le_mul_of_nonneg_right h2 hZ₂0
        _ = ε * Z₂ * q + 2 * Z₂ := by ring
        _ ≤ (a : ℝ) / 4 * q + 2 * Z₂ := by gcongr
        _ ≤ 3 / 4 * ((a : ℝ) * q) := by linarith
        _ ≤ _ := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hqa.le hc1) (by norm_num)
    have h5 : c * Z₁ + Z₂ ≤ c * ((a : ℝ) / 4) := by
      calc c * Z₁ + Z₂ ≤ c * Z₁ + c * Z₂ := by gcongr; exact le_mul_of_one_le_left hZ₂0 hc1
        _ = c * (Z₁ + Z₂) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left h5 (show (0 : ℝ) ≤ q by positivity)]

/-- **Paper: Theorem thm:laws.** "There are a finitely generated subring A of k, a positive integer a₁, and finitely
many laws over A such that (a) for every load n and t ∈ ℕ with ‖n‖ ≤ a₁t some law has n ≤ tσ; (b) for every law and
index, ‖λ + len_i‖_* ≤ √C₁·a₁." Here, as fixed before it, u is that of Theorem thm:poincare, with its constant C; C₀
is an integer that is at least 2C+1; h is a multiple of u with h ≥ 2u, h ≥ 3 and 1 + 8C₁ ≤ h/4, where C₁ = 4C₀. Such
an h exists, and the theorem holds for every one. -/
theorem thm_laws {K : Type} [Field K] (hK : Contracting K) :
    ∃ u : ℕ, 2 ≤ u ∧ ∃ (C : ℝ) (C₀ : ℕ), 0 ≤ C ∧ PoincareBound K u C ∧ 2 * C + 1 ≤ (C₀ : ℝ) ∧
      (∃ h : ℕ, u ∣ h ∧ 2 * u ≤ h ∧ 3 ≤ h ∧ 1 + 8 * (4 * (C₀ : ℝ)) ≤ (h : ℝ) / 4) ∧
      ∀ (h : ℕ) [NeZero h], u ∣ h → 2 * u ≤ h → 3 ≤ h → 1 + 8 * (4 * (C₀ : ℝ)) ≤ (h : ℝ) / 4 →
        ∃ (A : Subring K) (_ : Algebra.FiniteType ℤ A) (a₁ : ℕ) (Di : Type) (_ : Fintype Di) (L : Di → Nc.G.Law A)
          (ro : ∀ d, (L d).Ro ≃ U h) (cn : ∀ d, (L d).Cn ≃ NN h), 0 < a₁ ∧
          (∀ d ν, s(ro d ((L d).c ν), ro d ((L d).d ν)) = s(cNear (cn d ν), dNear (cn d ν))) ∧
          (∀ d, 1 ≤ (L d).lam ∧ Nonempty (L d).I) ∧
          (∀ (n : Sym2 (U h) → ℕ) (t : ℕ),
            √(((Fintype.card (U h) : ℝ) * ((Fintype.card (U h) : ℝ) - 1) / 2) *
                ∑ q : Sym2 (U h), if q.IsDiag then 0 else (n q : ℝ) ^ 2) ≤ a₁ * t →
            ∃ d, ∀ q : Sym2 (U h), ¬ q.IsDiag →
              n q ≤ (univ.filter fun e : (L d).Sl => s(ro d ((L d).a e), ro d ((L d).b e)) = q).card * t) ∧
          ∀ d i, √((Fintype.card (U h) : ℝ) / 2 * ∑ ν, (((L d).lam + (L d).len i ν : ℕ) : ℝ) ^ 2) ≤
            √(4 * (C₀ : ℝ)) * a₁ := by
  obtain ⟨u, hu, C, C₀, hC, hP, hC₀, hpairs⟩ := thm_laws_poincare hK
  refine ⟨u, hu, C, C₀, hC, hP, hC₀, ?_, fun h _ hdvd h2u h3 _ => ?_⟩
  · have hl : 4 * (1 + 8 * (4 * C₀)) + 3 ≤ (4 * (1 + 8 * (4 * C₀)) + 3) * u :=
      Nat.le_mul_of_pos_right _ (by omega)
    refine ⟨(4 * (1 + 8 * (4 * C₀)) + 3) * u, dvd_mul_left _ _, Nat.mul_le_mul_right u (by omega), by omega, ?_⟩
    rw [le_div_iff₀ (by norm_num)]
    exact_mod_cast (by omega : (1 + 8 * (4 * C₀)) * 4 ≤ (4 * (1 + 8 * (4 * C₀)) + 3) * u)
  · have hC₀1 : 1 ≤ C₀ := by
      have : (1 : ℝ) ≤ (C₀ : ℝ) := by linarith
      exact_mod_cast this
    obtain ⟨a₁, Di, fD, L, ro, cn, ha₁, hends, hlam, ha, hb⟩ :=
      thm_laws_over_field (by omega) hC₀1 (hpairs h hdvd h2u)
    obtain ⟨A, hA, hmem⟩ := thm_laws_ring L
    exact ⟨A, hA, a₁, Di, fD, fun d => restrictLaw (L d) A (hmem d), ro, cn, ha₁, hends, hlam, ha, hb⟩

/-- What the sections on towers and cuts take from Theorem thm:laws. -/
theorem exists_laws {K : Type} [Field K] (hK : Contracting K) :
    ∃ (h : ℕ) (_ : NeZero h), 3 ≤ h ∧ ∃ (A : Subring K) (_ : Algebra.FiniteType ℤ A)
      (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)), 1 + 8 * VL.C₁ ≤ (h : ℝ) / 4 ∧
        ∃ g : ℕ, 2 * VL.C₁ * (VL.a₁ : ℝ) ^ 2 = g := by
  classical
  obtain ⟨u, -, C, C₀, -, -, -, ⟨h, hdvd, h2u, h3, hgain⟩, hlaws⟩ := thm_laws hK
  have hne : NeZero h := ⟨by omega⟩
  obtain ⟨A, hA, a₁, Di, fD, L, ro, cn, ha₁, hends, hlam, ha, hb⟩ := hlaws h hdvd h2u h3 hgain
  have hcard : Fintype.card (U h) = 2 ^ ee h := card_U h
  refine ⟨h, hne, h3, A, hA,
    { Di := Di, L := L, ro := ro, cn := cn, ends := hends
      lam_pos := fun d => (hlam d).1, nonempty := fun d => (hlam d).2
      a₁ := a₁, a₁_pos := ha₁, C₁ := 4 * (C₀ : ℝ), C₁_nonneg := by positivity
      G₁ := 8 * C₀ * a₁ ^ 2, G₁_le := le_of_eq (by push_cast; ring)
      L1 := fun n t ht => ha n t (by rw [hcard]; exact ht)
      L2 := fun d i => ?_ }, hgain, 8 * C₀ * a₁ ^ 2, by push_cast; ring⟩
  have h1 := hb d i
  rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by positivity), hcard] at h1
  push_cast at h1
  rw [← @Nat.cast_le ℝ]
  push_cast
  linarith

end Paper
