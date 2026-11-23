/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Gauges

/-!
# The paper, section "Tensors, prices and duality": extension

The subsection "Extension": Proposition prop:extend, with the steps of its proof.
-/

namespace Paper

open Ov Ov.Ten Ov.Duality Nc.Price Finset

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

variable {I' : Type} [Fintype I'] [DecidableEq I'] {L : Type} [Fintype L]

/-- The product on the right in Proposition prop:extend: "Call the product on the right f(t)". -/
noncomputable def extendProduct (π : L → I' → I) (θ : L → ℝ) (φ : Spec K I) (t : Ten K I') : ℝ :=
  ∏ l, φ.F (Ten.push (π l) t) ^ θ l

/-- Proof of Proposition prop:extend: "Call the product on the right f(t); it is multiplicative and monotone." Also f ≥ 0 and
f(1) = 1. -/
theorem prop_extend_product (π : L → I' → I) (θ : L → ℝ) (hθ : ∀ l, 0 ≤ θ l) (φ : Spec K I) :
    (∀ t, 0 ≤ extendProduct π θ φ t) ∧ extendProduct π θ φ 1 = 1 ∧
    (∀ s t, extendProduct π θ φ (s * t) = extendProduct π θ φ s * extendProduct π θ φ t) ∧
    ∀ {s t}, Restr s t → extendProduct π θ φ s ≤ extendProduct π θ φ t := by
  refine ⟨fun t => Finset.prod_nonneg fun l _ => Real.rpow_nonneg (φ.nonneg _) _, ?_, fun s t => ?_, fun {s t} h => ?_⟩
  · refine Finset.prod_eq_one fun l _ => ?_
    rw [(def_spectral_congr φ).2 (tensor_push_one _), φ.one, Real.one_rpow]
  · rw [extendProduct, extendProduct, extendProduct, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [(def_spectral_congr φ).2 (tensor_push_mul _ s t), φ.mul, Real.mul_rpow (φ.nonneg _) (φ.nonneg _)]
  · exact Finset.prod_le_prod (fun l _ => Real.rpow_nonneg (φ.nonneg _) _) fun l _ =>
      Real.rpow_le_rpow (φ.nonneg _) ((def_spectral_congr φ).1 ((tensor_push_cover _).2 h)) (hθ l)

/-- Proof of Proposition prop:extend: "Suppose that ιA = ∑ s_j, each s_j a restriction of b_j. As ιA has trivial index sets
outside ι(I), so has every s_j; so s_j = ιa_j with ∑ a_j = A. Push-forwards preserve restrictions, so a_j = π_l s_j is a
restriction of π_l b_j for every l." -/
theorem prop_extend_cover (ι : I → I') {A : Ten K I} {κ : Type} [Fintype κ] {b : κ → Ten K I'}
    (h : Ten.SumRestr (Ten.push ι A) b) :
    ∃ c : κ → Ten K I, Ten.SumRestr A c ∧
      ∀ k, ∀ π : I' → I, (∀ i, π (ι i) = i) → Ten.Restr (c k) (Ten.push π (b k)) := by
  obtain ⟨v, hv, hr⟩ := Ten.sumRestr_iff.1 h
  let emb : (∀ i, A.ι i) → ∀ q, (Ten.push ι A).ι q := fun x q j => x j.1
  refine ⟨fun k => A.withVal fun x => v k (emb x), Ten.SumRestr.of_withVal A _ fun x => ?_,
    fun k π hπ => ?_⟩
  · exact hv (emb x)
  · have h1 : Ten.Restr (Ten.push ι (A.withVal fun x => v k (emb x)))
        ((Ten.push ι A).withVal (v k)) := by
      refine Ten.Restr.of_map' (fun q x => x) fun x => ?_
      rw [Ten.push_val]
      change v k _ = v k _
      congr 1
      funext q j
      obtain ⟨j, rfl⟩ := j
      rfl
    have h2 := (tensor_push_cover π).2 (h1.trans (hr k))
    have h3 : π ∘ ι = id := funext hπ
    have h4 := tensor_push_comp π ι (A.withVal fun x => v k (emb x))
    rw [h3] at h4
    exact (h4.trans (tensor_push_id _)).2.trans h2

/-- Proof of Proposition prop:extend: "So φ(A) ≤ ∑ φ(a_j) ≤ ∑ f(b_j)", for every cover (b_j) of ιA. -/
theorem prop_extend_lower (ι : I → I') (π : L → I' → I) (hπ : ∀ l i, π l (ι i) = i) (θ : L → ℝ) (hθ : ∀ l, 0 ≤ θ l)
    (hθ1 : ∑ l, θ l = 1) (φ : Spec K I) (A : Ten K I) {κ : Type} [Fintype κ] (b : κ → Ten K I')
    (hb : SumRestr (Ten.push ι A) b) : φ.F A ≤ ∑ k, extendProduct π θ φ (b k) := by
  obtain ⟨a, ha, hr⟩ := prop_extend_cover ι hb
  refine (φ.le_sum A a ha).trans (Finset.sum_le_sum fun k _ => ?_)
  -- φ(a_j) is at most every factor φ(π_l b_j), so at most their weighted geometric mean
  rcases (φ.nonneg (a k)).eq_or_lt with h0 | h0
  · rw [← h0]
    exact (prop_extend_product π θ hθ φ).1 _
  · calc φ.F (a k) = φ.F (a k) ^ (∑ l, θ l) := by rw [hθ1, Real.rpow_one]
      _ = ∏ l, φ.F (a k) ^ θ l := Real.rpow_sum_of_pos h0 _ _
      _ ≤ extendProduct π θ φ (b k) := Finset.prod_le_prod (fun l _ => Real.rpow_nonneg h0.le _) fun l _ =>
        Real.rpow_le_rpow h0.le ((def_spectral_congr φ).1 (hr k _ (hπ l))) (hθ l)

/-- Proof of Proposition prop:extend: "f(ιA) = φ(A), as π_l ι = id." -/
theorem prop_extend_upper (ι : I → I') (π : L → I' → I) (hπ : ∀ l i, π l (ι i) = i) (θ : L → ℝ)
    (hθ1 : ∑ l, θ l = 1) (φ : Spec K I) (A : Ten K I) : extendProduct π θ φ (Ten.push ι A) = φ.F A := by
  have retr : ∀ l, Equi (Ten.push (π l) (Ten.push ι A)) A := by
    intro l
    have h := tensor_push_comp (π l) ι A
    rw [show π l ∘ ι = id from funext (hπ l)] at h
    exact h.trans (tensor_push_id _)
  have h1 : extendProduct π θ φ (Ten.push ι A) = ∏ l, φ.F A ^ θ l :=
    Finset.prod_congr rfl fun l _ => by rw [(def_spectral_congr φ).2 (retr l)]
  rw [h1]
  rcases (φ.nonneg A).eq_or_lt with h0 | h0
  · obtain ⟨l, hl⟩ : ∃ l, θ l ≠ 0 := by
      by_contra hne
      push Not at hne
      simp [hne] at hθ1
    rw [← h0]
    exact Finset.prod_eq_zero (Finset.mem_univ l) (Real.zero_rpow hl)
  · rw [← Real.rpow_sum_of_pos h0, hθ1, Real.rpow_one]

/-- Proof of Proposition prop:extend: there is "a gauge with p ≤ f and p(ιA) = φ(A) for all A". In the proof it is the printed
one: "Let p(t) be the infimum of ∑ f(b_j) over the covers (b_j) of t. … With A = 1 this shows p(1) = 1". -/
theorem prop_extend_gauge (ι : I → I') (π : L → I' → I) (hπ : ∀ l i, π l (ι i) = i) (θ : L → ℝ) (hθ : ∀ l, 0 ≤ θ l)
    (hθ1 : ∑ l, θ l = 1) (φ : Spec K I) :
    ∃ p : PreSpec K I', (∀ t, p.p t ≤ extendProduct π θ φ t) ∧ ∀ A : Ten K I, p.p (Ten.push ι A) = φ.F A := by
  classical
  obtain ⟨f0, f1, fmul, fmono⟩ := prop_extend_product π θ hθ φ
  set f : Ten K I' → ℝ := extendProduct π θ φ with hf
  have hcongr : ∀ {s t : Ten K I'}, Equi s t → f s = f t := fun h => le_antisymm (fmono h.1) (fmono h.2)
  -- the sums ∑ f(b_j) over the covers of a class of tensors
  set S : Cls K I' → Set ℝ := fun m => {W | ∃ (κ : Type) (_ : Fintype κ) (b : κ → Cls K I'),
    (tenCover K I').cov m b ∧ ∑ k, f (rep (b k)) = W} with hS
  have hne : ∀ t, (S t).Nonempty := fun t =>
    ⟨_, Unit, inferInstance, fun _ => t, (tenCover K I').refl t, rfl⟩
  have h0 : ∀ t, ∀ w ∈ S t, 0 ≤ w := by
    rintro t w ⟨κ, _, b, -, rfl⟩
    exact Finset.sum_nonneg fun k _ => f0 _
  have hlow : ∀ A : Ten K I, ∀ w ∈ S (cls (Ten.push ι A)), φ.F A ≤ w := by
    rintro A w ⟨κ, _, b, hb, rfl⟩
    exact prop_extend_lower ι π hπ θ hθ hθ1 φ A _ ((rep_cls _).2.trans_sum hb)
  have hup : ∀ t : Ten K I', f t ∈ S (cls t) := fun t =>
    ⟨Unit, inferInstance, fun _ => cls t, (tenCover K I').refl _, by
      simpa using hcongr (rep_cls t)⟩
  have hpre : IsPre (tenCover K I') (fun t => sInf (S t)) := by
    refine isPre_sInf hne h0 ?_ ?_ ?_ ?_
    · have h := hup 1
      rwa [f1, cls_one] at h
    · intro w hw
      rw [← cls_one, ← cls_eq.2 (tensor_push_one ι)] at hw
      have h := hlow 1 w hw
      rwa [φ.one] at h
    · rintro s t a ⟨κ, _, b, hb, rfl⟩ a' ⟨κ', _, b', hb', rfl⟩
      refine ⟨Σ _ : κ, κ', inferInstance, _, (tenCover K I').mul_mul hb hb', ?_⟩
      rw [Fintype.sum_sigma, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
      rw [← fmul]
      exact hcongr (rep_cls _)
    · intro κ _ t b hb w hw
      choose μ i c hc hw using hw
      refine ⟨_, ⟨Σ k, μ k, inferInstance, _, (tenCover K I').bind hb hc, rfl⟩, ?_⟩
      rw [Fintype.sum_sigma]
      exact (Finset.sum_congr rfl fun k _ => hw k).le
  have Pf : ∀ t, (ofCls hpre).p t ≤ f t := fun t => csInf_le ⟨0, fun _ hw => h0 _ _ hw⟩ (hup t)
  exact ⟨ofCls hpre, Pf, fun A => le_antisymm ((Pf _).trans (prop_extend_upper ι π hπ θ hθ1 φ A).le)
    (le_csInf (hne _) (hlow A))⟩

/-- Proof of Proposition prop:extend: "let c = φ(C) and q(t) = inf p(t ιCⁿ)/cⁿ. As p(ιCⁿ) = cⁿ, this is a gauge below p that
keeps (1, ιC, 1/c)." Stated for any gauge p and any tensor f with p(f) > 0 and p(fⁿ) = p(f)ⁿ: some gauge q below p keeps
(1, f, 1/p(f)). It is the one of prop_gauge_localize, for the classes of tensors. -/
theorem prop_extend_localize (p : PreSpec K I) (f : Ten K I) (hf : 0 < p.p f)
    (hpow : ∀ n, p.p (Ten.kpow f n) = p.p f ^ n) :
    ∃ q : PreSpec K I, (∀ t, q.p t ≤ p.p t) ∧ ∀ t, q.p (t * 1) ≤ (p.p f)⁻¹ * q.p (t * f) := by
  obtain ⟨q, hq, hle, hk, -⟩ := prop_gauge_localize (isPre_onCls p) (f := cls f) (by simpa using hf)
    (fun n => by rw [← cls_kpow, onCls_cls, onCls_cls, hpow])
  refine ⟨ofCls hq, fun t => (hle _).trans (onCls_cls p t).le, fun t => ?_⟩
  have := hk (cls t)
  rw [onCls_cls] at this
  change q (cls (t * 1)) ≤ _ * q (cls (t * f))
  rwa [cls_mul, cls_mul]

/-- **Paper: Proposition prop:extend.** "Let ι : I → I′ and π_l : I′ → I, l ≤ L, be maps with π_l ι = id, let θ_l ≥ 0
add up to 1, let φ be a spectral point on I, and let C be a tensor on I. There is a spectral point φ′ on I′ with
φ′(t) ≤ ∏ φ(π_l t)^θ_l for all t, and φ′(ιC) = φ(C)." The maps are indexed by any finite type L. -/
theorem prop_extend (ι : I → I') (π : L → I' → I) (hπ : ∀ l i, π l (ι i) = i) (θ : L → ℝ) (hθ : ∀ l, 0 ≤ θ l)
    (hθ1 : ∑ l, θ l = 1) (φ : Spec K I) (C : Ten K I) :
    ∃ φ' : Spec K I', (∀ t, φ'.F t ≤ ∏ l, φ.F (Ten.push (π l) t) ^ θ l) ∧ φ'.F (Ten.push ι C) = φ.F C := by
  obtain ⟨p, pf, pA⟩ := prop_extend_gauge ι π hπ θ hθ hθ1 φ
  rcases (φ.nonneg C).eq_or_lt with hC | hC
  · -- φ(C) = 0 (the printed case C = 0)
    obtain ⟨φ', hφ', -⟩ := prop_gauge p
    exact ⟨φ', fun t => (hφ' t).trans (pf t),
      le_antisymm ((hφ' _).trans (pA C).le) (by rw [← hC]; exact φ'.nonneg _)⟩
  · obtain ⟨q, hq, hqk⟩ := prop_extend_localize p (Ten.push ι C) (by rwa [pA]) (fun n => by
      rw [← p.congr (Equi.push_kpow ι C n), pA, pA, φ.kpow])
    -- "A spectral point φ′ ≤ q that keeps this triple has c ≤ φ′(ιC) ≤ f(ιC) = c."
    obtain ⟨φ', hφ', hk⟩ := prop_gauge q
    refine ⟨φ', fun t => (hφ' t).trans ((hq t).trans (pf t)),
      le_antisymm ((hφ' _).trans ((hq _).trans (pA C).le)) ?_⟩
    have h1 := hk 1 (Ten.push ι C) _ (by rw [pA]; positivity) hqk 1
    rw [(def_spectral_congr φ').2 (Equi.one_mul _), (def_spectral_congr φ').2 (Equi.one_mul _), φ'.one, pA,
      inv_mul_eq_div, le_div_iff₀ hC, one_mul] at h1
    exact h1

end Paper
