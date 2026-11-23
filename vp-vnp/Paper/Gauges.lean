/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Tensors
import Nc.Price.Cover

/-!
# The paper, section "Tensors, prices and duality": gauges and duality

The subsection "Gauges": Proposition prop:gauge and Theorem thm:duality, with the steps of their proofs. Both proofs are
carried out in the commutative monoid of the classes of tensors (Ov.Duality.Cls) with its covering relation.
-/

namespace Paper

open Ov Ov.Ten Ov.Duality Ov.Duality.IsPre Nc.Price Finset

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-- "A gauge on I is a function p ≥ 0 on tensors with p(1) = 1, p(st) ≤ p(s)p(t) and p(s) ≤ ∑ p(t_j) whenever s is covered by
the t_j." -/
theorem def_gauge (p : Ten K I → ℝ) :
    (∃ P : PreSpec K I, P.p = p) ↔ (∀ t, 0 ≤ p t) ∧ p 1 = 1 ∧ (∀ s t, p (s * t) ≤ p s * p t) ∧
      ∀ (r : ℕ) (s : Ten K I) (t : Fin r → Ten K I), SumRestr s t → p s ≤ ∑ j, p (t j) := by
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨P.nonneg, P.one, P.mul_le, fun r s t h => P.le_sum s t h⟩
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨⟨p, h0, h1, h2, fun {κ} _ s b h => ?_⟩, rfl⟩
    classical
    refine (h3 _ s (b ∘ (Fintype.equivFin κ).symm) (h.reindex (Fintype.equivFin κ).symm)).trans (le_of_eq ?_)
    exact Fintype.sum_equiv (Fintype.equivFin κ).symm _ _ fun _ => rfl

section Monoid

/-! The proof of Proposition prop:gauge, for a commutative monoid M with a covering relation D (for us: the classes of
tensors). A gauge on M is a function with Ov.Duality.IsPre; Ov.Duality.Keeps p x y c says that p keeps (x, y, c). -/

variable {M : Type*} [CommMonoid M] {D : Cover M} {p : M → ℝ}

/-- Proof of Proposition prop:gauge: "The gauges below the given one that keep its triples are closed under infima of
chains." The infimum of a chain (or a directed family) of gauges is a gauge below them that keeps every triple which all
of them keep. -/
theorem prop_gauge_chain {ι : Type*} [Nonempty ι] {P : ι → M → ℝ} (dir : Directed (· ≥ ·) P)
    (hP : ∀ i, IsPre D (P i)) :
    IsPre D (fun t => ⨅ i, P i t) ∧ (∀ i t, ⨅ j, P j t ≤ P i t) ∧
      ∀ x y c, 0 ≤ c → (∀ i, Keeps (P i) x y c) → Keeps (fun t => ⨅ i, P i t) x y c :=
  ⟨isPre_iInf dir (fun i => (hP i).nonneg) (fun i => (hP i).one) (fun i s t => ⟨i, (hP i).mul_le s t⟩)
      (fun i _ _ t b hb => (hP i).le_sum t b hb),
    fun i t => ciInf_le ⟨0, by rintro _ ⟨j, rfl⟩; exact (hP j).nonneg t⟩ i,
    fun _ _ _ hc h => keeps_iInf (fun i => (hP i).nonneg) hc h⟩

/-- Proof of Proposition prop:gauge: "By Zorn's lemma there is a minimal one, p": a gauge below p₀ that keeps the triples of
p₀, and that is equal to every such gauge below it. -/
theorem prop_gauge_minimal {p₀ : M → ℝ} (h₀ : IsPre D p₀) :
    ∃ p : M → ℝ, IsPre D p ∧ (∀ t, p t ≤ p₀ t) ∧ (∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps p x y c) ∧
      ∀ q : M → ℝ, IsPre D q → (∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps q x y c) → (∀ t, q t ≤ p t) →
        ∀ t, q t = p t := by
  set Q : Set (M → ℝ)ᵒᵈ := {q | IsPre D (OrderDual.ofDual q) ∧
    ∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps (OrderDual.ofDual q) x y c} with hQ
  obtain ⟨m, hm0, hmax⟩ := zorn_le_nonempty₀ Q (by
    intro c hcQ hchain y hy
    have : Nonempty c := ⟨⟨y, hy⟩⟩
    obtain ⟨h1, h2, h3⟩ := prop_gauge_chain (D := D) (P := fun i : c => OrderDual.ofDual i.1) (by
      intro i j
      rcases hchain.total i.2 j.2 with hij | hij
      · exact ⟨j, hij, le_refl _⟩
      · exact ⟨i, le_refl _, hij⟩) fun i => (hcQ i.2).1
    exact ⟨OrderDual.toDual (fun t => ⨅ i : c, (OrderDual.ofDual i.1) t),
      ⟨h1, fun x y c hc hk => h3 x y c hc fun i => (hcQ i.2).2 x y c hc hk⟩, fun z hz t => h2 ⟨z, hz⟩ t⟩)
    (OrderDual.toDual p₀) ⟨h₀, fun _ _ _ _ hk => hk⟩
  refine ⟨OrderDual.ofDual m, hmax.1.1, hm0, hmax.1.2, fun q h1 h2 h3 t => ?_⟩
  have h4 : OrderDual.ofDual m ≤ q := hmax.2 (y := OrderDual.toDual q) ⟨h1, h2⟩ h3
  exact le_antisymm (h3 t) (h4 t)

/-- Proof of Proposition prop:gauge, for r(t) = inf p(tⁿ)^(1/n): "If s is covered by t_1, …, t_l, then sⁿ is covered by their
words of length n; grouping these … and bounding p(t_jᵃ) ≤ c_δ (r(t_j) + δ)ᵃ gives r(s) ≤ ∑ r(t_j)." In Lean r(t) is the infimum
of the a > 0 with p(tⁿ) ≤ C·aⁿ for some C and all n (Ov.Duality.IsPre.rad; it is the printed number by prop_gauge_radius_eq),
and the words are bounded by induction on n. -/
theorem prop_gauge_radius_cover (h : IsPre D p) {κ : Type} [Fintype κ] (t : M) (b : κ → M) (hb : D.cov t b) :
    sInf (rad p t) ≤ ∑ k, sInf (rad p (b k)) := by
  classical
  have h0 : ∀ t, 0 ≤ sInf (rad p t) := fun t => Real.sInf_nonneg fun _ ha => ha.1.le
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε := δ / (Fintype.card κ + 1) with hεd
  have hε : 0 < ε := by positivity
  set a : M → ℝ := fun y => sInf (rad p y) + ε with ha
  have ha0 : ∀ y, 0 < a y := fun y => by have := h0 y; simp only [ha]; linarith
  have hmem : ∀ y, ∃ C : ℝ, ∀ m : ℕ, p (y ^ m) ≤ C * a y ^ m := fun y =>
    (h.mem_rad_of_lt (show sInf (rad p y) < a y by simp only [ha]; linarith)).2
  choose C hC using hmem
  set S := Finset.univ.image b with hS
  set A := ∑ k, a (b k) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => (ha0 _).le
  have key : ∀ n : ℕ, ∀ e : M → ℕ, p ((∏ y ∈ S, y ^ e y) * t ^ n) ≤
      (∏ y ∈ S, C y) * (∏ y ∈ S, a y ^ e y) * A ^ n := by
    intro n
    induction n with
    | zero => intro e; simpa using h.prod_bound S a C ha0 hC e
    | succ n ih =>
      intro e
      have h1 := h.le_sum _ _ (D.mul ((∏ y ∈ S, y ^ e y) * t ^ n) hb)
      have h2 : t * ((∏ y ∈ S, y ^ e y) * t ^ n) = (∏ y ∈ S, y ^ e y) * t ^ (n + 1) := by
        rw [pow_succ', mul_left_comm]
      rw [h2] at h1
      refine h1.trans ?_
      have h3 : ∀ k, p (b k * ((∏ y ∈ S, y ^ e y) * t ^ n)) ≤
          (∏ y ∈ S, C y) * (∏ y ∈ S, a y ^ e y) * A ^ n * a (b k) := by
        intro k
        set y := b k with hy
        have hyS : y ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ _)
        have h4 := ih (fun z => if z = y then e z + 1 else e z)
        have e1 : ∏ z ∈ S, z ^ (if z = y then e z + 1 else e z) =
            y * ∏ z ∈ S, z ^ e z := by
          rw [← Finset.mul_prod_erase S _ hyS, ← Finset.mul_prod_erase S (fun z => z ^ e z) hyS]
          rw [if_pos rfl, pow_succ', mul_assoc]
          congr 2
          refine Finset.prod_congr rfl fun z hz => ?_
          rw [if_neg (Finset.ne_of_mem_erase hz)]
        have e2 : ∏ z ∈ S, a z ^ (if z = y then e z + 1 else e z) =
            a y * ∏ z ∈ S, a z ^ e z := by
          rw [← Finset.mul_prod_erase S _ hyS,
            ← Finset.mul_prod_erase S (fun z => a z ^ e z) hyS]
          rw [if_pos rfl, pow_succ', mul_assoc]
          congr 2
          refine Finset.prod_congr rfl fun z hz => ?_
          rw [if_neg (Finset.ne_of_mem_erase hz)]
        rw [e1, e2] at h4
        rw [← mul_assoc]
        refine h4.trans (le_of_eq ?_)
        ring
      refine (Finset.sum_le_sum fun k _ => h3 k).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, ← hA]
      ring
  have h5 : sInf (rad p t) ≤ A + ε := by
    refine csInf_le (rad_bdd p t) ⟨by linarith, ∏ y ∈ S, C y, fun m => ?_⟩
    have h6 := key m (fun _ => 0)
    simp only [pow_zero, Finset.prod_const_one, one_mul, mul_one] at h6
    refine h6.trans ?_
    have : (0 : ℝ) ≤ ∏ y ∈ S, C y :=
      Finset.prod_nonneg fun y _ => zero_le_one.trans (h.rad_const_pos (hC y))
    gcongr
    linarith
  have h7 : A = ∑ k, sInf (rad p (b k)) + Fintype.card κ * ε := by
    rw [hA, ha, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h8 : ((Fintype.card κ : ℝ) + 1) * ε = δ := by rw [hεd]; field_simp
  linarith

/-- Proof of Proposition prop:gauge: r is a gauge. "Clearly r(1) = 1 and r(st) ≤ r(s)r(t)"; for covers see
prop_gauge_radius_cover. -/
theorem prop_gauge_radius (h : IsPre D p) : IsPre D (fun t => sInf (rad p t)) := by
  classical
  have h0 : ∀ t, 0 ≤ sInf (rad p t) := fun t => Real.sInf_nonneg fun _ ha => ha.1.le
  refine ⟨h0, le_antisymm ?_ ?_, ?_, fun t b hb => prop_gauge_radius_cover h t b hb⟩
  · refine le_of_forall_pos_le_add fun δ hδ => csInf_le (rad_bdd p 1) ?_
    simpa [h.one] using h.mem_rad 1 hδ
  · refine le_csInf ⟨_, h.mem_rad 1 one_pos⟩ ?_
    rintro a ⟨ha, C, hC⟩
    by_contra hlt
    rw [not_le] at hlt
    have hC1 := h.rad_const_pos hC
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / C by positivity) hlt
    have := hC m
    rw [one_pow, h.one] at this
    rw [lt_div_iff₀ (by positivity)] at hm
    linarith
  · intro s t
    have key : ∀ a ∈ rad p s, ∀ b ∈ rad p t, sInf (rad p (s * t)) ≤ a * b := by
      rintro a ⟨ha, C, hC⟩ b ⟨hb, C', hC'⟩
      refine csInf_le (rad_bdd p _) ⟨by positivity, C * C', fun m => ?_⟩
      rw [mul_pow, mul_pow]
      have h1 := h.rad_const_pos hC
      calc p (s ^ m * t ^ m) ≤ p (s ^ m) * p (t ^ m) := h.mul_le _ _
        _ ≤ (C * a ^ m) * (C' * b ^ m) :=
          mul_le_mul (hC m) (hC' m) (h.nonneg _) (by positivity)
        _ = _ := by ring
    have hs := h0 s
    have ht := h0 t
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set A := sInf (rad p s) with hA
    set B := sInf (rad p t) with hB
    obtain ⟨ε, hε, hε1, hε2⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ε * (A + B + 1) ≤ δ := by
      refine ⟨min 1 (δ / (A + B + 1)), by positivity, min_le_left _ _, ?_⟩
      calc min 1 (δ / (A + B + 1)) * (A + B + 1) ≤ δ / (A + B + 1) * (A + B + 1) := by
            gcongr; exact min_le_right _ _
        _ = δ := by field_simp
    have := key (A + ε) (h.mem_rad_of_lt (by linarith)) (B + ε) (h.mem_rad_of_lt (by linarith))
    nlinarith

/-- Proof of Proposition prop:gauge: r ≤ p. -/
theorem prop_gauge_radius_le (h : IsPre D p) (t : M) : sInf (rad p t) ≤ p t :=
  le_of_forall_pos_le_add fun _ hδ => csInf_le (rad_bdd p t) (h.mem_rad t hδ)

/-- Proof of Proposition prop:gauge: "If p keeps (x, y, c), then p(tⁿxⁿ) ≤ cⁿ p(tⁿyⁿ), so r keeps it." -/
theorem prop_gauge_radius_keeps (h : IsPre D p) {x y : M} {c : ℝ} (hc : 0 ≤ c) (hk : Keeps p x y c) :
    Keeps (fun t => sInf (rad p t)) x y c := by
  intro t
  -- first p(s x^m) ≤ c^m p(s y^m) for all m and s
  have h1 : ∀ (m : ℕ) (s : M), p (s * x ^ m) ≤ c ^ m * p (s * y ^ m) := by
    intro m
    induction m with
    | zero => intro s; simp
    | succ m ih =>
      intro s
      calc p (s * x ^ (m + 1)) = p (s * x * x ^ m) := by rw [pow_succ', mul_assoc]
        _ ≤ c ^ m * p (s * x * y ^ m) := ih _
        _ = c ^ m * p (s * y ^ m * x) := by rw [mul_right_comm]
        _ ≤ c ^ m * (c * p (s * y ^ m * y)) := by gcongr; exact hk _
        _ = c ^ (m + 1) * p (s * y ^ (m + 1)) := by
          rw [mul_assoc s, ← pow_succ, pow_succ c m, mul_assoc]
  have h2 : ∀ a ∈ rad p (t * y), sInf (rad p (t * x)) ≤ c * a := by
    rintro a ⟨ha, C, hC⟩
    have hC1 := h.rad_const_pos hC
    refine le_of_forall_pos_le_add fun δ hδ => csInf_le (rad_bdd p _) ⟨by positivity, C, fun m => ?_⟩
    calc p ((t * x) ^ m) = p (t ^ m * x ^ m) := by rw [mul_pow]
      _ ≤ c ^ m * p (t ^ m * y ^ m) := h1 m _
      _ ≤ c ^ m * (C * a ^ m) := by rw [← mul_pow]; gcongr; exact hC m
      _ = C * (c * a) ^ m := by ring
      _ ≤ C * (c * a + δ) ^ m := by gcongr; linarith
  rcases hc.eq_or_lt with rfl | hc
  · simpa using h2 _ (h.mem_rad _ one_pos)
  · have h3 : sInf (rad p (t * x)) / c ≤ sInf (rad p (t * y)) := by
      refine le_csInf ⟨_, h.mem_rad _ one_pos⟩ fun a ha => ?_
      rw [div_le_iff₀ hc]
      exact (h2 a ha).trans (mul_comm _ _).le
    rw [div_le_iff₀ hc] at h3
    exact h3.trans (mul_comm _ _).le

/-- If p((tⁿ)ᵐ) ≤ C·aᵐ for all m, then p(tᵐ) ≤ C′·bᵐ for all m, with bⁿ = a. -/
theorem prop_gauge_radius_root (h : IsPre D p) {t : M} {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : a ∈ rad p (t ^ n)) :
    a ^ ((n : ℝ)⁻¹) ∈ rad p t := by
  obtain ⟨ha, C, hC⟩ := ha
  have hC1 := h.rad_const_pos hC
  set b := a ^ ((n : ℝ)⁻¹) with hb
  have hb0 : 0 < b := Real.rpow_pos_of_pos ha _
  have hbn : b ^ n = a := Real.rpow_inv_natCast_pow ha.le (by omega)
  set E := max 1 (p t / b) with hE
  have hE1 : 1 ≤ E := le_max_left _ _
  refine ⟨hb0, C * E ^ n, fun m => ?_⟩
  have h1 : t ^ m = (t ^ n) ^ (m / n) * t ^ (m % n) := by
    rw [← pow_mul, ← pow_add, Nat.div_add_mod]
  have h2 : b ^ m = a ^ (m / n) * b ^ (m % n) := by
    rw [← hbn, ← pow_mul, ← pow_add, Nat.div_add_mod]
  have h3 : p t ≤ E * b := by
    rw [← div_le_iff₀ hb0]; exact le_max_right _ _
  have h4 : p (t ^ (m % n)) ≤ E ^ n * b ^ (m % n) := by
    calc p (t ^ (m % n)) ≤ p t ^ (m % n) := h.pow_le _ _
      _ ≤ (E * b) ^ (m % n) := pow_le_pow_left₀ (h.nonneg t) h3 _
      _ = E ^ (m % n) * b ^ (m % n) := mul_pow _ _ _
      _ ≤ E ^ n * b ^ (m % n) := by
        gcongr
        exact (Nat.mod_lt _ hn).le
  rw [h1, h2]
  calc _ ≤ p ((t ^ n) ^ (m / n)) * p (t ^ (m % n)) := h.mul_le _ _
    _ ≤ (C * a ^ (m / n)) * (E ^ n * b ^ (m % n)) :=
      mul_le_mul (hC _) h4 (h.nonneg _) (by positivity)
    _ = _ := by ring

/-- Proof of Proposition prop:gauge: "Let r(t) = inf_{n≥1} p(tⁿ)^(1/n)". The number r(t) of the Lean proof, the infimum of the
a > 0 with p(tⁿ) ≤ C·aⁿ for some C and all n, is the printed one. (That r(t) + δ is such an a, Ov.Duality.IsPre.mem_rad_of_lt,
is the printed bound p(tᵃ) ≤ c_δ (r(t) + δ)ᵃ, which the paper takes from Fekete's lemma.) -/
theorem prop_gauge_radius_eq (h : IsPre D p) (t : M) :
    sInf (rad p t) = ⨅ n : ℕ, p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) := by
  have hbdd : BddBelow (Set.range fun n : ℕ => p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact Real.rpow_nonneg (h.nonneg _) _⟩
  refine le_antisymm (le_ciInf fun n => ?_) (le_csInf ⟨_, h.mem_rad t one_pos⟩ ?_)
  · -- (p(tⁿ) + δ)^(1/n) is such an a, for every δ > 0
    have h1 : ∀ δ : ℝ, 0 < δ → sInf (rad p t) ≤ (p (t ^ (n + 1)) + δ) ^ (((n + 1 : ℕ) : ℝ)⁻¹) := fun δ hδ =>
      csInf_le (rad_bdd p t) (prop_gauge_radius_root h n.succ_pos (h.mem_rad _ hδ))
    have h2 : Filter.Tendsto (fun δ : ℝ => (p (t ^ (n + 1)) + δ) ^ (((n + 1 : ℕ) : ℝ)⁻¹)) (nhdsWithin 0 (Set.Ioi 0))
        (nhds (p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹))) := by
      have h3 : Continuous fun δ : ℝ => (p (t ^ (n + 1)) + δ) ^ (((n + 1 : ℕ) : ℝ)⁻¹) :=
        (Real.continuous_rpow_const (by positivity)).comp (continuous_const.add continuous_id)
      have h4 := h3.tendsto 0
      rw [add_zero] at h4
      exact h4.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto h2 (Filter.eventually_of_mem self_mem_nhdsWithin fun δ hδ => h1 δ hδ)
  · -- p(tⁿ)^(1/n) ≤ C^(1/n)·a, and C^(1/n) tends to 1
    rintro a ⟨ha, C, hC⟩
    have hC1 := h.rad_const_pos hC
    have h1 : ∀ n : ℕ, ⨅ n : ℕ, p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) ≤ C ^ (((n + 1 : ℕ) : ℝ)⁻¹) * a := by
      intro n
      refine (ciInf_le hbdd n).trans ?_
      calc p (t ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) ≤ (C * a ^ (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹) :=
            Real.rpow_le_rpow (h.nonneg _) (hC _) (by positivity)
        _ = C ^ (((n + 1 : ℕ) : ℝ)⁻¹) * a := by
          rw [Real.mul_rpow (by linarith) (by positivity), Real.pow_rpow_inv_natCast ha.le n.succ_ne_zero]
    have h2 : Filter.Tendsto (fun n : ℕ => C ^ (((n + 1 : ℕ) : ℝ)⁻¹) * a) Filter.atTop (nhds (C ^ (0 : ℝ) * a)) := by
      refine Filter.Tendsto.mul_const a ?_
      refine ((Real.continuous_const_rpow (by linarith : C ≠ 0)).tendsto 0).comp ?_
      exact (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
    rw [Real.rpow_zero, one_mul] at h2
    exact ge_of_tendsto' h2 h1

/-- Proof of Proposition prop:gauge: "r = p, that is, p(tⁿ) = p(t)ⁿ." -/
theorem prop_gauge_radius_pow (h : IsPre D p) (hr : ∀ t, sInf (rad p t) = p t) (t : M) (n : ℕ) :
    p (t ^ n) = p t ^ n := by
  refine le_antisymm (h.pow_le t n) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [h.one]
  rw [← hr (t ^ n)]
  refine le_csInf ⟨_, h.mem_rad _ one_pos⟩ fun a ha => ?_
  have h5 : p t ≤ a ^ ((n : ℝ)⁻¹) := by
    rw [← hr t]
    exact csInf_le (rad_bdd p t) (prop_gauge_radius_root h hn ha)
  calc p t ^ n ≤ (a ^ ((n : ℝ)⁻¹)) ^ n := pow_le_pow_left₀ (h.nonneg t) h5 n
    _ = a := Real.rpow_inv_natCast_pow ha.1.le (by omega)

/-- Proof of Proposition prop:gauge: "Let f satisfy p(f) > 0 and let p_f(t) = inf p(tfⁿ)/p(f)ⁿ; the sequence is nonincreasing.
It is again such a gauge: p_f(1) = 1, submultiplicativity follows from p(stf^(a+b)) ≤ p(sfᵃ)p(tfᵇ), and the two other
properties pass to the limit." Here p(fⁿ) = p(f)ⁿ is a hypothesis. The statement says of q = p_f what is used: it is a gauge
below p, it keeps what p keeps, and it keeps (1, f, 1/p(f)), that is, p(f)·p_f(t) ≤ p_f(tf). -/
theorem prop_gauge_localize (h : IsPre D p) {f : M} (hf : 0 < p f) (hpow : ∀ n, p (f ^ n) = p f ^ n) :
    ∃ q : M → ℝ, IsPre D q ∧ (∀ t, q t ≤ p t) ∧ Keeps q 1 f (p f)⁻¹ ∧
      ∀ x y c, 0 ≤ c → Keeps p x y c → Keeps q x y c := by
  set P : ℕ → M → ℝ := fun n t => p (t * f ^ n) / p f ^ n with hP
  have anti : Antitone P := by
    refine antitone_nat_of_succ_le fun n t => ?_
    simp only [hP]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    calc p (t * f ^ (n + 1)) * p f ^ n ≤ (p (t * f ^ n) * p f) * p f ^ n := by
          gcongr
          rw [pow_succ, ← mul_assoc]
          exact h.mul_le _ _
      _ = p (t * f ^ n) * p f ^ (n + 1) := by ring
  have nonneg : ∀ n t, 0 ≤ P n t := fun n t => div_nonneg (h.nonneg _) (by positivity)
  have hle : ∀ n t, ⨅ j, P j t ≤ P n t := fun n t =>
    ciInf_le ⟨0, by rintro _ ⟨i, rfl⟩; exact nonneg i t⟩ n
  refine ⟨fun t => ⨅ n, P n t, isPre_iInf anti.directed_ge nonneg ?_ ?_ ?_, ?_, ?_, ?_⟩
  · intro n
    simp only [hP, one_mul, hpow]
    exact div_self (by positivity)
  · intro n s t
    refine ⟨n + n, ?_⟩
    simp only [hP]
    rw [div_mul_div_comm, ← pow_add]
    gcongr
    have : s * t * f ^ (n + n) = (s * f ^ n) * (t * f ^ n) := by
      rw [pow_add]; exact mul_mul_mul_comm _ _ _ _
    rw [this]
    exact h.mul_le _ _
  · intro n κ _ t b hb
    have h1 := h.le_sum _ _ (D.mul (f ^ n) hb)
    simp only [hP]
    rw [← Finset.sum_div]
    gcongr
  · intro t
    simpa [hP] using hle 0 t
  · intro t
    rw [mul_one, Real.mul_iInf_of_nonneg (by positivity)]
    refine le_ciInf fun n => (hle (n + 1) t).trans (le_of_eq ?_)
    simp only [hP]
    rw [pow_succ' f n, ← mul_assoc, pow_succ]
    field_simp
  · intro x y c hc hk
    refine keeps_iInf nonneg hc fun n t => ?_
    simp only [hP]
    rw [mul_div_assoc']
    gcongr
    have := hk (t * f ^ n)
    rwa [mul_right_comm, mul_right_comm t y]

/-- Proposition prop:gauge for a commutative monoid with a covering relation: below every gauge p₀ there is a gauge that is
multiplicative and keeps every triple which p₀ keeps. -/
theorem prop_gauge_monoid {p₀ : M → ℝ} (h₀ : IsPre D p₀) :
    ∃ F : M → ℝ, IsPre D F ∧ (∀ s t, F (s * t) = F s * F t) ∧ (∀ t, F t ≤ p₀ t) ∧
      ∀ x y c, 0 ≤ c → Keeps p₀ x y c → Keeps F x y c := by
  obtain ⟨p, hp, hle, hkeep, hmin⟩ := prop_gauge_minimal h₀
  -- "By minimality r = p, that is, p(tⁿ) = p(t)ⁿ."
  have hrad : ∀ t, sInf (rad p t) = p t :=
    hmin _ (prop_gauge_radius hp) (fun x y c hc hk => prop_gauge_radius_keeps hp hc (hkeep x y c hc hk))
      (prop_gauge_radius_le hp)
  refine ⟨p, hp, fun s f => le_antisymm (hp.mul_le s f) ?_, hle, hkeep⟩
  rcases (hp.nonneg f).eq_or_lt with hf | hf
  · -- "If p(f) = 0, then p(tf) = 0 as well."
    rw [← hf, mul_zero]
    exact hp.nonneg _
  · -- "By minimality p_f = p, hence p(tf) = p(t)p(f)."
    obtain ⟨q, hq, hqle, hqk, hqkeep⟩ := prop_gauge_localize hp hf (prop_gauge_radius_pow hp hrad f)
    have hqp := hmin q hq (fun x y c hc hk => hqkeep x y c hc (hkeep x y c hc hk)) hqle
    have h1 := hqk s
    rw [hqp, hqp, mul_one, inv_mul_eq_div, le_div_iff₀ hf] at h1
    exact h1

end Monoid

/-- **Paper: Proposition prop:gauge.** "Below every gauge there is a spectral point that keeps every triple which the
gauge keeps." A gauge is an Ov.PreSpec; it keeps (x, y, c) if p(tx) ≤ c p(ty) for all t. This is prop_gauge_monoid for the
classes of tensors. -/
theorem prop_gauge (p : PreSpec K I) :
    ∃ φ : Spec K I, (∀ t, φ.F t ≤ p.p t) ∧
      ∀ (x y : Ten K I) (c : ℝ), 0 ≤ c → (∀ t, p.p (t * x) ≤ c * p.p (t * y)) →
        ∀ t, φ.F (t * x) ≤ c * φ.F (t * y) := by
  obtain ⟨F, hF, hmul, hle, hk⟩ := prop_gauge_monoid (isPre_onCls p)
  refine ⟨⟨fun t => F (cls t), fun _ => hF.nonneg _, hF.one, fun s t => by rw [cls_mul, hmul],
    fun s b hb => hF.le_sum _ _ (tenCover_cov.2 hb)⟩, fun t => ?_, fun x y c hc h t => ?_⟩
  · exact (hle (cls t)).trans (onCls_cls p t).le
  · have h1 := hk (cls x) (cls y) c hc (keeps_onCls h) (cls t)
    rwa [← cls_mul, ← cls_mul] at h1

section Certificates

variable {M : Type*} [CommMonoid M] {D : Cover M} {B : Type} [Fintype B]

/-- Proof of Theorem thm:duality, first half: "Let p(t) be the infimum of the weights of all certificates for t. Certificates
can be multiplied, and can be raised to a common level and added along covers. As the trivial certificate of level 0 gives
p(1) ≤ 1, and copies of 1 give every t a certificate of level 0, the function p is a gauge if p(1) ≥ 1. … Multiplying a
certificate for tC by A_β gives one for tA_β of one level higher and η times the weight; so p keeps (A_β, C, η)." -/
theorem thm_duality_gauge {C : M} {A : B → M} {η : ℝ} (hη : 0 < η)
    (hone : ∀ t : M, ∃ r : ℕ, D.cov t (fun _ : Fin r => (1 : M)))
    (h : ∀ k W, Cert D C A η 1 k W → 1 ≤ W) :
    IsPre D (fun t => sInf {W | ∃ k, Cert D C A η t k W}) ∧
      ∀ β, Keeps (fun t => sInf {W | ∃ k, Cert D C A η t k W}) (A β) C η := by
  set S : M → Set ℝ := fun t => {W | ∃ k, Cert D C A η t k W} with hS
  have hne : ∀ t, (S t).Nonempty := by
    intro t
    obtain ⟨r, hr⟩ := hone t
    exact ⟨_, 0, Cert.cover hr fun _ => Cert.one 0⟩
  have h0 : ∀ t, ∀ w ∈ S t, 0 ≤ w := fun t w ⟨k, hk⟩ => hk.nonneg hη
  refine ⟨isPre_sInf hne h0 ⟨0, Cert.one 0⟩ (fun w ⟨k, hk⟩ => h k w hk)
    (fun s t a ⟨k, hk⟩ b ⟨l, hl⟩ => ⟨k + l, hk.mul hη hl⟩) ?_, fun β => ?_⟩
  · intro κ _ t b hb w hw
    choose k hk using hw
    exact ⟨_, ⟨∑ j, k j, Cert.cover hb fun j => (hk j).raise hη
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))⟩, le_rfl⟩
  · exact keeps_sInf hne h0 hη fun t w ⟨k, hk⟩ => ⟨k + 1, hk.mul_gen hη β⟩

/-- Proof of Theorem thm:duality: "So p(1) < 1, and 1 has a certificate of some level k and weight below 1. Then k ≥ 1, and
every term has v_j ≠ 0, as it would weigh 1 otherwise: this is a cover of C^k by terms in which at least one C was
exchanged." (The certificate of level k₀ is raised to the level k = k₀ + 1.) -/
theorem thm_duality_exchange {C : M} {A : B → M} {η : ℝ} (hη : 0 < η) {k₀ : ℕ} {W : ℝ}
    (h : Cert D C A η 1 k₀ W) (hW1 : W < 1) :
    ∃ (κ : Type) (_ : Fintype κ) (u : κ → ℕ) (v : κ → B → ℕ), (∀ j, u j + ∑ β, v j β = k₀ + 1) ∧
      (∀ j, u j < k₀ + 1) ∧ D.cov (C ^ (k₀ + 1)) (fun j => C ^ u j * mon A (v j)) ∧
      ∑ j, η ^ (∑ β, v j β) ≤ 1 := by
  obtain ⟨κ, _, u, v, hu, hc, hW⟩ := h.raise hη (Nat.le_succ k₀)
  rw [one_mul] at hc
  have hlt : ∑ j, η ^ (∑ β, v j β) < 1 := hW.trans_lt hW1
  refine ⟨κ, inferInstance, u, v, hu, fun j => ?_, hc, hlt.le⟩
  by_contra hge
  have h1 := hu j
  have h2 : ∑ β, v j β = 0 := by omega
  have h3 := Finset.single_le_sum (f := fun j => η ^ (∑ β, v j β))
    (fun j _ => by positivity) (Finset.mem_univ j)
  simp only [h2, pow_zero] at h3
  linarith

/-- Proof of Theorem thm:duality: "In C^N replace C^k by this cover as long as some term contains it. The total weight never
increases, so it stays at most 1, and each final term has fewer than k factors C." -/
theorem thm_duality_replace {C : M} {A : B → M} {η : ℝ} (hη : 0 < η) {k : ℕ} {κ : Type} [Fintype κ] {u : κ → ℕ}
    {v : κ → B → ℕ} (hu : ∀ j, u j + ∑ β, v j β = k) (huk : ∀ j, u j < k)
    (hc : D.cov (C ^ k) (fun j => C ^ u j * mon A (v j))) (hw : ∑ j, η ^ (∑ β, v j β) ≤ 1) (N : ℕ) :
    ∃ (κ' : Type) (_ : Fintype κ') (u' : κ' → ℕ) (v' : κ' → B → ℕ),
      (∀ j, u' j < k) ∧ (∀ j, u' j + ∑ β, v' j β = N) ∧
      D.cov (C ^ N) (fun j => C ^ u' j * mon A (v' j)) ∧ ∑ j, η ^ (∑ β, v' j β) ≤ 1 := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N k with hN | hN
    · exact ⟨Unit, inferInstance, fun _ => N, fun _ _ => 0, fun _ => by simpa using hN,
        by simp, by simpa [mon_zero] using D.refl (C ^ N), by simp⟩
    · have hN' : ∀ j, N - k + u j < N := fun j => by have := huk j; omega
      choose μ i u' v' hu' hs' hc' hw' using fun j => ih _ (hN' j)
      refine ⟨Σ j, μ j, inferInstance, fun x => u' x.1 x.2, fun x β => v x.1 β + v' x.1 x.2 β,
        fun x => hu' _ _, fun x => ?_, ?_, ?_⟩
      · have h1 := hs' x.1 x.2
        have h2 := hu x.1
        rw [Finset.sum_add_distrib]
        dsimp only
        omega
      · have h1 : D.cov (C ^ N) (fun j => C ^ (N - k + u j) * mon A (v j)) := by
          have h2 := D.mul (C ^ (N - k)) hc
          rw [← pow_add, Nat.add_sub_cancel' hN] at h2
          convert h2 using 2 with j
          rw [pow_add]
          ac_rfl
        refine D.bind (c := fun j (x : μ j) =>
          C ^ u' j x * mon A (fun β => v j β + v' j x β)) h1 fun j => ?_
        have h2 := D.mul (mon A (v j)) (hc' j)
        convert h2 using 2 with x
        rw [mon_add]
        ac_rfl
      · rw [Fintype.sum_sigma]
        refine le_trans (Finset.sum_le_sum fun j _ => ?_) hw
        calc ∑ x, η ^ (∑ β, (v j β + v' j x β)) =
            η ^ (∑ β, v j β) * ∑ x, η ^ (∑ β, v' j x β) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun x _ => by rw [← pow_add, Finset.sum_add_distrib]
          _ ≤ η ^ (∑ β, v j β) * 1 := by gcongr; exact hw' j
          _ = _ := mul_one _

omit [Fintype B] in
/-- Proof of Theorem thm:duality: "Replacing each remaining factor C by a fixed number c of copies of a nonzero A_β": if C is
covered by c copies of a, then Cⁿ is covered by cⁿ copies of aⁿ. -/
theorem thm_duality_copies {C a : M} {c : ℕ} (hc : D.cov C (fun _ : Fin c => a)) (n : ℕ) :
    ∃ (μ : Type) (_ : Fintype μ), Fintype.card μ = c ^ n ∧ D.cov (C ^ n) (fun _ : μ => a ^ n) := by
  induction n with
  | zero => exact ⟨Unit, inferInstance, by simp, by simpa using D.refl (1 : M)⟩
  | succ n ih =>
    obtain ⟨μ, _, hμ, hcov⟩ := ih
    refine ⟨Σ _ : μ, Fin c, inferInstance, ?_, ?_⟩
    · rw [Fintype.card_sigma]
      simp [hμ, pow_succ]
    · have := D.mul_mul hcov hc
      simpa only [pow_succ] using this

/-- Proof of Theorem thm:duality, second half: from a certificate for 1 of level k₀ and weight below 1, and a cover of C by c
copies of some A_β, a cover of C^N by products of N factors. "Hence there are at most η^(-N) terms. Replacing each remaining
factor C by a fixed number c of copies of a nonzero A_β gives at most c^k η^(-N)" terms; the Lean bound has c + 1 for c, and
k = k₀ + 1. -/
theorem thm_duality_cover {C : M} {A : B → M} {η : ℝ} (hη : 0 < η) (hη1 : η < 1) {β₀ : B} {c : ℕ}
    (hcA : D.cov C (fun _ : Fin c => A β₀)) {k₀ : ℕ} {W : ℝ} (h : Cert D C A η 1 k₀ W) (hW1 : W < 1) (N : ℕ) :
    ∃ (κ : Type) (_ : Fintype κ) (v : κ → B → ℕ),
      (Fintype.card κ : ℝ) ≤ ((c : ℝ) + 1) ^ (k₀ + 1) * (η⁻¹) ^ N ∧ (∀ j, ∑ β, v j β = N) ∧
      D.cov (C ^ N) (fun j => mon A (v j)) := by
  classical
  obtain ⟨κ, _, u, v, hu, huk, hc, hw⟩ := thm_duality_exchange hη h hW1
  obtain ⟨κ', _, u', v', hu', hs', hc', hw'⟩ := thm_duality_replace hη hu huk hc hw N
  choose μ i hμ hcov using fun j : κ' => thm_duality_copies hcA (u' j)
  set E : ℝ := ((c : ℝ) + 1) ^ (k₀ + 1) with hE
  refine ⟨Σ j, μ j, inferInstance, fun x β => v' x.1 β + if β = β₀ then u' x.1 else 0,
    ?_, fun x => ?_, ?_⟩
  · rw [Fintype.card_sigma]
    push_cast
    have h1 : ∀ j, (Fintype.card (μ j) : ℝ) ≤ E := fun j => by
      rw [hμ j]
      push_cast
      calc (c : ℝ) ^ u' j ≤ ((c : ℝ) + 1) ^ u' j := by gcongr; linarith
        _ ≤ E := pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) c]) (hu' j).le
    have h2 : (Fintype.card κ' : ℝ) * η ^ N ≤ 1 := by
      refine le_trans ?_ hw'
      rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
      refine Finset.sum_le_sum fun j _ => pow_le_pow_of_le_one hη.le hη1.le ?_
      have := hs' j
      omega
    calc ∑ j, (Fintype.card (μ j) : ℝ) ≤ ∑ _j : κ', E := Finset.sum_le_sum fun j _ => h1 j
      _ = Fintype.card κ' * E := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card κ' * η ^ N) * (E * (η⁻¹) ^ N) := by
        rw [inv_pow]
        field_simp
      _ ≤ 1 * (E * (η⁻¹) ^ N) := by gcongr
      _ = _ := one_mul _
  · have := hs' x.1
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    omega
  · refine D.bind (b := fun j => C ^ u' j * mon A (v' j))
      (c := fun j (_ : μ j) => mon A (fun β => v' j β + if β = β₀ then u' j else 0)) hc' fun j => ?_
    have h1 := D.mul (mon A (v' j)) (hcov j)
    convert h1 using 2 with x
    rw [mon_add, mon_single]
    exact mul_comm _ _

end Certificates

/-- **Paper: Theorem thm:duality.** "Let C ≠ 0 and A_1, …, A_r be tensors on I, not all A_β zero, and suppose that
every spectral point satisfies φ(C) ≤ max φ(A_β). Then for every ε > 0 and all large N, the power C^N is covered by at
most 2^(εN) products of N factors from A_1, …, A_r." The family is indexed by any finite type B. -/
theorem thm_duality [Nonempty I] {B : Type} [Fintype B] [DecidableEq B] {C : Ten K I} {A : B → Ten K I}
    (hC : ∃ x, C.val x ≠ 0) (hA : ∃ β x, (A β).val x ≠ 0) (h : ∀ φ : Spec K I, ∃ β, φ.F C ≤ φ.F (A β)) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ (m : ℕ) (v : Fin m → B → ℕ), (m : ℝ) ≤ 2 ^ (ε * N) ∧
      (∀ i, ∑ β, v i β = N) ∧
      SumRestr (Ten.kpow C N) fun i => Ten.prod fun β => Ten.kpow (A β) (v i β) := by
  -- η = 2^(-ε/2)
  have hη : (0 : ℝ) < 2 ^ (-(ε / 2)) := by positivity
  have hη1 : (2 : ℝ) ^ (-(ε / 2)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hinv : ((2 : ℝ) ^ (-(ε / 2)))⁻¹ = 2 ^ (ε / 2) := by rw [← Real.rpow_neg (by norm_num), neg_neg]
  have hsq : ∀ N : ℕ, ((2 : ℝ) ^ (ε / 2)) ^ N * ((2 : ℝ) ^ (ε / 2)) ^ N = 2 ^ (ε * N) := by
    intro N
    rw [← mul_pow, ← Real.rpow_add (by norm_num), add_halves, Real.rpow_mul (by norm_num), Real.rpow_natCast]
  -- copies of 1, and so of any nonzero tensor, cover every tensor
  have hcov : ∀ (t : Ten K I) {s : Ten K I}, Restr 1 s →
      ∃ r : ℕ, (tenCover K I).cov (cls t) (fun _ : Fin r => cls s) := fun t s hs => by
    obtain ⟨r, hr⟩ := tensor_covered_by_ones t
    exact ⟨r, tenCover_cov.2 (hr.mono fun _ => hs)⟩
  have hone : ∀ t : Cls K I, ∃ r : ℕ, (tenCover K I).cov t (fun _ : Fin r => (1 : Cls K I)) := by
    intro t
    obtain ⟨r, hr⟩ := hcov (rep t) (Restr.refl 1)
    rw [cls_rep] at hr
    exact ⟨r, hr⟩
  obtain ⟨β₀, hβ₀⟩ := hA
  by_cases hcert : ∃ k W, Cert (tenCover K I) (cls C) (fun β => cls (A β)) (2 ^ (-(ε / 2))) 1 k W ∧ W < 1
  · -- 1 has a certificate of weight below 1
    obtain ⟨k, W, hc, hW⟩ := hcert
    obtain ⟨c, hcA⟩ := hcov C (tensor_one_restr hβ₀)
    have hbase : (1 : ℝ) < 2 ^ (ε / 2) := Real.one_lt_rpow one_lt_two (by linarith)
    -- c^k η^(-N) ≤ 2^(εN) for large N
    obtain ⟨N₀, hN₀⟩ := pow_unbounded_of_one_lt (((c : ℝ) + 1) ^ (k + 1)) hbase
    refine ⟨N₀, fun N hN => ?_⟩
    obtain ⟨κ, _, v, hcard, hv, hc⟩ := thm_duality_cover hη hη1 (β₀ := β₀) hcA hc hW N
    let e := Fintype.equivFin κ
    refine ⟨Fintype.card κ, fun i => v (e.symm i), ?_, fun i => hv _, ?_⟩
    · rw [hinv] at hcard
      refine hcard.trans (le_trans ?_ (hsq N).le)
      gcongr
      exact hN₀.le.trans (pow_le_pow_right₀ hbase.le hN)
    simp only [cls_mon, ← cls_kpow] at hc
    exact (tenCover_cov.1 hc).reindex e.symm
  · -- otherwise the weights of certificates are a gauge, and Proposition prop:gauge contradicts the hypothesis
    exfalso
    push Not at hcert
    obtain ⟨hp, hA⟩ := thm_duality_gauge (D := tenCover K I) (C := cls C) (A := fun β => cls (A β)) hη hone hcert
    obtain ⟨φ, -, hk⟩ := prop_gauge (ofCls hp)
    obtain ⟨β, hβ⟩ := h φ
    have h2 := hk (A β) C _ hη.le (fun t => by
      have h5 := hA β (cls t)
      rw [← cls_mul, ← cls_mul] at h5
      exact h5) 1
    rw [(def_spectral_congr φ).2 (Equi.one_mul _), (def_spectral_congr φ).2 (Equi.one_mul _)] at h2
    have h3 : 1 ≤ φ.F C := (def_spectral_values φ C).1 hC
    nlinarith

end Paper
