/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Ov.Core.Unit
import Nc.Rate.Defs

/-!
# The paper, section "Tensors, prices and duality": tensors

The subsection "Tensors". One theorem for every numbered statement, in the order of the paper and named by its label, and
one for every step of the running text that is used later. Tensors are arrays over a field K with one finite index set for
each party (Ov.Ten); tensors that are restrictions of one another (Ov.Ten.Equi) are not identified, instead a spectral point
has the same value on them (def_spectral_congr). The other subsections are in Paper/Gauges.lean, Paper/Extension.lean and
Paper/Prices.lean.
-/

namespace Paper

open Ov Ov.Ten Nc.Price Finset

variable {K : Type} [Field K] {I : Type} [Fintype I] [DecidableEq I]

/-! ## Tensors -/

section Tensors

variable {J L : Type} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]

/-- "Tensors that are restrictions of each other are identified, so that the product is commutative, with unit the tensor
1"; it is also associative. -/
theorem tensor_mul_laws (s t u : Ten K I) :
    Equi (s * t) (t * s) ∧ Equi (s * t * u) (s * (t * u)) ∧ Equi (1 * t) t ∧ Equi (t * 1) t :=
  ⟨Equi.mul_comm s t, Equi.mul_assoc s t u, Equi.one_mul t, Equi.mul_one t⟩

/-- "Every nonzero t has 1 as a restriction". -/
theorem tensor_one_restr [Nonempty I] {t : Ten K I} (ht : ∃ x, t.val x ≠ 0) : Restr 1 t :=
  Restr.one_le ht.choose_spec

/-- "Every t is covered by finitely many copies of 1." -/
theorem tensor_covered_by_ones [Nonempty I] (t : Ten K I) : ∃ r : ℕ, SumRestr t fun _ : Fin r => (1 : Ten K I) :=
  ⟨_, (rankLE_card t).sumRestr⟩

/-- "Push-forward commutes with products". -/
theorem tensor_push_mul (π : J → I) (s t : Ten K J) : Equi (Ten.push π (s * t)) (Ten.push π s * Ten.push π t) :=
  Equi.push_mul π s t

/-- "Push-forward commutes with … compositions". -/
theorem tensor_push_comp (π : J → I) (ρ : L → J) (t : Ten K L) :
    Equi (Ten.push π (Ten.push ρ t)) (Ten.push (π ∘ ρ) t) :=
  Equi.push_push π ρ t

/-- The push-forward along the identity does nothing. -/
theorem tensor_push_id (t : Ten K I) : Equi (Ten.push id t) t := Equi.push_id t

/-- "Push-forward … sends 1 to 1". -/
theorem tensor_push_one (π : J → I) : Equi (Ten.push π (1 : Ten K J)) 1 := Equi.push_one π

/-- "Push-forward … sends … covers to covers"; in particular restrictions to restrictions. -/
theorem tensor_push_cover (π : J → I) :
    (∀ {κ : Type} [Fintype κ] {s : Ten K J} {b : κ → Ten K J}, SumRestr s b →
      SumRestr (Ten.push π s) fun k => Ten.push π (b k)) ∧
    ∀ {s t : Ten K J}, Restr s t → Restr (Ten.push π s) (Ten.push π t) :=
  ⟨fun h => h.push π, fun h => h.push π⟩

end Tensors

/-- **Paper: Definition def:spectral.** "A spectral point on I is a function φ ≥ 0 on tensors with φ(1) = 1,
φ(st) = φ(s)φ(t), and φ(s) ≤ ∑ φ(t_j) whenever s is covered by t_1, …, t_r." -/
theorem def_spectral (φ : Ten K I → ℝ) :
    (∃ F : Spec K I, F.F = φ) ↔ (∀ t, 0 ≤ φ t) ∧ φ 1 = 1 ∧ (∀ s t, φ (s * t) = φ s * φ t) ∧
      ∀ (r : ℕ) (s : Ten K I) (t : Fin r → Ten K I), SumRestr s t → φ s ≤ ∑ j, φ (t j) := by
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨F.nonneg, F.one, F.mul, fun r s t h => F.le_sum s t h⟩
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨⟨φ, h0, h1, h2, fun {κ} _ s b h => ?_⟩, rfl⟩
    classical
    refine (h3 _ s (b ∘ (Fintype.equivFin κ).symm) (h.reindex (Fintype.equivFin κ).symm)).trans (le_of_eq ?_)
    exact Fintype.sum_equiv (Fintype.equivFin κ).symm _ _ fun _ => rfl

/-- The text after the definition: "So φ(t) ≥ 1 if t ≠ 0, and φ(0) = 0 (the empty sum)." -/
theorem def_spectral_values [Nonempty I] (φ : Spec K I) (t : Ten K I) :
    ((∃ x, t.val x ≠ 0) → 1 ≤ φ.F t) ∧ ((∀ x, t.val x = 0) → φ.F t = 0) :=
  ⟨fun ⟨_, hx⟩ => φ.one_le hx, φ.zero⟩

/-- Tensors that are restrictions of each other are identified: a spectral point is monotone under restriction, so it has
the same value on them. -/
theorem def_spectral_congr (φ : Spec K I) {s t : Ten K I} :
    (Restr s t → φ.F s ≤ φ.F t) ∧ (Equi s t → φ.F s = φ.F t) :=
  ⟨φ.mono, φ.congr⟩

open Classical in
/-- The first example after Definition def:spectral: "An example is φ(t) = 1 for all t ≠ 0". -/
noncomputable def trivialPoint (K : Type) [Field K] (I : Type) [Fintype I] [DecidableEq I] : Spec K I where
  F t := if ∃ x, t.val x ≠ 0 then 1 else 0
  nonneg t := by split_ifs <;> norm_num
  one := if_pos ⟨fun _ => (), one_ne_zero⟩
  mul s t := by
    by_cases hs : ∃ x, s.val x ≠ 0
    · by_cases ht : ∃ x, t.val x ≠ 0
      · rw [if_pos hs, if_pos ht, if_pos, mul_one]
        obtain ⟨x, hx⟩ := hs
        obtain ⟨y, hy⟩ := ht
        exact ⟨fun p => (x p, y p), mul_ne_zero hx hy⟩
      · rw [if_neg ht, mul_zero, if_neg]
        rintro ⟨x, hx⟩
        exact ht ⟨fun p => (x p).2, right_ne_zero_of_mul hx⟩
    · rw [if_neg hs, zero_mul, if_neg]
      rintro ⟨x, hx⟩
      exact hs ⟨fun p => (x p).1, left_ne_zero_of_mul hx⟩
  le_sum {κ} _ s b h := by
    by_cases hs : ∃ x, s.val x ≠ 0
    · rw [if_pos hs]
      obtain ⟨x, hx⟩ := hs
      obtain ⟨L, hL⟩ := h
      rw [hL] at hx
      obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
      have h1 : ∃ x, (b k).val x ≠ 0 := ⟨y, right_ne_zero_of_mul hy⟩
      calc (1 : ℝ) = if ∃ x, (b k).val x ≠ 0 then 1 else 0 := (if_pos h1).symm
        _ ≤ _ := Finset.single_le_sum
          (f := fun k => if ∃ x, (b k).val x ≠ 0 then (1 : ℝ) else 0)
          (fun k _ => by split_ifs <;> norm_num) (Finset.mem_univ k)
    · rw [if_neg hs]
      exact Finset.sum_nonneg fun k _ => by split_ifs <;> norm_num

/-- The last example after Definition def:spectral: "φ^s is again a spectral point for 0 < s ≤ 1." -/
noncomputable def powerPoint (φ : Spec K I) (s : ℝ) (h0 : 0 < s) (h1 : s ≤ 1) : Spec K I where
  F t := φ.F t ^ s
  nonneg t := Real.rpow_nonneg (φ.nonneg t) s
  one := by rw [φ.one, Real.one_rpow]
  mul a b := by rw [φ.mul, Real.mul_rpow (φ.nonneg a) (φ.nonneg b)]
  le_sum {κ} _ a b h := by
    classical
    refine (Real.rpow_le_rpow (φ.nonneg a) (φ.le_sum a b h) h0.le).trans ?_
    have key : ∀ S : Finset κ, (∑ k ∈ S, φ.F (b k)) ^ s ≤ ∑ k ∈ S, φ.F (b k) ^ s := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp [Real.zero_rpow h0.ne']
      | insert k S hk ih =>
        rw [Finset.sum_insert hk, Finset.sum_insert hk]
        exact (Real.rpow_add_le_add_rpow (φ.nonneg _) (Finset.sum_nonneg fun _ _ => φ.nonneg _) h0.le h1).trans
          (by gcongr)
    exact key Finset.univ

/-- Proof of Lemma lem:exponents: "The function q ↦ φ(⟨q⟩_P) is at least 1, multiplicative and monotone, hence a power of q."
The unit tensor has a leg at π a for every a; the exponent is Nc.Price.hexp. -/
theorem lem_exponents_power [Nonempty I] (φ : Spec K I) {A : Type} [Fintype A] [DecidableEq A] (π : A → I) :
    0 ≤ hexp φ π ∧ ∀ q : ℕ, 1 ≤ q → φ.F (Ten.push π (Ten.unit K A q)) = (q : ℝ) ^ hexp φ π :=
  ⟨Real.logb_nonneg (by norm_num) (φ.one_le_unit π (by norm_num)), fun _ hq =>
    eq_rpow_of_mul_mono (fun n => φ.F (Ten.push π (Ten.unit K A n))) (fun _ h => φ.one_le_unit π h)
      (fun m n _ _ => by
        rw [(def_spectral_congr φ).2 ((Equi.unit_mul m n).push π), (def_spectral_congr φ).2 (tensor_push_mul _ _ _), φ.mul])
      (fun _ _ _ h => (def_spectral_congr φ).1 ((Restr.unit_mono h).push π)) _ hq⟩

/-- The case of a wire: φ(⟨q⟩_uv) = q ^ d_φ(u,v). -/
theorem lem_exponents_wire (φ : Spec K I) (u v : I) {q : ℕ} (hq : 1 ≤ q) :
    φ.F (Ten.wire K q u v) = (q : ℝ) ^ φ.e u v :=
  have : Nonempty I := ⟨u⟩
  (lem_exponents_power φ ![u, v]).2 q hq

theorem lem_exponents_wire_two (φ : Spec K I) (u v : I) : φ.F (Ten.wire K 2 u v) = 2 ^ φ.e u v := by
  have := lem_exponents_wire φ u v (q := 2) (by norm_num)
  exact_mod_cast this

/-- Proof of Lemma lem:exponents: "A wire of dimension q is covered by q copies of 1, so d_φ ≤ 1." (The cover and its
consequence φ(⟨q⟩_uv) ≤ q are Ov.Spec.unit_le.) Also d_φ ≥ 0, as for every exponent. -/
theorem lem_exponents_unit_interval (φ : Spec K I) (u v : I) : 0 ≤ φ.e u v ∧ φ.e u v ≤ 1 := by
  have : Nonempty I := ⟨u⟩
  refine ⟨(lem_exponents_power φ ![u, v]).1, ?_⟩
  have h : φ.F (Ten.wire K 2 u v) ≤ (2 : ℕ) := φ.unit_le ![u, v] 2
  rw [lem_exponents_wire_two] at h
  have h2 : (2 : ℝ) ^ φ.e u v ≤ 2 ^ (1 : ℝ) := by simpa using h
  exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h2

/-- "We put ⟨q⟩_uu = 1": a wire from u to u is a restriction of 1, so d_φ(u,u) = 0. -/
theorem lem_exponents_self (φ : Spec K I) (u : I) : φ.e u u = 0 := by
  have : Nonempty I := ⟨u⟩
  have h : φ.F (Ten.wire K 2 u u) = 1 := by
    refine le_antisymm ?_ (φ.one_le_unit ![u, u] (by norm_num))
    rw [← φ.one]
    exact (def_spectral_congr φ).1 (Restr.wire_self 2 u)
  rw [Spec.e, h, Real.logb_one]

/-- A wire has no direction. -/
theorem lem_exponents_symm (φ : Spec K I) (u v : I) : φ.e u v = φ.e v u := by
  rw [Spec.e, Spec.e, (def_spectral_congr φ).2 (Equi.wire_comm 2 u v)]

/-- Proof of Lemma lem:exponents: "Contracting the two indices at v shows that ⟨q⟩_uw is a restriction of ⟨q⟩_uv ⟨q⟩_vw". -/
theorem lem_exponents_contract (q : ℕ) (u v w : I) :
    Restr (Ten.wire K q u w) (Ten.wire K q u v * Ten.wire K q v w) :=
  Restr.wire_trans q u w v

/-- Proof of Lemma lem:exponents: "… this is the triangle inequality." -/
theorem lem_exponents_triangle (φ : Spec K I) (u v w : I) : φ.e u w ≤ φ.e u v + φ.e v w := by
  have h := φ.le_mul (lem_exponents_contract (K := K) 2 u v w)
  rw [lem_exponents_wire_two, lem_exponents_wire_two, lem_exponents_wire_two, ← Real.rpow_add (by norm_num)] at h
  exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h

/-- Proof of Lemma lem:exponents: "Identifying the indices at every vertex in the same way shows that ⟨q⟩_P is a restriction of
the product of the wires on the edges of the tree." The unit tensor has a leg at π p for every vertex p ∈ A; the edge e joins
a e and b e; of the graph only connectedness is used, in the form that a function to Fin q that is constant along edges is
constant. -/
theorem lem_exponents_tree {A E : Type} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype E] [DecidableEq E] (q : ℕ)
    (π : A → I) (a b : E → A) (hconn : ∀ f : A → Fin q, (∀ e, f (a e) = f (b e)) → ∀ p p', f p = f p') :
    Restr (Ten.push π (Ten.unit K A q)) (Ten.prod fun e => Ten.wire K q (π (a e)) (π (b e))) := by
  classical
  have key := Restr.of_edges π (ξ := fun o : Option A => o.elim (π (Classical.arbitrary A)) π) (Ten.unit K A q)
    (fun _ : E => Fin q) (fun e => some (a e)) (fun e => some (b e))
    (fun o x l => o.elim 1 fun p => ∏ e, if a e = p ∨ b e = p then (if l e = x p then (1 : K) else 0) else 1)
    (by
      rintro (_ | p) x x' l l' hx hl
      · rfl
      · refine Finset.prod_congr rfl fun e _ => ?_
        by_cases he : a e = p ∨ b e = p
        · have h2 : l e = l' e := hl e (he.imp (congrArg some) (congrArg some))
          have h3 : x p = x' p := hx p rfl
          rw [if_pos he, if_pos he, h2, h3]
        · rw [if_neg he, if_neg he])
    (by
      intro x
      refine Eq.trans ?_ (Fintype.sum_eq_single (fun e => (x (a e) : Fin q)) ?_).symm
      · rw [Fintype.prod_option]
        show _ = 1 * _
        rw [one_mul]
        by_cases h : ∀ i j, x i = x j
        · rw [Ten.unit_val_of h]
          refine (Finset.prod_eq_one fun p _ => Finset.prod_eq_one fun e _ => ?_).symm
          exact (ite_eq_right_iff.2 fun _ => if_pos (h (a e) p))
        · rw [Ten.unit_val_not h]
          obtain ⟨e, he⟩ : ∃ e, x (a e) ≠ x (b e) := by
            by_contra hne
            push Not at hne
            exact h (hconn x hne)
          refine (Finset.prod_eq_zero (Finset.mem_univ (b e)) (Finset.prod_eq_zero (Finset.mem_univ e) ?_)).symm
          exact (if_pos (Or.inr rfl)).trans (if_neg he)
      · intro l hl
        obtain ⟨e, he⟩ := Function.ne_iff.1 hl
        refine Finset.prod_eq_zero (Finset.mem_univ (some (a e))) (Finset.prod_eq_zero (Finset.mem_univ e) ?_)
        exact (if_pos (Or.inl rfl)).trans (if_neg he))
  simpa only [Fintype.card_fin, Option.elim_some] using key

/-- The consequence of lem_exponents_tree in exponents: g_φ(P) ≤ ∑ d_φ(e) over the edges. -/
theorem lem_exponents_tree_le [Nonempty I] (φ : Spec K I) {A E : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype E] [DecidableEq E] (π : A → I) (a b : E → A)
    (hconn : ∀ f : A → Fin 2, (∀ e, f (a e) = f (b e)) → ∀ p p', f p = f p') :
    hexp φ π ≤ ∑ e, φ.e (π (a e)) (π (b e)) := by
  rw [hexp, Real.logb_le_iff_le_rpow (by norm_num) (zero_lt_one.trans_le (φ.one_le_unit π (by norm_num)))]
  refine (φ.le_prod (lem_exponents_tree 2 π a b hconn)).trans (le_of_eq ?_)
  rw [Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact Finset.prod_congr rfl fun e _ => lem_exponents_wire_two φ _ _

/-- **Paper: Lemma lem:exponents.** "Let φ be a spectral point on I. For every nonempty P ⊆ I there is g_φ(P) ≥ 0 with
φ(⟨q⟩_P) = q ^ g_φ(P) for all q ≥ 1. The function d_φ(u,v) = g_φ({u,v}), d_φ(u,u) = 0, is a pseudometric with values in
[0,1], and g_φ(P) ≤ ∑ d_φ(e) over the edges of any tree on P." The function d_φ is Ov.Spec.e. -/
theorem lem_exponents [Nonempty I] (φ : Spec K I) :
    ∃ g : Finset I → ℝ,
      (∀ P : Finset I, P.Nonempty → 0 ≤ g P ∧
        ∀ q : ℕ, 1 ≤ q → φ.F (Ten.push (Subtype.val : P → I) (Ten.unit K P q)) = (q : ℝ) ^ g P) ∧
      (∀ u v, u ≠ v → φ.e u v = g {u, v}) ∧ (∀ u, φ.e u u = 0) ∧
      (∀ u v, φ.e u v = φ.e v u) ∧ (∀ u v w, φ.e u w ≤ φ.e u v + φ.e v w) ∧ (∀ u v, φ.e u v ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ (P : Finset I) (G : SimpleGraph P) [DecidableRel G.Adj], G.IsTree →
        g P ≤ ∑ e ∈ G.edgeFinset, Sym2.lift ⟨fun u v => φ.e u v, fun _ _ => lem_exponents_symm φ _ _⟩ (e.map Subtype.val) := by
  classical
  refine ⟨fun P => hexp φ (Subtype.val : P → I), fun P _ =>
    ⟨(lem_exponents_power φ _).1, (lem_exponents_power φ _).2⟩,
    fun u v _ => ?_, lem_exponents_self φ, lem_exponents_symm φ, lem_exponents_triangle φ,
    lem_exponents_unit_interval φ, ?_⟩
  · show hexp φ ![u, v] = hexp φ (Subtype.val : ({u, v} : Finset I) → I)
    have h : Set.range ![u, v] = Set.range (Subtype.val : ({u, v} : Finset I) → I) := by
      simp only [Matrix.range_cons, Matrix.range_empty, Subtype.range_coe_subtype]
      ext x
      simp [or_comm]
    rw [hexp, hexp, (def_spectral_congr φ).2 (Ten.Equi.push_unit_congr _ _ h 2)]
  · intro P G _ hT
    have : Nonempty P := hT.connected.nonempty
    refine (lem_exponents_tree_le φ (Subtype.val : P → I) (E := G.edgeFinset)
      (fun e => e.1.out.1) (fun e => e.1.out.2) fun f hf p q => ?_).trans (le_of_eq ?_)
    · obtain ⟨w⟩ := hT.connected.preconnected p q
      induction w with
      | nil => rfl
      | @cons u v _ hadj _ ih =>
        refine Eq.trans ?_ ih
        have hmem : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.2 hadj
        have h1 : f (s(u, v) : Sym2 P).out.1 = f (s(u, v) : Sym2 P).out.2 := hf ⟨_, hmem⟩
        have h2 : (s((s(u, v) : Sym2 P).out.1, (s(u, v) : Sym2 P).out.2) : Sym2 P) = s(u, v) := Quot.out_eq _
        rcases Sym2.eq_iff.1 h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at h1
        exacts [h1, h1.symm]
    · rw [← Finset.sum_coe_sort G.edgeFinset]
      refine Finset.sum_congr rfl fun e _ => ?_
      conv_rhs => rw [← Quot.out_eq e.1]
      rfl

end Paper
