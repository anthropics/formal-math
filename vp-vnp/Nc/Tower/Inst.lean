/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tower.Coord
import Nc.Tow.Defs

/-!
# The tower
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

open Finset

variable (h n : ℕ) [NeZero h]

/-- The chain of subgroups. -/
noncomputable def Gam : ℕ → Subgroup (G h n) := (exists_chain h n).choose

theorem Gam_zero : Gam h n 0 = ⊥ := (exists_chain h n).choose_spec.1

theorem Gam_le (j : ℕ) : Gam h n j ≤ Gam h n (j + 1) := (exists_chain h n).choose_spec.2.1 j

theorem Gam_ker (j : ℕ) : Gam h n j ≤ Ker h n := (exists_chain h n).choose_spec.2.2.1 j

theorem card_Gam {j : ℕ} (hj : j ≤ JJ h n) : Nat.card (Gam h n j) = (2 ^ ee h) ^ j :=
  (exists_chain h n).choose_spec.2.2.2 j hj

/-- The chambers. -/
abbrev XX (j : ℕ) : Type := G h n ⧸ Gam h n j

noncomputable instance instFintypeXX (j : ℕ) : Fintype (XX h n j) := Fintype.ofFinite _

noncomputable instance instDecXX (j : ℕ) : DecidableEq (XX h n j) := Classical.decEq _

variable {h n}

/-- The value of a chamber in SL_h(F₂). -/
noncomputable def evX {j : ℕ} : XX h n j → SL2 h :=
  Quotient.lift (fun g => evG g) (by
    intro a b hab
    have h1 : a⁻¹ * b ∈ Gam h n j := QuotientGroup.leftRel_apply.1 hab
    have h2 := mem_Ker.1 (Gam_ker h n j h1)
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2)

theorem evX_mk {j : ℕ} (g : G h n) : evX (QuotientGroup.mk g : XX h n j) = evG g := rfl

theorem evX_smul {j : ℕ} (g : G h n) (c : XX h n j) : evX (g • c) = evG g * evX c := by
  induction c using QuotientGroup.induction_on with
  | H a =>
    change evX (QuotientGroup.mk (g * a) : XX h n j) = _
    rw [evX_mk, map_mul]
    rfl

/-- The covering. -/
noncomputable def pr {j : ℕ} : XX h n j → XX h n (j + 1) := Subgroup.quotientMapOfLE (Gam_le h n j)

/-- **Paper: Proposition prop:tower.** The projections are equivariant. -/
theorem _root_.Paper.prop_tower_equivariant {j : ℕ} (g : G h n) (c : XX h n j) : pr (g • c) = g • pr c := by
  induction c using QuotientGroup.induction_on with
  | H a => rfl

theorem evX_pr {j : ℕ} (c : XX h n j) : evX (pr c) = evX c := by
  induction c using QuotientGroup.induction_on with
  | H a => rfl

/-- The coordinate at the vertex of type i. -/
noncomputable def cor {j : ℕ} (i : Fin h) (c : XX h n j) : U h := coQ i (evX c)

theorem cor_th {j : ℕ} (i : Fin h) (u : U h) (c : XX h n j) : cor i ((th i u : G h n) • c) = u * cor i c := by
  rw [cor, cor, evX_smul, evG_th, coQ_mul]

theorem cor_pr {j : ℕ} (i : Fin h) (c : XX h n j) : cor i (pr c) = cor i c := by rw [cor, cor, evX_pr]

variable (h n) in
/-- The vertices of type i: the chambers with coordinate 1. -/
abbrev VV (j : ℕ) (i : Fin h) : Type := {c : XX h n j // cor i c = 1}

noncomputable instance instFintypeVV (j : ℕ) (i : Fin h) : Fintype (VV h n j i) := Fintype.ofFinite _

noncomputable instance instDecVV (j : ℕ) (i : Fin h) : DecidableEq (VV h n j i) := Classical.decEq _

/-- The vertex of a chamber. -/
noncomputable def vert {j : ℕ} (i : Fin h) (c : XX h n j) : VV h n j i :=
  ⟨(th i (cor i c)⁻¹ : G h n) • c, by rw [cor_th, inv_mul_cancel]⟩

theorem vert_val {j : ℕ} (i : Fin h) (c : XX h n j) : (vert i c).1 = (th i (cor i c)⁻¹ : G h n) • c := rfl

theorem th_vert {j : ℕ} (i : Fin h) (c : XX h n j) : (th i (cor i c) : G h n) • (vert i c).1 = c := by
  rw [vert_val, ← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]

theorem vert_th {j : ℕ} (i : Fin h) (u : U h) (c : XX h n j) : vert i ((th i u : G h n) • c) = vert i c := by
  refine Subtype.ext ?_
  rw [vert_val, vert_val, cor_th, ← mul_smul, ← map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

theorem vert_of {j : ℕ} (i : Fin h) (v : VV h n j i) : vert i v.1 = v := by
  refine Subtype.ext ?_
  rw [vert_val, v.2, inv_one, map_one, one_smul]

theorem vert_cor_bijective (j : ℕ) (i : Fin h) : Function.Bijective fun c : XX h n j => (vert i c, cor i c) := by
  constructor
  · intro c c' e
    simp only [Prod.mk.injEq] at e
    rw [← th_vert i c, ← th_vert i c', e.1, e.2]
  · rintro ⟨v, u⟩
    refine ⟨(th i u : G h n) • v.1, ?_⟩
    simp only
    rw [vert_th, vert_of, cor_th, v.2, mul_one]

variable (h n) in
/-- The edges: pairs of type k, represented by their first chambers. -/
abbrev EE (h2 : 2 ≤ h) (j : ℕ) : Type := {p : Fin h × XX h n j // FQ h2 p.1 (evX p.2)}

noncomputable instance instFintypeEE (h2 : 2 ≤ h) (j : ℕ) : Fintype (EE h n h2 j) := Fintype.ofFinite _

noncomputable instance instDecEE (h2 : 2 ≤ h) (j : ℕ) : DecidableEq (EE h n h2 j) := Classical.decEq _

theorem FQ_gen {j : ℕ} (h2 : 2 ≤ h) (k : Fin h) (c : XX h n j) :
    FQ h2 k (evX ((gen h2 k : G h n) • c)) ↔ ¬ FQ h2 k (evX c) := by rw [evX_smul, FQ_iff]

theorem gen_gen {j : ℕ} (h2 : 2 ≤ h) (k : Fin h) (c : XX h n j) :
    (gen h2 k : G h n) • (gen h2 k : G h n) • c = c := by rw [← mul_smul, gen_mul_self, one_smul]

/-- **Paper: Proposition prop:tower(a).** The copy of U_h "acts freely on every X^(j)". -/
theorem _root_.Paper.prop_tower_free {j : ℕ} (i : Fin h) (u : U h) (c : XX h n j) (e : (th i u : G h n) • c = c) :
    u = 1 := by
  have h1 := congrArg (cor i) e
  rwa [cor_th, mul_eq_right] at h1

/-- **Paper: Proposition prop:tower(b).** "c and X_i c always lie in different i-cosets." -/
theorem _root_.Paper.prop_tower_cosets {j : ℕ} (h2 : 2 ≤ h) (i : Fin h) (c : XX h n j) (u : U h) :
    (th i u : G h n) • c ≠ (gen h2 i : G h n) • c := by
  intro e
  have h1 := congrArg evX e
  rw [evX_smul, evX_smul, mul_left_inj] at h1
  -- the entry (i−1, i) at s = 0
  have hi : (i - 1 : Fin h) ≠ i := sub_one_ne h2 i
  have h2' := congrArg (fun M : SL2 h => M.1 (i - 1) i) h1
  simp only [th, MonoidHom.comp_apply, evG_th0] at h2'
  rw [evG_apply, gen_val] at h2'
  simp [Matrix.transvection, Matrix.one_apply_ne hi, tt] at h2'
  rw [(u.2 _ _).1 (Fin.pos_iff_ne_zero.2 fun h0 => hi (by rw [neg_eq_zero.1 h0, sub_zero]))] at h2'
  split_ifs at h2' <;> simp [ev_t] at h2'

theorem gen_smul_ne {j : ℕ} (h2 : 2 ≤ h) (k : Fin h) (c : XX h n j) : (gen h2 k : G h n) • c ≠ c := fun e =>
  Paper.prop_tower_cosets h2 k c 1 (by rw [map_one, one_smul, e])

/-- The edge of type k at a chamber. -/
noncomputable def edge {j : ℕ} (h2 : 2 ≤ h) (k : Fin h) (c : XX h n j) : EE h n h2 j :=
  open Classical in
  if hc : FQ h2 k (evX c) then ⟨(k, c), hc⟩ else ⟨(k, (gen h2 k : G h n) • c), (FQ_gen h2 k c).2 hc⟩

theorem edge_type {j : ℕ} (h2 : 2 ≤ h) (k : Fin h) (c : XX h n j) : (edge h2 k c).1.1 = k := by
  unfold edge
  split_ifs <;> rfl

theorem edge_end {j : ℕ} (h2 : 2 ≤ h) (k : Fin h) (c : XX h n j) :
    (edge h2 k c).1.2 = c ∨ (edge h2 k c).1.2 = (gen h2 k : G h n) • c := by
  unfold edge
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem edge_self {j : ℕ} (h2 : 2 ≤ h) (e : EE h n h2 j) : edge h2 e.1.1 e.1.2 = e := by
  unfold edge
  rw [dif_pos e.2]

theorem edge_gen {j : ℕ} (h2 : 2 ≤ h) (k : Fin h) (c : XX h n j) : edge h2 k ((gen h2 k : G h n) • c) = edge h2 k c := by
  unfold edge
  by_cases hc : FQ h2 k (evX c)
  · rw [dif_pos hc, dif_neg (fun e => (FQ_gen h2 k c).1 e hc)]
    exact Subtype.ext (Prod.ext rfl (gen_gen h2 k c))
  · rw [dif_neg hc, dif_pos ((FQ_gen h2 k c).2 hc)]

/-- The edges of one type are half of the chambers. -/
theorem card_edges (h2 : 2 ≤ h) (j : ℕ) (i : Fin h) :
    2 * (univ.filter fun e : EE h n h2 j => e.1.1 = i).card = 1 * Fintype.card (XX h n j) := by
  classical
  have h1 : (univ.filter fun e : EE h n h2 j => e.1.1 = i).card =
      (univ.filter fun c : XX h n j => FQ h2 i (evX c)).card := by
    refine Finset.card_bij' (fun e _ => e.1.2) (fun c _ => edge h2 i c) ?_ ?_ ?_ ?_
    · intro e he
      rw [mem_filter] at he ⊢
      exact ⟨mem_univ _, he.2 ▸ e.2⟩
    · intro c _
      rw [mem_filter]
      exact ⟨mem_univ _, edge_type h2 i c⟩
    · intro e he
      rw [mem_filter] at he
      rw [← he.2]
      exact edge_self h2 e
    · intro c hc
      rw [mem_filter] at hc
      unfold edge
      rw [dif_pos hc.2]
  have h3 : (univ.filter fun c : XX h n j => FQ h2 i (evX c)).card =
      (univ.filter fun c : XX h n j => ¬ FQ h2 i (evX c)).card := by
    refine Finset.card_bij' (fun c _ => (gen h2 i : G h n) • c) (fun c _ => (gen h2 i : G h n) • c) ?_ ?_ ?_ ?_
    · intro c hc
      rw [mem_filter] at hc ⊢
      exact ⟨mem_univ _, fun e => (FQ_gen h2 i c).1 e hc.2⟩
    · intro c hc
      rw [mem_filter] at hc ⊢
      exact ⟨mem_univ _, (FQ_gen h2 i c).2 hc.2⟩
    · intro c _; exact gen_gen h2 i c
    · intro c _; exact gen_gen h2 i c
  have h4 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (XX h n j))) (fun c => FQ h2 i (evX c))
  rw [Finset.card_univ] at h4
  rw [h1, one_mul]
  omega

theorem deg_edges (h2 : 2 ≤ h) (j : ℕ) (c : XX h n j) (i : Fin h) :
    (univ.filter fun e : EE h n h2 j => e.1.1 = i ∧ (e.1.2 = c ∨ (gen h2 e.1.1 : G h n) • e.1.2 = c)).card ≤ 1 := by
  rw [Finset.card_le_one]
  have key : ∀ e ∈ univ.filter fun e : EE h n h2 j => e.1.1 = i ∧ (e.1.2 = c ∨ (gen h2 e.1.1 : G h n) • e.1.2 = c),
      e = edge h2 i c := by
    intro e he
    rw [mem_filter] at he
    obtain ⟨-, h1, h3 | h3⟩ := he
    · rw [← h1, ← h3, edge_self]
    · rw [← h1, ← h3, edge_gen, edge_self]
  intro e he e' he'
  rw [key e he, key e' he']

/-- Near pairs of the unitriangular group. -/
abbrev NN (h : ℕ) [NeZero h] : Type := {p : Fin (h - 1) × U h // FU p.1 p.2}

noncomputable instance instFintypeNN : Fintype (NN h) := Fintype.ofFinite _

noncomputable instance instDecNN : DecidableEq (NN h) := Classical.decEq _

noncomputable instance instDecU : DecidableEq (U h) := Classical.decEq _

/-- The near pair {u, x_l u}. -/
noncomputable def npair (l : Fin (h - 1)) (u : U h) : NN h :=
  open Classical in if hu : FU l u then ⟨(l, u), hu⟩ else ⟨(l, x h l * u), (FU_iff l u).2 hu⟩

theorem npair_type (l : Fin (h - 1)) (u : U h) : (npair l u).1.1 = l := by
  unfold npair
  split_ifs <;> rfl

theorem npair_sym (l : Fin (h - 1)) (u : U h) :
    s(u, x h l * u) = s((npair l u).1.2, x h (npair l u).1.1 * (npair l u).1.2) := by
  unfold npair
  split_ifs
  · rfl
  · simp only
    rw [← mul_assoc, x_mul_self, one_mul, Sym2.eq_swap]

theorem npair_eq {l : Fin (h - 1)} {u u' : U h} (e : npair l u = npair l u') : u = u' ∨ u = x h l * u' := by
  unfold npair at e
  split_ifs at e with h1 h3 h3
  · exact Or.inl (congrArg (fun p => p.1.2) e)
  · exact Or.inr (congrArg (fun p => p.1.2) e)
  · right
    have h4 : x h l * u = u' := congrArg (fun p => p.1.2) e
    rw [← h4, ← mul_assoc, x_mul_self, one_mul]
  · left
    have h4 : x h l * u = x h l * u' := congrArg (fun p => p.1.2) e
    exact mul_left_cancel h4

theorem npair_self (ν : NN h) : npair ν.1.1 ν.1.2 = ν := by
  unfold npair
  rw [dif_pos ν.2]

theorem npair_x (l : Fin (h - 1)) (u : U h) : npair l (x h l * u) = npair l u := by
  unfold npair
  by_cases hu : FU l u
  · rw [dif_pos hu, dif_neg (fun e => (FU_iff l u).1 e hu)]
    refine Subtype.ext (Prod.ext rfl ?_)
    simp only
    rw [← mul_assoc, x_mul_self, one_mul]
  · rw [dif_neg hu, dif_pos ((FU_iff l u).2 hu)]

/-- The index of a type seen from the type i. -/
noncomputable def idx (i k : Fin h) (hk : k ≠ i) : Fin (h - 1) := (exists_sh hk).choose

theorem sh_idx (i k : Fin h) (hk : k ≠ i) : sh i (idx i k hk) = k := (exists_sh hk).choose_spec

theorem idx_sh (i : Fin h) (l : Fin (h - 1)) : idx i (sh i l) (sh_ne i l) = l :=
  sh_injective i (sh_idx i _ _)

theorem gen_idx (h2 : 2 ≤ h) (i k : Fin h) (hk : k ≠ i) : (gen h2 k : G h n) = th i (x h (idx i k hk)) := by
  rw [th_x h2, sh_idx]

/-- The edges of types other than i are the near pairs at the vertices of type i. -/
noncomputable def nearFun (h2 : 2 ≤ h) (j : ℕ) (i : Fin h) (e : {e : EE h n h2 j // e.1.1 ≠ i}) : VV h n j i × NN h :=
  (vert i e.1.1.2, npair (idx i e.1.1.1 e.2) (cor i e.1.1.2))

theorem nearFun_bijective (h2 : 2 ≤ h) (j : ℕ) (i : Fin h) : Function.Bijective (nearFun (n := n) h2 j i) := by
  constructor
  · rintro ⟨⟨⟨k, c⟩, hc⟩, hk⟩ ⟨⟨⟨k', c'⟩, hc'⟩, hk'⟩ e
    simp only [nearFun, Prod.mk.injEq] at e
    obtain ⟨e1, e2⟩ := e
    have hl : idx i k hk = idx i k' hk' := by
      have h6 : (npair (idx i k hk) (cor i c)).1.1 = (npair (idx i k' hk') (cor i c')).1.1 :=
        congrArg (fun p : NN h => p.1.1) e2
      rw [npair_type, npair_type] at h6
      exact h6
    have hkk : k = k' := by rw [← sh_idx i k hk, hl, sh_idx]
    subst hkk
    have hcc : c = c' := by
      rcases npair_eq e2 with e3 | e3
      · exact (vert_cor_bijective j i).1 (Prod.ext e1 e3)
      · exfalso
        have h3 : c = (gen h2 k : G h n) • c' := by
          refine (vert_cor_bijective j i).1 (Prod.ext ?_ ?_)
          · simp only
            rw [gen_idx h2 i k hk, vert_th, e1]
          · simp only
            rw [gen_idx h2 i k hk, cor_th, e3]
        have h4 : FQ h2 k (evX c) := hc
        rw [h3] at h4
        exact (FQ_gen h2 k c').1 h4 hc'
    subst hcc
    rfl
  · rintro ⟨v, ν⟩
    let l := ν.1.1
    let c : XX h n j := (th i ν.1.2 : G h n) • v.1
    have hk : sh i l ≠ i := sh_ne i l
    refine ⟨⟨edge h2 (sh i l) c, by rw [edge_type]; exact hk⟩, ?_⟩
    have h5 : ∀ (k : Fin h) (hk' : k ≠ i), k = sh i l → idx i k hk' = l := by
      rintro k hk' rfl
      exact idx_sh i l
    have hg : (gen h2 (sh i l) : G h n) = th i (x h l) := (th_x h2 i l).symm
    refine Prod.ext ?_ ?_
    · change vert i (edge h2 (sh i l) c).1.2 = v
      rcases edge_end h2 (sh i l) c with e | e
      · rw [e, vert_th, vert_of]
      · rw [e, hg, vert_th, vert_th, vert_of]
    · change npair (idx i (edge h2 (sh i l) c).1.1 _) (cor i (edge h2 (sh i l) c).1.2) = ν
      rw [h5 _ _ (edge_type h2 (sh i l) c)]
      rcases edge_end h2 (sh i l) c with e | e
      · rw [e, cor_th, v.2, mul_one]
        exact npair_self ν
      · rw [e, hg, cor_th, npair_x, cor_th, v.2, mul_one]
        exact npair_self ν

/-- The covering on edges. -/
noncomputable def prE {j : ℕ} (h2 : 2 ≤ h) (e : EE h n h2 j) : EE h n h2 (j + 1) :=
  ⟨(e.1.1, pr e.1.2), by rw [evX_pr]; exact e.2⟩

/-- The covering on vertices. -/
noncomputable def prV {j : ℕ} {i : Fin h} (v : VV h n j i) : VV h n (j + 1) i := ⟨pr v.1, by rw [cor_pr, v.2]⟩

theorem vert_pr {j : ℕ} (i : Fin h) (c : XX h n j) : vert i (pr c) = prV (vert i c) := by
  refine Subtype.ext ?_
  rw [vert_val, cor_pr, ← Paper.prop_tower_equivariant]
  rfl

theorem card_XX {j : ℕ} (hj : j ≤ JJ h n) : Fintype.card (XX h n j) * (2 ^ ee h) ^ j = Nat.card (G h n) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Gam h n j), card_Gam h n hj, Nat.card_eq_fintype_card]

theorem card_XX_succ {j : ℕ} (hj : j < JJ h n) :
    Fintype.card (XX h n j) = 2 ^ ee h * Fintype.card (XX h n (j + 1)) := by
  have h1 := card_XX (h := h) (n := n) hj.le
  have h3 := card_XX (h := h) (n := n) (Nat.succ_le_of_lt hj)
  have hp : 0 < (2 ^ ee h) ^ j := Nat.pow_pos (Nat.pow_pos (by omega))
  refine Nat.eq_of_mul_eq_mul_right hp ?_
  rw [h1, ← h3, Nat.succ_eq_add_one, pow_succ]
  ring

/-- **Paper: Proposition prop:tower.** The projections "are b to one". -/
theorem _root_.Paper.prop_tower_fibre {j : ℕ} (hj : j < JJ h n) (d : XX h n (j + 1)) :
    (univ.filter fun c : XX h n j => pr c = d).card = 2 ^ ee h := by
  classical
  have h1 : ∀ (g : G h n) (d : XX h n (j + 1)), (univ.filter fun c : XX h n j => pr c = d).card =
      (univ.filter fun c : XX h n j => pr c = g • d).card := by
    intro g d
    refine Finset.card_bij' (fun c _ => g • c) (fun c _ => g⁻¹ • c) ?_ ?_ ?_ ?_
    · intro c hc
      rw [mem_filter] at hc ⊢
      exact ⟨mem_univ _, by rw [Paper.prop_tower_equivariant, hc.2]⟩
    · intro c hc
      rw [mem_filter] at hc ⊢
      exact ⟨mem_univ _, by rw [Paper.prop_tower_equivariant, hc.2, inv_smul_smul]⟩
    · intro c _; exact inv_smul_smul g c
    · intro c _; exact smul_inv_smul g c
  have h3 : ∀ d' : XX h n (j + 1), (univ.filter fun c : XX h n j => pr c = d').card =
      (univ.filter fun c : XX h n j => pr c = d).card := by
    intro d'
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (G h n) d' d
    exact h1 g d'
  have h4 : Fintype.card (XX h n j) = ∑ d' : XX h n (j + 1), (univ.filter fun c : XX h n j => pr c = d').card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise fun c _ => mem_univ _
  rw [Finset.sum_congr rfl fun d' _ => h3 d', Finset.sum_const, Finset.card_univ, smul_eq_mul, card_XX_succ hj,
    mul_comm] at h4
  exact (Nat.eq_of_mul_eq_mul_left (Fintype.card_pos_iff.2 ⟨d⟩) h4).symm

theorem fibre_edges {j : ℕ} (h2 : 2 ≤ h) (hj : j < JJ h n) (d : EE h n h2 (j + 1)) :
    (univ.filter fun e : EE h n h2 j => prE h2 e = d).card ≤ 2 ^ ee h := by
  rw [← Paper.prop_tower_fibre hj d.1.2]
  refine Finset.card_le_card_of_injOn (fun e => e.1.2) ?_ ?_
  · intro e he
    rw [Finset.mem_coe, mem_filter] at he ⊢
    exact ⟨mem_univ _, congrArg (fun p : EE h n h2 (j + 1) => p.1.2) he.2⟩
  · intro e he e' he' hee
    rw [Finset.mem_coe, mem_filter] at he he'
    have h1 : e.1.1 = e'.1.1 := by
      have a1 := congrArg (fun p : EE h n h2 (j + 1) => p.1.1) he.2
      have a2 := congrArg (fun p : EE h n h2 (j + 1) => p.1.1) he'.2
      exact a1.trans a2.symm
    exact Subtype.ext (Prod.ext h1 hee)

/-- **Paper: Proposition prop:tower(b).** "Exactly b of them onto each": b cosets over each, a coset being given by its
one element in VV (prop_tower_representatives). -/
theorem _root_.Paper.prop_tower_cosets_over {j : ℕ} {i : Fin h} (hj : j < JJ h n) (v : VV h n (j + 1) i) :
    (univ.filter fun w : VV h n j i => prV w = v).card = 2 ^ ee h := by
  rw [← Paper.prop_tower_fibre hj v.1]
  refine Finset.card_bij (fun w _ => w.1) (fun w hw => mem_filter.2 ⟨mem_univ _, congrArg Subtype.val (mem_filter.1 hw).2⟩)
    (fun w _ w' _ e => Subtype.ext e) (fun c hc => ⟨⟨c, ?_⟩, mem_filter.2 ⟨mem_univ _, Subtype.ext (mem_filter.1 hc).2⟩, rfl⟩)
  rw [← cor_pr, (mem_filter.1 hc).2]
  exact v.2

/-- **Paper: Proposition prop:tower(a).** "We call its orbits i-cosets": every i-coset has one element in VV. -/
theorem _root_.Paper.prop_tower_representatives {j : ℕ} (i : Fin h) (c : XX h n j) :
    ∃! v : VV h n j i, ∃ u : U h, (th i u : G h n) • v.1 = c := by
  refine ⟨vert i c, ⟨cor i c, th_vert i c⟩, ?_⟩
  rintro v ⟨u, rfl⟩
  rw [vert_th, vert_of]

/-- Hosts. -/
theorem exists_host (j : ℕ) (i : Fin h) : ∃ f : VV h n j i → XX h n (j + 1), j < JJ h n →
    Function.Injective f ∧ ∀ v, vert i (f v) = prV v := by
  classical
  by_cases hj : j < JJ h n
  · have h1 : ∀ d : VV h n (j + 1) i, Nonempty ({v : VV h n j i // prV v = d} ↪ U h) := by
      intro d
      refine Function.Embedding.nonempty_of_card_le ?_
      rw [card_U, ← ee, ← Paper.prop_tower_cosets_over hj d, Fintype.card_subtype]
    let φ : ∀ d : VV h n (j + 1) i, {v : VV h n j i // prV v = d} ↪ U h := fun d => (h1 d).some
    have hφ : ∀ (v : VV h n j i) (d : VV h n (j + 1) i) (hv : prV v = d), φ (prV v) ⟨v, rfl⟩ = φ d ⟨v, hv⟩ := by
      rintro v _ rfl
      rfl
    refine ⟨fun v => (th i (φ (prV v) ⟨v, rfl⟩) : G h n) • (prV v).1, fun _ => ⟨?_, fun v => ?_⟩⟩
    · intro v v' e
      simp only at e
      have e1 : prV v = prV v' := by
        have := congrArg (vert i) e
        rwa [vert_th, vert_th, vert_of, vert_of] at this
      have e2 : φ (prV v) ⟨v, rfl⟩ = φ (prV v') ⟨v', rfl⟩ := by
        have := congrArg (cor i) e
        rwa [cor_th, cor_th, (prV v).2, (prV v').2, mul_one, mul_one] at this
      rw [hφ v (prV v') e1] at e2
      exact congrArg Subtype.val ((φ (prV v')).injective e2)
    · rw [vert_th, vert_of]
  · exact ⟨fun v => pr v.1, fun hj' => absurd hj' hj⟩

end Nc.Tower
