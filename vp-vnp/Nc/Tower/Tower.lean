/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tower.Inst
import Nc.Tower.Base

/-!
# The tower as a structure, and routes
-/

set_option linter.unusedSectionVars false

namespace Nc.Tower

open Finset

attribute [-instance] Subtype.instBEq

variable (h n : ℕ) [NeZero h]

/-- **The tower.** -/
noncomputable def tower (h2 : 2 ≤ h) : Nc.Tow.Tower h (2 ^ ee h) (2 ^ ee h) (JJ h n) 1 where
  X := XX h n
  Ed := EE h n h2
  V := VV h n
  Fl := U h
  Nr := NN h
  fX := instFintypeXX h n
  dX := instDecXX h n
  fE := instFintypeEE h2
  dE := instDecEE h2
  fV := instFintypeVV
  dV := instDecVV
  fF := inferInstance
  dF := inferInstance
  fN := inferInstance
  dN' := inferInstance
  e0 := fun e => e.1.2
  e1 := fun e => (gen h2 e.1.1 : G h n) • e.1.2
  e_ne := fun e => (gen_smul_ne h2 _ _).symm
  ty := fun e => e.1.1
  card_ed := fun j _ i => card_edges h2 j i
  deg := fun j _ c i => deg_edges h2 j c i
  vx := vert
  co := cor
  vx_co := fun _ i => vert_cor_bijective _ i
  card_fl := card_U h
  cN := fun ν => ν.1.2
  dN := fun ν => x h ν.1.1 * ν.1.2
  n_ne := fun ν e => x_ne_one ν.1.1 (by simpa using e.symm)
  nr := fun _ i => Equiv.ofBijective _ (nearFun_bijective h2 _ i)
  nr_vx0 := fun _ i e => rfl
  nr_vx1 := fun _ i e => by
    change vert i ((gen h2 e.1.1.1 : G h n) • e.1.1.2) = vert i e.1.1.2
    rw [gen_idx h2 i _ e.2, vert_th]
  nr_co := fun _ i e => by
    change s(cor i e.1.1.2, cor i ((gen h2 e.1.1.1 : G h n) • e.1.1.2)) =
      s((npair (idx i e.1.1.1 e.2) (cor i e.1.1.2)).1.2,
        x h (npair (idx i e.1.1.1 e.2) (cor i e.1.1.2)).1.1 * (npair (idx i e.1.1.1 e.2) (cor i e.1.1.2)).1.2)
    rw [gen_idx h2 i _ e.2, cor_th]
    exact npair_sym _ _
  π := pr
  πE := prE h2
  πV := prV
  π_ends := fun _ e => by
    change s(pr e.1.2, (gen h2 e.1.1 : G h n) • pr e.1.2) = s(pr e.1.2, pr ((gen h2 e.1.1 : G h n) • e.1.2))
    rw [Paper.prop_tower_equivariant]
  π_ty := fun _ _ => rfl
  card_X := fun _ hj => card_XX_succ hj
  fibre := fun hj d => fibre_edges h2 hj d
  π_vx := fun _ i c => vert_pr i c
  π_co := fun _ i c => cor_pr i c
  host := fun {j} i => (exists_host (n := n) j i).choose
  host_inj := fun {j} hj i => ((exists_host (n := n) j i).choose_spec hj).1
  host_vx := fun {j} hj i v => ((exists_host (n := n) j i).choose_spec hj).2 v

variable {h n}

/-- The edges along a list of types. -/
noncomputable def path (h2 : 2 ≤ h) {j : ℕ} : List (Fin h) → XX h n j → List (EE h n h2 j)
  | [], _ => []
  | k :: l, c => edge h2 k c :: path h2 l ((gen h2 k : G h n) • c)

theorem length_path (h2 : 2 ≤ h) {j : ℕ} (l : List (Fin h)) (c : XX h n j) : (path h2 l c).length = l.length := by
  induction l generalizing c with
  | nil => rfl
  | cons k l ih => rw [path, List.length_cons, ih, List.length_cons]

theorem step_edge (h2 : 2 ≤ h) {j : ℕ} (k : Fin h) (c : XX h n j) :
    (tower h n h2).step (edge h2 k c) c = (gen h2 k : G h n) • c := by
  have hu : (tower h n h2).step (edge h2 k c) c = if (edge h2 k c).1.2 = c then
      (gen h2 (edge h2 k c).1.1 : G h n) • (edge h2 k c).1.2 else (edge h2 k c).1.2 := rfl
  rw [hu, edge_type]
  rcases edge_end h2 k c with e | e
  · rw [if_pos e, e]
  · rw [if_neg, e]
    rw [e]
    exact gen_smul_ne h2 k c

theorem walk_path (h2 : 2 ≤ h) {j : ℕ} (l : List (Fin h)) (c : XX h n j) :
    (tower h n h2).Walk c (path h2 l c) (((l.reverse.map (gen h2)).prod : G h n) • c : XX h n j) := by
  induction l generalizing c with
  | nil =>
    change c = ((([] : List (Fin h)).reverse.map (gen h2)).prod : G h n) • c
    simp
  | cons k l ih =>
    refine ⟨?_, ?_⟩
    · rcases edge_end h2 k c with e | e
      · exact Or.inl e
      · right
        change (gen h2 (edge h2 k c).1.1 : G h n) • (edge h2 k c).1.2 = c
        rw [edge_type, e, gen_gen]
    · rw [step_edge]
      have h3 := ih ((gen h2 k : G h n) • c)
      rw [← mul_smul] at h3
      simpa using h3

theorem count_path (h2 : 2 ≤ h) {j : ℕ} (l : List (Fin h)) (e : EE h n h2 j) :
    ∑ c : XX h n j, (path h2 l c).count e ≤ 2 * l.length := by
  induction l with
  | nil => simp [path]
  | cons k l ih =>
    have h1 : ∀ c : XX h n j, (path h2 (k :: l) c).count e =
        (path h2 l ((gen h2 k : G h n) • c)).count e + if edge h2 k c = e then 1 else 0 := by
      intro c
      rw [path, List.count_cons]
      simp only [beq_iff_eq]
    rw [Finset.sum_congr rfl fun c _ => h1 c, Finset.sum_add_distrib]
    have h3 : ∑ c : XX h n j, (path h2 l ((gen h2 k : G h n) • c)).count e = ∑ c : XX h n j, (path h2 l c).count e :=
      Equiv.sum_comp (MulAction.toPerm (gen h2 k : G h n)) fun c => (path h2 l c).count e
    have h4 : (∑ c : XX h n j, if edge h2 k c = e then 1 else 0) ≤ 2 := by
      rw [← Finset.card_filter]
      have h5 : (univ.filter fun c : XX h n j => edge h2 k c = e) ⊆ {e.1.2, (gen h2 k : G h n) • e.1.2} := by
        intro c hc
        rw [mem_filter] at hc
        rw [mem_insert, mem_singleton]
        rcases edge_end h2 k c with e1 | e1
        · left
          rw [← hc.2, e1]
        · right
          rw [← hc.2, e1, gen_gen]
      exact (Finset.card_le_card h5).trans Finset.card_le_two
    rw [h3, List.length_cons]
    omega

/-- The chambers of the first level are the elements of the group. -/
theorem smul_bijective (c : XX h n 0) : Function.Bijective fun g : G h n => g • c := by
  constructor
  · intro g g' e
    induction c using QuotientGroup.induction_on with
    | H a =>
      have e1 : (QuotientGroup.mk (g * a) : XX h n 0) = QuotientGroup.mk (g' * a) := e
      have e2 := QuotientGroup.eq.1 e1
      rw [Gam_zero, Subgroup.mem_bot] at e2
      have e3 : g * a = g' * a := inv_mul_eq_one.1 e2
      exact mul_right_cancel e3
  · intro d
    exact MulAction.exists_smul_eq (G h n) c d

/-- The route. -/
noncomputable def rte (h2 : 2 ≤ h) (w : G h n → List (Fin h)) (c c' : XX h n 0) : List (EE h n h2 0) :=
  path h2 (w ((Equiv.ofBijective _ (smul_bijective c)).symm c')).reverse c

theorem rte_walk (h2 : 2 ≤ h) (w : G h n → List (Fin h)) (hw : ∀ g, ((w g).map (gen h2)).prod = g) (c c' : XX h n 0) :
    (tower h n h2).Walk c (rte h2 w c c') c' := by
  have h1 := walk_path h2 (w ((Equiv.ofBijective _ (smul_bijective c)).symm c')).reverse c
  rw [List.reverse_reverse, hw] at h1
  have h3 : ((Equiv.ofBijective _ (smul_bijective c)).symm c' : G h n) • c = c' :=
    (Equiv.ofBijective _ (smul_bijective c)).apply_symm_apply c'
  rw [h3] at h1
  exact h1

theorem rte_length (h2 : 2 ≤ h) (w : G h n → List (Fin h)) {m : ℕ} (hw : ∀ g, (w g).length ≤ m) (c c' : XX h n 0) :
    (rte h2 w c c').length ≤ m := by
  rw [rte, length_path, List.length_reverse]
  exact hw _

theorem rte_use (h2 : 2 ≤ h) (w : G h n → List (Fin h)) {m : ℕ} (hw : ∀ g, (w g).length ≤ m) (e : EE h n h2 0) :
    ∑ c, ∑ c', (rte h2 w c c').count e ≤ 2 * (Fintype.card (XX h n 0) * m) := by
  classical
  have h1 : ∀ c : XX h n 0, ∑ c' : XX h n 0, (rte h2 w c c').count e =
      ∑ g : G h n, (path h2 (w g).reverse c).count e := fun c =>
    Equiv.sum_comp (Equiv.ofBijective _ (smul_bijective c)).symm fun g => (path h2 (w g).reverse c).count e
  rw [Finset.sum_congr rfl fun c _ => h1 c, Finset.sum_comm]
  calc ∑ g : G h n, ∑ c : XX h n 0, (path h2 (w g).reverse c).count e ≤ ∑ _g : G h n, 2 * m := by
        refine Finset.sum_le_sum fun g _ => (count_path h2 _ e).trans ?_
        rw [List.length_reverse]
        exact Nat.mul_le_mul_left _ (hw g)
    _ = 2 * (Fintype.card (XX h n 0) * m) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
          Fintype.card_congr (Equiv.ofBijective _ (smul_bijective (QuotientGroup.mk 1 : XX h n 0)))]
        ring

/-- **Routes.** -/
theorem exists_routes (h2 : 2 ≤ h) {m : ℕ} (hm : ∀ g : G h n, WL h2 g m) :
    Nonempty (Nc.Tow.Routes (tower h n h2) m (2 * (Fintype.card (XX h n 0) * m))) := by
  choose w hw1 hw2 using hm
  exact ⟨{ rt := rte h2 w
           walk := rte_walk h2 w hw2
           len := rte_length h2 w hw1
           use := rte_use h2 w hw1 }⟩

/-- Sums over the near pairs. -/
theorem sum_NN {M : Type*} [AddCommMonoid M] (f : Fin (h - 1) → U h → M) (hf : ∀ l u, f l (x h l * u) = f l u) :
    ∑ l, ∑ u, f l u = ∑ ν : NN h, f ν.1.1 ν.1.2 + ∑ ν : NN h, f ν.1.1 ν.1.2 := by
  classical
  rw [← Fintype.sum_prod_type (fun p : Fin (h - 1) × U h => f p.1 p.2),
    ← Finset.sum_filter_add_sum_filter_not univ (fun p : Fin (h - 1) × U h => FU p.1 p.2)]
  have h1 : ∑ p ∈ univ.filter (fun p : Fin (h - 1) × U h => FU p.1 p.2), f p.1 p.2 = ∑ ν : NN h, f ν.1.1 ν.1.2 := by
    refine Finset.sum_bij' (fun p hp => (⟨p, (mem_filter.1 hp).2⟩ : NN h)) (fun ν _ => ν.1) ?_ ?_ ?_ ?_ ?_
    · intro p _; exact mem_univ _
    · intro ν _; exact mem_filter.2 ⟨mem_univ _, ν.2⟩
    · intro p _; rfl
    · intro ν _; rfl
    · intro p _; rfl
  have h3 : ∑ p ∈ univ.filter (fun p : Fin (h - 1) × U h => ¬ FU p.1 p.2), f p.1 p.2 =
      ∑ p ∈ univ.filter (fun p : Fin (h - 1) × U h => FU p.1 p.2), f p.1 p.2 := by
    refine Finset.sum_bij' (fun p _ => (p.1, x h p.1 * p.2)) (fun p _ => (p.1, x h p.1 * p.2)) ?_ ?_ ?_ ?_ ?_
    · intro p hp
      rw [mem_filter] at hp ⊢
      exact ⟨mem_univ _, (FU_iff _ _).2 hp.2⟩
    · intro p hp
      rw [mem_filter] at hp ⊢
      exact ⟨mem_univ _, fun e => (FU_iff _ _).1 e hp.2⟩
    · intro p _
      refine Prod.ext rfl ?_
      change x h p.1 * (x h p.1 * p.2) = p.2
      rw [← mul_assoc, x_mul_self, one_mul]
    · intro p _
      refine Prod.ext rfl ?_
      change x h p.1 * (x h p.1 * p.2) = p.2
      rw [← mul_assoc, x_mul_self, one_mul]
    · intro p _
      exact (hf _ _).symm
  rw [h3, h1]

section Numbers

variable (h n)

theorem card_XJ (h2 : 2 ≤ h) :
    Fintype.card ((tower h n h2).X (JJ h n)) < Nat.card (SL2 h) * 2 ^ ee h := by
  have h1 := card_XX (h := h) (n := n) (j := JJ h n) le_rfl
  rw [card_G] at h1
  have he : 0 < ee h := by
    unfold ee
    have : 2 ≤ h * (h - 1) := by
      calc 2 = 2 * 1 := rfl
        _ ≤ h * (h - 1) := Nat.mul_le_mul h2 (by omega)
    omega
  have h3 : (h ^ 2 - 1) * n < ee h * (JJ h n + 1) := by
    have := Nat.lt_mul_div_succ ((h ^ 2 - 1) * n) he
    unfold JJ
    omega
  have h4 : 2 ^ ((h ^ 2 - 1) * n) < (2 ^ ee h) ^ (JJ h n) * 2 ^ ee h := by
    rw [← pow_succ, ← pow_mul]
    exact Nat.pow_lt_pow_right (by omega) h3
  have hp : 0 < (2 ^ ee h) ^ JJ h n := Nat.pow_pos (Nat.pow_pos (by omega))
  refine Nat.lt_of_mul_lt_mul_right (a := (2 ^ ee h) ^ JJ h n) ?_
  have h5 : Fintype.card ((tower h n h2).X (JJ h n)) * (2 ^ ee h) ^ JJ h n = Nat.card (SL2 h) * 2 ^ ((h ^ 2 - 1) * n) := h1
  rw [h5, mul_assoc, mul_comm (2 ^ ee h)]
  exact Nat.mul_lt_mul_of_pos_left h4 Nat.card_pos

end Numbers

end Nc.Tower
