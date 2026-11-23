/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tape.Run
import Nc.Tape.Refine

/-!
# Blocks of a run

A run of `K * T` steps is cut into `K` blocks of `T` steps. The value of the automaton is a sum, over the states
between the blocks, over the ways to cut the inputs, and over the common segments `X s α β` written on tape `s`
by block `α` and read by block `β` (staircase support), of the product of the weights of the blocks.
-/

set_option linter.unusedSectionVars false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {Γ S J Q : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype J] [DecidableEq J] [Fintype Q] [DecidableEq Q]

/-- A product of matrices as a sum over paths. -/
theorem prod_path {K : ℕ} (M : Fin K → Matrix Q Q F) (a b : Q) :
    (List.ofFn M).prod a b = ∑ q : Fin (K + 1) → Q,
      if q 0 = a ∧ q (Fin.last K) = b then ∏ k, M k (q k.castSucc) (q k.succ) else 0 := by
  induction K generalizing a with
  | zero =>
    simp only [List.ofFn_zero, List.prod_nil, Finset.univ_eq_empty, Finset.prod_empty]
    rw [Matrix.one_apply]
    by_cases h : a = b
    · subst h
      rw [if_pos rfl, Finset.sum_eq_single fun _ => a]
      · simp
      · intro q _ hne
        rw [if_neg]
        rintro ⟨h0, -⟩
        apply hne
        funext k
        have : k = 0 := Fin.ext (by omega)
        rw [this, h0]
      · simp
    · rw [if_neg h, Finset.sum_eq_zero]
      intro q _
      rw [if_neg]
      rintro ⟨h0, h1⟩
      apply h
      rw [← h0, ← h1]
      congr 1
  | succ K ih =>
    have hR : (∑ q : Fin (K + 1 + 1) → Q, if q 0 = a ∧ q (Fin.last (K + 1)) = b then
        ∏ k, M k (q k.castSucc) (q k.succ) else 0) = ∑ q : Fin (K + 1) → Q,
        if q (Fin.last K) = b then M 0 a (q 0) * ∏ k : Fin K, M k.succ (q k.castSucc) (q k.succ) else 0 := by
      rw [← (Fin.consEquiv fun _ : Fin (K + 2) => Q).sum_comp, Fintype.sum_prod_type,
        Finset.sum_eq_single a]
      · refine Finset.sum_congr rfl fun q _ => ?_
        have e1 : (Fin.consEquiv fun _ : Fin (K + 2) => Q) (a, q) = (Fin.cons a q : Fin (K + 2) → Q) := rfl
        simp only [e1]
        have e2 : (Fin.cons a q : Fin (K + 2) → Q) (Fin.last (K + 1)) = q (Fin.last K) := by
          rw [← Fin.succ_last, Fin.cons_succ]
        have e3 : (Fin.cons a q : Fin (K + 2) → Q) 0 = a := rfl
        rw [e2, e3]
        simp only [true_and]
        split_ifs
        · rw [Fin.prod_univ_succ]
          rfl
        · rfl
      · intro a' _ ha'
        refine Finset.sum_eq_zero fun q _ => if_neg ?_
        rintro ⟨h0, -⟩
        exact ha' h0
      · simp
    rw [hR, List.ofFn_succ, List.prod_cons, Matrix.mul_apply]
    simp only [ih, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_eq_single (q 0)]
    · by_cases h : q (Fin.last K) = b <;> simp [h]
    · intro c _ hc
      rw [if_neg (fun hh => hc hh.1.symm), mul_zero]
    · simp

theorem emit_append (o₁ o₂ : List (Letter S J Γ)) (z : Ch S J) : emit (o₁ ++ o₂) z = emit o₁ z ++ emit o₂ z := by
  simp [emit, List.reduceOption_append, proj_append]

theorem emit_flatten {K : ℕ} (o : Fin K → List (Letter S J Γ)) (z : Ch S J) :
    emit (List.ofFn o).flatten z = cat fun k => emit (o k) z := by
  induction K with
  | zero => simp [emit, cat]
  | succ K ih => rw [List.ofFn_succ, List.flatten_cons, emit_append, ih, cat_succ]

theorem length_emit_le (o : List (Letter S J Γ)) (z : Ch S J) : (emit o z).length ≤ o.length := by
  have h1 := sum_length_proj o.reduceOption
  have h2 := List.reduceOption_length_le o
  exact (Finset.single_le_sum (f := fun z => (proj o.reduceOption z).length) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ z)).trans (h1.le.trans h2)

/-- The weight of the blocks of `T` steps from `q` to `q'` that emit `v`. -/
noncomputable def blockW (mu : Letter S J Γ → Matrix Q Q F) (T : ℕ) (q q' : Q) (v : Ch S J → List Γ) : F :=
  ∑ o : Fin T → Letter S J Γ, if emit (List.ofFn o) = v then ((List.ofFn o).map mu).prod q q' else 0

/-- Words of length at most `T`. -/
noncomputable def wordsLe (Γ : Type*) [Fintype Γ] (T : ℕ) : Finset (List Γ) :=
  (List.finite_length_le Γ T).toFinset

theorem mem_wordsLe {T : ℕ} {w : List Γ} : w ∈ wordsLe Γ T ↔ w.length ≤ T := by simp [wordsLe]

/-- A block emits at most `T` letters on a channel. -/
theorem blockW_ne_zero {mu : Letter S J Γ → Matrix Q Q F} {T : ℕ} {q q' : Q} {v : Ch S J → List Γ}
    (h : blockW mu T q q' v ≠ 0) (z : Ch S J) : v z ∈ wordsLe Γ T := by
  obtain ⟨o, -, ho⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at ho with he
  · rw [mem_wordsLe, ← he]
    simpa using length_emit_le (List.ofFn o) z
  · exact absurd rfl ho

/-- The value as a sum over states and over what the blocks emit. -/
theorem runVal_blocks (mu : Letter S J Γ → Matrix Q Q F) (i e : Q) (K T : ℕ) (u : J → List Γ) :
    runVal mu i e (K * T) u = ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
      ∑ v ∈ Fintype.piFinset fun _ : Fin K => Fintype.piFinset fun _ : Ch S J => wordsLe Γ T,
        if (∀ s, cat (fun k => v k (.tp s false)) = cat fun k => v k (.tp s true)) ∧
          ∀ j, cat (fun k => v k (.inp j)) = u j then
          ∏ k, blockW mu T (q k.castSucc) (q k.succ) (v k) else 0
      else 0 := by
  classical
  -- runs as families of blocks
  have h1 : runVal mu i e (K * T) u = ∑ o : Fin K → Fin T → Letter S J Γ,
      if (∀ s, cat (fun k => emit (List.ofFn (o k)) (.tp s false)) =
          cat fun k => emit (List.ofFn (o k)) (.tp s true)) ∧
        ∀ j, cat (fun k => emit (List.ofFn (o k)) (.inp j)) = u j then
      ((List.ofFn fun k => ((List.ofFn (o k)).map mu).prod)).prod i e else 0 := by
    rw [runVal]
    let eq : (Fin K → Fin T → Letter S J Γ) ≃ (Fin (K * T) → Letter S J Γ) :=
      (Equiv.curry (Fin K) (Fin T) (Letter S J Γ)).symm.trans (finProdFinEquiv.arrowCongr (Equiv.refl _))
    rw [← eq.sum_comp]
    refine Finset.sum_congr rfl fun o _ => ?_
    have e1 : List.ofFn (eq o) = (List.ofFn fun k => List.ofFn (o k)).flatten := by
      rw [List.ofFn_mul]
      congr 1
      congr 1
      funext k
      congr 1
      funext l
      have : finProdFinEquiv.symm ⟨k.1 * T + l.1, by
          calc k.1 * T + l.1 < (k.1 + 1) * T := by nlinarith [l.2]
            _ ≤ K * T := Nat.mul_le_mul_right _ k.2⟩ = (k, l) := by
        rw [Equiv.symm_apply_eq]
        apply Fin.ext
        simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
      simp only [eq, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id,
        Equiv.curry_symm_apply, Function.uncurry, this]
    rw [e1]
    simp only [Matched, emit_flatten]
    congr 1
    rw [List.map_flatten, List.prod_flatten]
    congr 2
    simp [List.map_ofFn, Function.comp_def]
  rw [h1]
  simp only [prod_path]
  have h2 : ∀ (o : Fin K → Fin T → Letter S J Γ) (c : Prop) [Decidable c],
      (if c then ∑ q : Fin (K + 1) → Q, (if q 0 = i ∧ q (Fin.last K) = e then
        ∏ k, ((List.ofFn (o k)).map mu).prod (q k.castSucc) (q k.succ) else 0) else 0) =
      ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
        (if c then ∏ k, ((List.ofFn (o k)).map mu).prod (q k.castSucc) (q k.succ) else 0) else 0 := by
    intro o c _
    by_cases hc : c
    · simp only [if_pos hc]
    · simp [hc]
  simp only [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases hq : q 0 = i ∧ q (Fin.last K) = e
  swap
  · simp [hq]
  simp only [if_pos hq]
  -- group the families of blocks by what they emit
  have h3 : ∀ o : Fin K → Fin T → Letter S J Γ, (fun k => emit (List.ofFn (o k))) ∈
      Fintype.piFinset fun _ : Fin K => Fintype.piFinset fun _ : Ch S J => wordsLe Γ T := by
    intro o
    simp only [Fintype.mem_piFinset, mem_wordsLe]
    intro k z
    simpa using length_emit_le (List.ofFn (o k)) z
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun o : Fin K → Fin T → Letter S J Γ =>
    fun k => emit (List.ofFn (o k))) (fun o _ => h3 o)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_filter]
  by_cases hv : (∀ s, cat (fun k => v k (.tp s false)) = cat fun k => v k (.tp s true)) ∧
      ∀ j, cat (fun k => v k (.inp j)) = u j
  · rw [if_pos hv]
    simp only [blockW]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun o _ => ?_
    by_cases ho : (fun k => emit (List.ofFn (o k))) = v
    · have ho' : ∀ k, emit (List.ofFn (o k)) = v k := fun k => congrFun ho k
      rw [if_pos ho, if_pos (by simpa only [ho'] using hv)]
      exact Finset.prod_congr rfl fun k _ => by rw [if_pos (ho' k)]
    · rw [if_neg ho]
      symm
      have : ∃ k, emit (List.ofFn (o k)) ≠ v k := by
        by_contra hc
        push Not at hc
        exact ho (funext hc)
      obtain ⟨k, hk⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)
  · rw [if_neg hv, Finset.sum_eq_zero]
    intro o _
    split_ifs with ho hc
    · exfalso
      have ho' : ∀ k, emit (List.ofFn (o k)) = v k := fun k => congrFun ho k
      simp only [ho'] at hc
      exact hv hc
    · rfl
    · rfl

end Nc
