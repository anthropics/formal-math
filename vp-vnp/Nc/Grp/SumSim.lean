/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.BaseProg

/-!
# Sums over simulations
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem sumL_toList {X β : Type} [Fintype X] (f : X → A × β) (G : β → A) :
    sumL ((univ : Finset X).toList.map f) G = ∑ x, (f x).1 * G (f x).2 := by
  rw [sumL, List.map_map, Finset.sum_map_toList]
  rfl

theorem sumL_runL_succ {Λ : Type} {nC nI nO : ℕ} (tab : Fin nC → (Fin nI → Bool) → List (Opt nC nO Λ)) (k : ℕ)
    (s : TSt nC nI nO Λ) (G : TSt nC nI nO Λ → A) :
    sumL (runL θ tab (k + 1) s) G = sumL (stepL θ tab s) fun s' => sumL (runL θ tab k s') G := by
  rw [runL, List.replicate_succ, foldL, sumL_bindL]
  rfl

theorem foldL_append {β ε : Type} (f : ε → β → List (A × β)) (xs ys : List ε) (s : β) (G : β → A) :
    sumL (foldL f (xs ++ ys) s) G = sumL (foldL f xs s) fun s' => sumL (foldL f ys s') G := by
  induction xs generalizing s with
  | nil => rw [List.nil_append, foldL, sumL_single]
  | cons x xs ih =>
    rw [List.cons_append, foldL, foldL, sumL_bindL, sumL_bindL]
    exact sumL_congr fun p _ => ih _

section sim

variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}
  (mu : Letter S Unit Γ → Matrix Q Q A) (cb : Option Γ → Fin c → Bool)

theorem sumL_sim (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q') (k : ℕ) (q : Q) (f : Outs S)
    (G : TSt (Fintype.card Q) 0 (nT S + nT S) (List Bool) → A) :
    sumL (runL θ (simTab θ mu cb) k (qn Q q, Fin.elim0, f)) G = ∑ o : Fin k → Letter S Unit Γ, ∑ q' : Q,
      ((List.ofFn o).map mu).prod q q' * G (qn Q q', Fin.elim0, fun j =>
        (List.ofFn o).reverse.flatMap (fun z => pushOf cb z j) ++ f j) := by
  induction k generalizing q f with
  | zero =>
    rw [runL, List.replicate_zero, foldL, sumL_single, Fintype.sum_unique]
    simp only [List.ofFn_zero, List.map_nil, List.prod_nil, List.reverse_nil, List.flatMap_nil, List.nil_append]
    rw [Finset.sum_eq_single q]
    · rw [Matrix.one_apply_eq, one_mul]
    · intro q' _ hq'
      rw [Matrix.one_apply_ne hq'.symm, zero_mul]
    · simp
  | succ k ih =>
    rw [sumL_runL_succ]
    have h1 : sumL (stepL θ (simTab θ mu cb) (qn Q q, Fin.elim0, f)) (fun s' => sumL (runL θ (simTab θ mu cb) k s') G) =
        ∑ z : Letter S Unit Γ × Q, mu z.1 q z.2 * sumL (runL θ (simTab θ mu cb) k (qn Q z.2, Fin.elim0, fun j =>
          pushOf cb z.1 j ++ f j)) G := by
      rw [stepL, simTab, List.map_map, sumL_toList]
      refine Finset.sum_congr rfl fun z _ => ?_
      have e0 : (fun i : Fin 0 => ((Fin.elim0 : Fin 0 → List Bool) i).tail) = Fin.elim0 := funext fun i => i.elim0
      simp only [Function.comp_apply, Opt.app, e0, Equiv.symm_apply_apply, we_val (hmu _ _ _)]
    rw [h1, Fintype.sum_prod_type, ← (Fin.consEquiv fun _ : Fin (k + 1) => Letter S Unit Γ).sum_comp,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [ih]
    have h2 : ∀ o : Fin k → Letter S Unit Γ, (List.ofFn ((Fin.consEquiv fun _ : Fin (k + 1) => Letter S Unit Γ) (z, o))) =
        z :: List.ofFn o := by
      intro o
      rw [List.ofFn_succ]
      rfl
    simp only [h2, List.map_cons, List.prod_cons, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, List.reverse_cons,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [Finset.sum_comm]

/-- The output lists of a run. -/
noncomputable def outsOf (w : List (Letter S Unit Γ)) : Outs S := fun j => w.reverse.flatMap fun z => pushOf cb z j

theorem sumL_simSem (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q') (T : ℕ) (q q' : Q) (G : Outs S → A) :
    sumL (simSem θ mu cb T (qn Q q) (qn Q q')) G = ∑ o : Fin T → Letter S Unit Γ,
      ((List.ofFn o).map mu).prod q q' * G (outsOf cb (List.ofFn o)) := by
  rw [simSem, sumL_bindL, sumL_sim mu cb hmu]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [Finset.sum_eq_single q']
  · simp only [if_true, sumL_single, List.append_nil]
    rfl
  · intro q'' _ h
    have : qn Q q'' ≠ qn Q q' := fun h' => h ((qn Q).injective h')
    simp [this]
  · simp

theorem length_pushOf (z : Letter S Unit Γ) (j : Fin (nT S + nT S)) : (pushOf cb z j).reverse = pushOf cb z j := by
  unfold pushOf
  split
  · rfl
  · split_ifs <;> rfl

theorem outsOf_eq (w : List (Letter S Unit Γ)) (j : Fin (nT S + nT S)) :
    outsOf cb w j = (w.flatMap fun z => pushOf cb z j).reverse := by
  unfold outsOf
  induction w with
  | nil => rfl
  | cons z w ih =>
    simp only [List.reverse_cons, List.flatMap_append, ih, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.reverse_append, length_pushOf]

theorem chOf_injective : Function.Injective (chOf (S := S)) := by
  rintro (⟨s, b⟩ | ⟨u⟩) (⟨s', b'⟩ | ⟨u'⟩) h
  · simp only [chOf, Prod.mk.injEq, Option.some.injEq] at h
    rw [h.1, h.2]
  · simp [chOf] at h
  · simp [chOf] at h
  · rfl

theorem flatMap_pushOf (w : List (Letter S Unit Γ)) {j : Fin (nT S + nT S)} {ch : Ch S Unit} (h : chOf ch = outOf j) :
    (w.flatMap fun z => pushOf cb z j) = (emit w ch).map (code cb) := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    rw [List.flatMap_cons, ih]
    cases z with
    | none => rfl
    | some a =>
      obtain ⟨ch', a⟩ := a
      have e1 : emit (some (ch', a) :: w) ch = if ch' = ch then a :: emit w ch else emit w ch := by
        simp only [emit, List.reduceOption_cons_of_some, proj_cons]
      rw [e1]
      by_cases hch : ch' = ch
      · subst hch
        simp [pushOf, h]
      · have : chOf ch' ≠ outOf j := fun h' => hch (chOf_injective (h'.trans h.symm))
        simp [pushOf, this, hch]

theorem flatMap_pushOf_none (w : List (Letter S Unit Γ)) {j : Fin (nT S + nT S)} (h : outOf j = ((none : Option S), false)) :
    (w.flatMap fun z => pushOf cb z j) = [] := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    rw [List.flatMap_cons, ih, List.append_nil]
    cases z with
    | none => rfl
    | some a =>
      obtain ⟨ch', a⟩ := a
      have : chOf ch' ≠ outOf j := by
        rw [h]
        cases ch' <;> simp [chOf]
      simp [pushOf, this]

/-- What a run writes and reads on a tape. -/
def wr (w : List (Letter S Unit Γ)) : Option S → List Γ
  | none => []
  | some s => emit w (.tp s false)

/-- What a run reads. -/
def rdr (w : List (Letter S Unit Γ)) : Option S → List Γ
  | none => emit w (.inp ())
  | some s => emit w (.tp s true)

theorem outsOf_left (w : List (Letter S Unit Γ)) (i : Fin (nT S)) :
    outsOf cb w (Fin.castAdd (nT S) i) = ((wr w ((tapes S).get i)).map (code cb)).reverse := by
  rw [outsOf_eq]
  congr 1
  have h : outOf (Fin.castAdd (nT S) i) = ((tapes S).get i, false) := by
    rw [outOf, Fin.addCases_left]
  generalize hs : (tapes S).get i = s at h
  cases s with
  | none => exact flatMap_pushOf_none cb w h
  | some s => exact flatMap_pushOf cb w (ch := .tp s false) h.symm

theorem outsOf_right (w : List (Letter S Unit Γ)) (i : Fin (nT S)) :
    outsOf cb w (Fin.natAdd (nT S) i) = ((rdr w ((tapes S).get i)).map (code cb)).reverse := by
  rw [outsOf_eq]
  congr 1
  have h : outOf (Fin.natAdd (nT S) i) = ((tapes S).get i, true) := by
    rw [outOf, Fin.addCases_right]
  generalize hs : (tapes S).get i = s at h
  cases s with
  | none => exact flatMap_pushOf cb w (ch := .inp ()) h.symm
  | some s => exact flatMap_pushOf cb w (ch := .tp s true) h.symm

theorem inOuts_left (u : List Γ) (i : Fin (nT S)) :
    inOuts (S := S) (u.map (code cb)).reverse (Fin.castAdd (nT S) i) =
      (((if (tapes S).get i = none then u else []) : List Γ).map (code cb)).reverse := by
  have h : outOf (Fin.castAdd (nT S) i) = ((tapes S).get i, false) := by
    rw [outOf, Fin.addCases_left]
  rw [inOuts, h]
  by_cases hs : (tapes S).get i = none
  · rw [if_pos (by rw [hs]), if_pos hs]
  · rw [if_neg (fun h' => hs (Prod.ext_iff.1 h').1), if_neg hs]
    rfl

theorem inOuts_right (u : List Γ) (i : Fin (nT S)) :
    inOuts (S := S) (u.map (code cb)).reverse (Fin.natAdd (nT S) i) = (([] : List Γ).map (code cb)).reverse := by
  have h : outOf (Fin.natAdd (nT S) i) = ((tapes S).get i, true) := by
    rw [outOf, Fin.addCases_right]
  rw [inOuts, h]
  simp

end sim

end Nc.Grp
