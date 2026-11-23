/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.RunWord

/-!
# Certificates of matched runs

A run of an automaton on tapes and inputs is certified by the states, the places of the heads and the contents
of the tapes. The certificate of a run is unique, and it exists if and only if the run is matched.
-/

set_option linter.unusedSectionVars false

namespace Nc

open Finset

section Path

variable {F : Type*} [CommRing F] {Q A : Type*} [Fintype Q] [DecidableEq Q]

/-- An entry of a product of matrices is a sum over paths. -/
theorem prod_ofFn_apply (mu : A → Matrix Q Q F) (t : ℕ) (o : Fin t → A) (i e : Q) :
    ((List.ofFn o).map mu).prod i e = ∑ q : Fin (t + 1) → Q,
      if q 0 = i ∧ q (Fin.last t) = e then ∏ τ : Fin t, mu (o τ) (q τ.castSucc) (q τ.succ) else 0 := by
  induction t generalizing i with
  | zero =>
    rw [← (Equiv.funUnique (Fin 1) Q).symm.sum_comp]
    simp only [List.ofFn_zero, List.map_nil, List.prod_nil, Matrix.one_apply, Finset.univ_eq_empty,
      Finset.prod_empty, Equiv.funUnique_symm_apply, uniqueElim_const]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  | succ t ih =>
    have hR : (∑ q : Fin (t + 1 + 1) → Q, if q 0 = i ∧ q (Fin.last (t + 1)) = e then
        ∏ τ : Fin (t + 1), mu (o τ) (q τ.castSucc) (q τ.succ) else 0) =
        ∑ q : Fin (t + 1) → Q, if q (Fin.last t) = e then
          mu (o 0) i (q 0) * ∏ τ : Fin t, mu (o τ.succ) (q τ.castSucc) (q τ.succ) else 0 := by
      rw [← (Fin.consEquiv (fun _ => Q)).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single i]
      · refine Finset.sum_congr rfl fun q _ => ?_
        simp only [Fin.consEquiv_apply, Fin.cons_zero, true_and, Fin.prod_univ_succ, Fin.castSucc_zero,
          Fin.cons_succ, ← Fin.succ_last, ← Fin.succ_castSucc]
      · intro b _ hb
        refine Finset.sum_eq_zero fun q _ => if_neg ?_
        rintro ⟨h, -⟩
        exact hb (by simpa using h)
      · intro h
        exact absurd (mem_univ _) h
    rw [List.ofFn_succ, List.map_cons, List.prod_cons, Matrix.mul_apply, hR]
    simp only [ih, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_eq_single (q 0)]
    · simp only [true_and, mul_ite, mul_zero]
    · intro b _ hb
      rw [if_neg (fun h => hb h.1.symm), mul_zero]
    · intro h
      exact absurd (mem_univ _) h

end Path

variable {Γ S Q : Type*} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
variable {n t M N : ℕ}

/-- The channels whose places start at 0. -/
def Ch.start : Ch S (Fin n) → Bool
  | .tp _ _ => true
  | .inp j => j.1 = 0

/-- The conditions on a certificate: `o` letters, `q` states, `P` places, `c` contents; `x` is the code. -/
structure Good (i e : Q) (x : Fin N × Option Γ → Bool) (o : Fin t → Letter S (Fin n) Γ) (q : Fin (t + 1) → Q)
    (P : Ch S (Fin n) → Fin (t + 1) → Fin M) (c : S → Fin M → Option Γ) : Prop where
  first : q 0 = i
  last : q (Fin.last t) = e
  zero : ∀ z, z.start = true → (P z 0).1 = 0
  step : ∀ z τ, (P z (Fin.succ τ)).1 = (P z (Fin.castSucc τ)).1 + (emit [o τ] z).length
  link : ∀ j j' : Fin n, j'.1 = j.1 + 1 → (P (.inp j') 0).1 = (P (.inp j) (Fin.last t)).1 + 1
  write : ∀ s b τ γ, o τ = some (.tp s b, γ) → c s (P (.tp s b) (Fin.castSucc τ)) = some γ
  blank : ∀ s b p, P (.tp s b) (Fin.last t) ≤ p → c s p = none
  read : ∀ j τ γ, o τ = some (.inp j, γ) → ∃ h : (P (.inp j) (Fin.castSucc τ)).1 < N, x (⟨_, h⟩, some γ) = true
  sep : ∀ j, ∃ h : (P (.inp j) (Fin.last t)).1 < N, x (⟨_, h⟩, none) = true

section Forward

variable {i e : Q} {u : Fin n → List Γ} {o : Fin t → Letter S (Fin n) Γ} {q : Fin (t + 1) → Q}
  {P : Ch S (Fin n) → Fin (t + 1) → Fin M} {c : S → Fin M → Option Γ}

theorem emit_take_succ (o : Fin t → Letter S (Fin n) Γ) (z : Ch S (Fin n)) (τ : Fin t) :
    (emit ((List.ofFn o).take (τ + 1)) z).length =
      (emit ((List.ofFn o).take τ) z).length + (emit [o τ] z).length := by
  rw [List.take_add_one, emit_appendR, List.length_append]
  simp

/-- The first place of a channel in a run. -/
def place0 (o : Fin t → Letter S (Fin n) Γ) : Ch S (Fin n) → ℕ
  | .tp _ _ => 0
  | .inp j => base (fun j => emit (List.ofFn o) (.inp j)) j

theorem Good.place {x : Fin N × Option Γ → Bool} (h : Good i e x o q P c) (z : Ch S (Fin n)) (τ : Fin (t + 1)) :
    (P z τ).1 = (P z 0).1 + (emit ((List.ofFn o).take τ) z).length := by
  induction τ using Fin.induction with
  | zero => simp
  | succ τ ih =>
    rw [h.step, ih, Fin.val_succ, emit_take_succ, Fin.val_castSucc]
    omega

theorem Good.place_last {x : Fin N × Option Γ → Bool} (h : Good i e x o q P c) (z : Ch S (Fin n)) :
    (P z (Fin.last t)).1 = (P z 0).1 + (emit (List.ofFn o) z).length := by
  rw [h.place, Fin.val_last, List.take_of_length_le (by simp)]

theorem Good.place_zero {x : Fin N × Option Γ → Bool} (h : Good i e x o q P c) (z : Ch S (Fin n)) :
    (P z 0).1 = place0 o z := by
  rcases z with ⟨s, b⟩ | j
  · exact h.zero _ rfl
  · have key : ∀ m : ℕ, ∀ j : Fin n, j.1 = m → (P (.inp j) 0).1 = place0 o (.inp j) := by
      intro m
      induction m with
      | zero =>
        intro j hj
        rw [h.zero _ (by simp [Ch.start, hj]), place0, hj, base_zero]
      | succ m ih =>
        intro j hj
        have hm : m < n := by have := j.2; omega
        have hb := base_succ (fun j => emit (List.ofFn o) (.inp j)) ⟨m, hm⟩
        rw [h.link ⟨m, hm⟩ j hj, h.place_last, ih ⟨m, hm⟩ rfl, place0, place0, hj, hb]
    exact key j j rfl

theorem Good.contents {x : Fin N × Option Γ → Bool} (h : Good i e x o q P c) (s : S) (b : Bool) (p : Fin M) :
    c s p = (emit (List.ofFn o) (.tp s b))[p.1]? := by
  by_cases hp : p.1 < (emit (List.ofFn o) (.tp s b)).length
  · obtain ⟨τ, γ, h1, h2, h3⟩ := exists_emit _ _ _ hp
    rw [List.length_ofFn] at h1
    have ho : o ⟨τ, h1⟩ = some (.tp s b, γ) := by
      simpa [List.getElem?_ofFn, h1] using h2
    have hw := h.write s b ⟨τ, h1⟩ γ ho
    have hP : P (.tp s b) (Fin.castSucc ⟨τ, h1⟩) = p := by
      apply Fin.ext
      rw [h.place, h.zero _ rfl, Fin.val_castSucc, zero_add, h3]
    rw [hP] at hw
    have := emit_getElem _ _ _ _ h2
    rw [h3] at this
    rw [hw, this]
  · rw [List.getElem?_eq_none (by omega), h.blank s b p]
    rw [Fin.le_def, h.place_last, h.zero _ rfl]
    omega

theorem Good.matched (hM : t < M) (h : Good i e (code N u) o q P c) : Matched (List.ofFn o) u := by
  constructor
  · intro s
    apply List.ext_getElem?
    intro p
    by_cases hp : p < M
    · rw [← h.contents s false ⟨p, hp⟩, ← h.contents s true ⟨p, hp⟩]
    · have h1 := emit_length_le (List.ofFn o) (.tp s false)
      have h2 := emit_length_le (List.ofFn o) (.tp s true)
      rw [List.length_ofFn] at h1 h2
      rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · have : u = fun j => emit (List.ofFn o) (.inp j) := by
      refine eq_of_read u _ fun k p hp => ?_
      rcases hp.lt_or_eq with hp | hp
      · obtain ⟨τ, γ, h1, h2, h3⟩ := exists_emit _ _ _ hp
        rw [List.length_ofFn] at h1
        have ho : o ⟨τ, h1⟩ = some (.inp k, γ) := by
          simpa [List.getElem?_ofFn, h1] using h2
        obtain ⟨hN, hx⟩ := h.read k ⟨τ, h1⟩ γ ho
        have hP : (P (.inp k) (Fin.castSucc ⟨τ, h1⟩)).1 = base (fun j => emit (List.ofFn o) (.inp j)) k + p := by
          rw [h.place, h.place_zero, Fin.val_castSucc, h3]
          rfl
        have hx' := of_decide_eq_true hx
        simp only [hP] at hx'
        have hg := emit_getElem _ _ _ _ h2
        rw [h3] at hg
        rw [hx', List.getElem?_append_left (by simpa using hp), List.getElem?_map, hg]
        rfl
      · obtain ⟨hN, hx⟩ := h.sep k
        have hP : (P (.inp k) (Fin.last t)).1 = base (fun j => emit (List.ofFn o) (.inp j)) k + p := by
          rw [h.place_last, h.place_zero, hp]
          rfl
        have hx' := of_decide_eq_true hx
        simp only [hP] at hx'
        rw [hx', hp, List.getElem?_append_right (by simp)]
        simp
    intro j
    rw [this]

end Forward

section Backward

variable {i e : Q} {u : Fin n → List Γ} {o : Fin t → Letter S (Fin n) Γ} {q : Fin (t + 1) → Q}

theorem emit_take_le (o : Fin t → Letter S (Fin n) Γ) (z : Ch S (Fin n)) (τ : ℕ) :
    (emit ((List.ofFn o).take τ) z).length ≤ (emit (List.ofFn o) z).length := by
  conv_rhs => rw [← List.take_append_drop τ (List.ofFn o), emit_appendR, List.length_append]
  omega

theorem place_lt (hM : N + t < M) (hN : (wordOf (List.ofFn u)).length ≤ N)
    (hu : ∀ j, emit (List.ofFn o) (.inp j) = u j) (z : Ch S (Fin n)) (τ : ℕ) :
    place0 o z + (emit ((List.ofFn o).take τ) z).length < M := by
  have h1 := emit_take_le o z τ
  rcases z with ⟨s, b⟩ | j
  · have h2 := emit_length_le (List.ofFn o) (.tp s b)
    rw [List.length_ofFn] at h2
    simp only [place0]
    omega
  · have h2 := base_add_lt u j
    have h3 : (fun j => emit (List.ofFn o) (.inp j)) = u := funext hu
    simp only [place0, h3]
    rw [hu] at h1
    omega

theorem exists_good (hM : N + t < M) (hN : (wordOf (List.ofFn u)).length ≤ N) (h : Matched (List.ofFn o) u)
    (hi : q 0 = i) (he : q (Fin.last t) = e) :
    ∃ (P : Ch S (Fin n) → Fin (t + 1) → Fin M) (c : S → Fin M → Option Γ), Good i e (code N u) o q P c := by
  have h3 : (fun j => emit (List.ofFn o) (.inp j)) = u := funext h.2
  refine ⟨fun z τ => ⟨_, place_lt hM hN h.2 z τ⟩, fun s p => (emit (List.ofFn o) (.tp s false))[p.1]?,
    hi, he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    rcases z with ⟨s, b⟩ | j
    · simp [place0]
    · have : j.1 = 0 := by simpa [Ch.start] using hz
      simp [place0, this]
  · intro z τ
    simp only [Fin.val_succ, Fin.val_castSucc]
    rw [emit_take_succ]
    omega
  · intro j j' hj
    simp only [Fin.val_zero, List.take_zero, emit_nil, List.length_nil, add_zero, Fin.val_last, place0, h3]
    rw [List.take_of_length_le (by simp), h.2, hj, base_succ]
  · intro s b τ γ ho
    have hL : (List.ofFn o)[τ.1]? = some (some (.tp s b, γ)) := by simp [ho]
    have := emit_getElem _ _ _ _ hL
    simp only [place0, Fin.val_castSucc, zero_add]
    cases b
    · exact this
    · rw [h.1 s]
      exact this
  · intro s b p hp
    rw [Fin.le_def] at hp
    simp only [place0, Fin.val_last, zero_add] at hp
    rw [List.take_of_length_le (by simp)] at hp
    apply List.getElem?_eq_none
    cases b
    · exact hp
    · rw [h.1 s]
      exact hp
  · intro j τ γ ho
    have hL : (List.ofFn o)[τ.1]? = some (some (.inp j, γ)) := by simp [ho]
    have hg := emit_getElem _ _ _ _ hL
    rw [h.2] at hg
    have hlt := (List.getElem?_eq_some_iff.1 hg).1
    have hb := base_add_lt u j
    simp only [place0, h3, Fin.val_castSucc]
    refine ⟨by omega, ?_⟩
    unfold code
    rw [decide_eq_true_eq, wordOf_getElem, List.getElem?_append_left (by simpa using hlt), List.getElem?_map, hg]
    rfl
  · intro j
    have hb := base_add_lt u j
    have hP : place0 o (.inp j) + (emit ((List.ofFn o).take (Fin.last t).1) (.inp j)).length =
        base u j + (u j).length := by
      simp only [place0, h3, Fin.val_last]
      rw [List.take_of_length_le (by simp), h.2]
    refine ⟨lt_of_eq_of_lt hP (by omega), ?_⟩
    unfold code
    rw [decide_eq_true_eq]
    simp only [hP]
    rw [wordOf_getElem, List.getElem?_append_right (by simp)]
    simp

end Backward

end Nc
