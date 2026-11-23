/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.RunGood
import Nc.FinDom

/-!
# The value of an automaton is a sum over finite domains
-/

set_option linter.unusedSectionVars false

namespace Nc

open Finset

variable {F : Type*} [Field F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]
variable {n t M N : ℕ}

/-- The hidden variables: letters, states, places, contents. -/
abbrev RD (S : Type) (n t M : ℕ) : Type := Fin t ⊕ Fin (t + 1) ⊕ (Ch S (Fin n) × Fin (t + 1)) ⊕ (S × Fin M)

instance : DecidableEq (RD S n t M) :=
  haveI : DecidableEq ((Ch S (Fin n) × Fin (t + 1)) ⊕ (S × Fin M)) := inferInstance
  haveI : DecidableEq (Fin (t + 1) ⊕ (Ch S (Fin n) × Fin (t + 1)) ⊕ (S × Fin M)) := instDecidableEqSum
  instDecidableEqSum

/-- Their domains. -/
@[reducible] def RE (Γ S Q : Type) (n t M : ℕ) : RD S n t M → Type
  | .inl _ => Letter S (Fin n) Γ
  | .inr (.inl _) => Q
  | .inr (.inr (.inl _)) => Fin M
  | .inr (.inr (.inr _)) => Option Γ

instance : ∀ d : RD S n t M, Fintype (RE Γ S Q n t M d)
  | .inl _ => inferInstanceAs (Fintype (Letter S (Fin n) Γ))
  | .inr (.inl _) => inferInstanceAs (Fintype Q)
  | .inr (.inr (.inl _)) => inferInstanceAs (Fintype (Fin M))
  | .inr (.inr (.inr _)) => inferInstanceAs (Fintype (Option Γ))

instance : ∀ d : RD S n t M, DecidableEq (RE Γ S Q n t M d)
  | .inl _ => inferInstanceAs (DecidableEq (Letter S (Fin n) Γ))
  | .inr (.inl _) => inferInstanceAs (DecidableEq Q)
  | .inr (.inr (.inl _)) => inferInstanceAs (DecidableEq (Fin M))
  | .inr (.inr (.inr _)) => inferInstanceAs (DecidableEq (Option Γ))

/-- The bits: the code and the hidden bits. -/
abbrev RV (Γ S Q : Type) (n t M N : ℕ) : Type := (Fin N × Option Γ) ⊕ Σ d, RE Γ S Q n t M d

/-- The bit "the letter at step `τ` is `a`". -/
def vEm (τ : Fin t) (a : Letter S (Fin n) Γ) : RV Γ S Q n t M N := .inr ⟨.inl τ, a⟩
/-- The bit "the state before step `τ` is `q`". -/
def vSt (τ : Fin (t + 1)) (q : Q) : RV Γ S Q n t M N := .inr ⟨.inr (.inl τ), q⟩
/-- The bit "the place of `z` before step `τ` is `m`". -/
def vPl (z : Ch S (Fin n)) (τ : Fin (t + 1)) (m : Fin M) : RV Γ S Q n t M N := .inr ⟨.inr (.inr (.inl (z, τ))), m⟩
/-- The bit "tape `s` holds `x` at place `p`". -/
def vCt (s : S) (p : Fin M) (x : Option Γ) : RV Γ S Q n t M N := .inr ⟨.inr (.inr (.inr (s, p))), x⟩

/-- The rules that carry weights. -/
abbrev RS (Γ S Q : Type) (n t : ℕ) : Type := Fin t × Letter S (Fin n) Γ × Q × Q

/-- The rules that forbid. -/
abbrev RH (Γ S : Type) (n t M : ℕ) : Type :=
  Bool ⊕ Ch S (Fin n) ⊕ (Ch S (Fin n) × Fin t × Fin M × Letter S (Fin n) Γ) ⊕ (Fin n × Fin n × Fin M) ⊕
    (S × Bool × Fin t × Γ × Fin M) ⊕ (S × Bool × Fin M × Fin M) ⊕ (Fin n × Fin t × Γ × Fin M) ⊕ (Fin n × Fin M)

/-- The literals of a rule with a weight. -/
def sLits : RS Γ S Q n t → List (RV Γ S Q n t M N × Bool)
  | (τ, a, q, q') => [(vEm τ a, true), (vSt τ.castSucc q, true), (vSt τ.succ q', true)]

/-- The literals of a rule that forbids. -/
def hLits (i e : Q) : RH Γ S n t M → List (RV Γ S Q n t M N × Bool)
  | .inl false => [(vSt 0 i, false)]
  | .inl true => [(vSt (Fin.last t) e, false)]
  | .inr (.inl z) => if h : 0 < M then [(vPl z 0 ⟨0, h⟩, false)] else []
  | .inr (.inr (.inl (z, τ, m, a))) => (vPl z τ.castSucc m, true) :: (vEm τ a, true) ::
      if h : m.1 + (emit [a] z).length < M then [(vPl z τ.succ ⟨_, h⟩, false)] else []
  | .inr (.inr (.inr (.inl (j, j', m)))) => (vPl (.inp j) (Fin.last t) m, true) ::
      if h : m.1 + 1 < M then [(vPl (.inp j') 0 ⟨_, h⟩, false)] else []
  | .inr (.inr (.inr (.inr (.inl (s, b, τ, γ, m))))) =>
      [(vEm τ (some (.tp s b, γ)), true), (vPl (.tp s b) τ.castSucc m, true), (vCt s m (some γ), false)]
  | .inr (.inr (.inr (.inr (.inr (.inl (s, b, m, p)))))) =>
      [(vPl (.tp s b) (Fin.last t) m, true), (vCt s p none, false)]
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl (j, τ, γ, m))))))) =>
      (vEm τ (some (.inp j, γ)), true) :: (vPl (.inp j) τ.castSucc m, true) ::
        if h : m.1 < N then [(.inl (⟨_, h⟩, some γ), false)] else []
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (j, m))))))) => (vPl (.inp j) (Fin.last t) m, true) ::
      if h : m.1 < N then [(.inl (⟨_, h⟩, none), false)] else []

/-- The rules that are in force. -/
def active : RH Γ S n t M → Bool
  | .inr (.inl z) => z.start
  | .inr (.inr (.inr (.inl (j, j', _)))) => j'.1 = j.1 + 1
  | .inr (.inr (.inr (.inr (.inr (.inl (_, _, m, p)))))) => m ≤ p
  | _ => true

section Hard

variable (i e : Q) (x : Fin N × Option Γ → Bool) (g : ∀ d, RE Γ S Q n t M d)

/-- The letters. -/
def gEm (τ : Fin t) : Letter S (Fin n) Γ := g (.inl τ)
/-- The states. -/
def gSt (τ : Fin (t + 1)) : Q := g (.inr (.inl τ))
/-- The places. -/
def gPl (z : Ch S (Fin n)) (τ : Fin (t + 1)) : Fin M := g (.inr (.inr (.inl (z, τ))))
/-- The contents. -/
def gCt (s : S) (p : Fin M) : Option Γ := g (.inr (.inr (.inr (s, p))))

@[simp] theorem elim_vEm (τ : Fin t) (a : Letter S (Fin n) Γ) :
    Sum.elim x (hot g) (vEm τ a) = decide (gEm g τ = a) := rfl
@[simp] theorem elim_vSt (τ : Fin (t + 1)) (q : Q) :
    Sum.elim x (hot g) (vSt τ q) = decide (gSt g τ = q) := rfl
@[simp] theorem elim_vPl (z : Ch S (Fin n)) (τ : Fin (t + 1)) (m : Fin M) :
    Sum.elim x (hot g) (vPl z τ m) = decide (gPl g z τ = m) := rfl
@[simp] theorem elim_vCt (s : S) (p : Fin M) (y : Option Γ) :
    Sum.elim x (hot g) (vCt s p y) = decide (gCt g s p = y) := rfl

/-- No rule in force is violated. -/
def Hard : Prop := ∀ r : RH Γ S n t M, active r = true → ¬ ∀ l ∈ hLits i e r, Sum.elim x (hot g) l.1 = l.2

theorem good_of_hard (h : Hard i e x g) : Good i e x (gEm g) (gSt g) (gPl g) (gCt g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hLits, active] using h (.inl false)
  · simpa [hLits, active] using h (.inl true)
  · intro z hz
    have hM : 0 < M := (Nat.zero_le _).trans_lt (gPl g z 0).2
    have := h (.inr (.inl z)) hz
    simp [hLits, hM] at this
    rw [this]
  · intro z τ
    have := h (.inr (.inr (.inl (z, τ, gPl g z τ.castSucc, gEm g τ)))) rfl
    by_cases hM : (gPl g z τ.castSucc).1 + (emit [gEm g τ] z).length < M
    · simp [hLits, hM] at this
      rw [this]
    · simp [hLits, hM] at this
  · intro j j' hj
    have := h (.inr (.inr (.inr (.inl (j, j', gPl g (.inp j) (Fin.last t)))))) (by simp [active, hj])
    by_cases hM : (gPl g (.inp j) (Fin.last t)).1 + 1 < M
    · simp [hLits, hM] at this
      rw [this]
    · simp [hLits, hM] at this
  · intro s b τ γ ho
    have := h (.inr (.inr (.inr (.inr (.inl (s, b, τ, γ, gPl g (.tp s b) τ.castSucc)))))) rfl
    simpa [hLits, ho] using this
  · intro s b p hp
    have := h (.inr (.inr (.inr (.inr (.inr (.inl (s, b, gPl g (.tp s b) (Fin.last t), p)))))))
      (by simpa [active] using hp)
    simpa [hLits] using this
  · intro j τ γ ho
    have := h (.inr (.inr (.inr (.inr (.inr (.inr (.inl (j, τ, γ, gPl g (.inp j) τ.castSucc)))))))) rfl
    by_cases hN : (gPl g (.inp j) τ.castSucc).1 < N
    · refine ⟨hN, ?_⟩
      simpa [hLits, ho, hN] using this
    · simp [hLits, ho, hN] at this
  · intro j
    have := h (.inr (.inr (.inr (.inr (.inr (.inr (.inr (j, gPl g (.inp j) (Fin.last t))))))))) rfl
    by_cases hN : (gPl g (.inp j) (Fin.last t)).1 < N
    · refine ⟨hN, ?_⟩
      simpa [hLits, hN] using this
    · simp [hLits, hN] at this

theorem hard_of_good (h : Good i e x (gEm g) (gSt g) (gPl g) (gCt g)) : Hard i e x g := by
  rintro ((_ | _) | z | ⟨z, τ, m, a⟩ | ⟨j, j', m⟩ | ⟨s, b, τ, γ, m⟩ | ⟨s, b, m, p⟩ | ⟨j, τ, γ, m⟩ | ⟨j, m⟩) hr hl
  · simp [hLits, h.first] at hl
  · simp [hLits, h.last] at hl
  · have hM : 0 < M := (Nat.zero_le _).trans_lt (gPl g z 0).2
    simp [hLits, hM] at hl
    exact hl (Fin.ext (h.zero z hr))
  · simp only [hLits, List.forall_mem_cons, elim_vPl, elim_vEm, decide_eq_true_eq] at hl
    obtain ⟨rfl, rfl, hl⟩ := hl
    have hs := h.step z τ
    have hM := (gPl g z τ.succ).2
    rw [hs] at hM
    rw [dif_pos hM] at hl
    simp at hl
    exact hl (Fin.ext hs)
  · simp only [hLits, List.forall_mem_cons, elim_vPl, decide_eq_true_eq] at hl
    obtain ⟨rfl, hl⟩ := hl
    have hs := h.link j j' (by simpa [active] using hr)
    have hM := (gPl g (.inp j') 0).2
    rw [hs] at hM
    rw [dif_pos hM] at hl
    simp at hl
    exact hl (Fin.ext hs)
  · simp only [hLits, List.forall_mem_cons, elim_vPl, elim_vEm, elim_vCt, decide_eq_true_eq,
      decide_eq_false_iff_not] at hl
    obtain ⟨ho, rfl, hl, -⟩ := hl
    exact hl (h.write s b τ γ ho)
  · simp only [hLits, List.forall_mem_cons, elim_vPl, elim_vCt, decide_eq_true_eq,
      decide_eq_false_iff_not] at hl
    obtain ⟨rfl, hl, -⟩ := hl
    exact hl (h.blank s b p (by simpa [active] using hr))
  · simp only [hLits, List.forall_mem_cons, elim_vPl, elim_vEm, decide_eq_true_eq] at hl
    obtain ⟨ho, rfl, hl⟩ := hl
    obtain ⟨hN, hx⟩ := h.read j τ γ ho
    rw [dif_pos hN] at hl
    simp [hx] at hl
  · simp only [hLits, List.forall_mem_cons, elim_vPl, decide_eq_true_eq] at hl
    obtain ⟨rfl, hl⟩ := hl
    obtain ⟨hN, hx⟩ := h.sep j
    rw [dif_pos hN] at hl
    simp [hx] at hl

end Hard

/-- The literals of all rules. -/
def rLits (i e : Q) : RS Γ S Q n t ⊕ RH Γ S n t M → List (RV Γ S Q n t M N × Bool) := Sum.elim sLits (hLits i e)

/-- The weights of all rules. -/
def rWt (mu : Letter S (Fin n) Γ → Matrix Q Q F) : RS Γ S Q n t ⊕ RH Γ S n t M → F :=
  Sum.elim (fun r => mu r.2.1 r.2.2.1 r.2.2.2) fun r => if active r then 0 else 1

theorem prod_soft (mu : Letter S (Fin n) Γ → Matrix Q Q F) (x : Fin N × Option Γ → Bool)
    (g : ∀ d, RE Γ S Q n t M d) :
    (∏ r : RS Γ S Q n t, if ∀ l ∈ sLits (M := M) (N := N) r, Sum.elim x (hot g) l.1 = l.2 then
      mu r.2.1 r.2.2.1 r.2.2.2 else 1) = ∏ τ, mu (gEm g τ) (gSt g (Fin.castSucc τ)) (gSt g (Fin.succ τ)) := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Finset.prod_eq_single (gEm g τ, gSt g (Fin.castSucc τ), gSt g (Fin.succ τ))]
  · rw [if_pos]
    simp [sLits]
  · rintro ⟨a, q, q'⟩ _ hne
    refine if_neg fun h => hne ?_
    simp only [sLits, List.forall_mem_cons, elim_vEm, elim_vSt, decide_eq_true_eq] at h
    rw [h.1, h.2.1, h.2.2.1]
  · intro h
    exact absurd (mem_univ _) h

open scoped Classical in
theorem prod_hard (i e : Q) (x : Fin N × Option Γ → Bool) (g : ∀ d, RE Γ S Q n t M d) :
    (∏ r : RH Γ S n t M, if ∀ l ∈ hLits i e r, Sum.elim x (hot g) l.1 = l.2 then
      (if active r then (0 : F) else 1) else 1) =
        if Good i e x (gEm g) (gSt g) (gPl g) (gCt g) then 1 else 0 := by
  split_ifs with hg
  · have hh := hard_of_good i e x g hg
    refine Finset.prod_eq_one fun r _ => ?_
    by_cases hr : active r = true
    · rw [if_neg (hh r hr)]
    · simp [hr]
  · have hh : ¬ Hard i e x g := fun h => hg (good_of_hard i e x g h)
    unfold Hard at hh
    push Not at hh
    obtain ⟨r, hr, hl⟩ := hh
    refine Finset.prod_eq_zero (mem_univ r) ?_
    rw [if_pos hl, if_pos hr]

end Nc
