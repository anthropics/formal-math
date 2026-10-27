/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Interfaces
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7) from the interface statements

`no_linear_circuits`: the language `L0` is not decided by circuits of linear size. Suppose it is,
with the constant c₀. Take the machine N of the algorithm for c₀, its table e, and a chain a of e
that starts beyond all thresholds. Along the chain,
«`Phi m` is satisfiable» passes from each number to the next and back, because `Phi m` says that N
accepts the next number, and N accepts a number if and only if its formula is satisfiable. At the
last place the formula says the opposite of the
formula at the first place: a contradiction. -/

public section

namespace CircuitLowerBound

open ENP Groundwork Turing

theorem Acc.mono {N : TM2ComputableAux Bool Bool} {P T T' : ℕ} (h : Acc N P T) (hT : T ≤ T') : Acc N P T' := by
  obtain ⟨y, ⟨h⟩⟩ := h
  exact ⟨y, ⟨⟨h.toEvalsTo, h.steps_le_m.trans hT⟩⟩⟩

theorem sat_nil : Sat [] := ⟨fun _ => false, by simp⟩

theorem not_sat_nil_clause : ¬Sat [[]] := by
  rintro ⟨a, h⟩
  obtain ⟨l, hl, -⟩ := h [] (by simp)
  simp at hl

/-- The variables of `Phi m` have m bits. -/
theorem phi_vars (hV : StVars) (m : ℕ) : ∀ D ∈ Phi m, ∀ l ∈ D, l.1 < 2 ^ m := by
  intro D hD l hl
  unfold Phi at hD
  split_ifs at hD with h1 h2 h3 h4
  · exact hV _ _ _ h2 D hD l hl
  · simp at hD
  · simp only [List.mem_singleton] at hD; subst hD; simp at hl
  · simp at hD
  · simp at hD

/-- A circuit that decides the language on the words of length m computes a satisfying assignment of
`Phi m`, if there is one. -/
theorem sat_by_circuit (hG : StGreedy) (hV : StVars) {m : ℕ} {C : Circuit} (hC : ∀ x : List Bool, x.length = m → (eval C x = true ↔ L0 x))
    (hs : Sat (Phi m)) : ∀ D ∈ Phi m, ∃ l ∈ D, eval C (toWord m l.1) = l.2 := by
  intro D hD
  obtain ⟨l, hl, hval⟩ := hG (Phi m) (2 ^ m) (phi_vars hV m) hs D hD
  refine ⟨l, hl, ?_⟩
  have h1 := hC (toWord m l.1) (length_toWord _ _)
  unfold L0 at h1
  rw [length_toWord, ofWord_toWord (phi_vars hV m D hD l hl), hval] at h1
  cases h2 : l.2 <;> cases h3 : eval C (toWord m l.1) <;> simp_all

theorem lin_le_two_pow : ∀ x : ℕ, 8 ≤ x → 24 * x + 26 ≤ 2 ^ x := by
  intro x hx
  induction x, hx using Nat.le_induction with
  | base => norm_num
  | succ x hx ih => rw [pow_succ]; omega

/-- Room, and time, for a number L of a chain and a parameter P ≤ 3L. -/
theorem room {e : MCode} {L P : ℕ} (hL : 4 * (kb e + lam e) + 64 ≤ L) (hP : P ≤ 3 * L) : Fits e L P ∧ P / 8 ≤ bt e L := by
  have hb : 3 * L / 8 ≤ bt e L := by unfold bt; omega
  refine ⟨⟨by omega, ?_⟩, by omega⟩
  have h1 := lin_le_two_pow (L / 8) (by omega)
  have h2 : 2 ^ (L / 8) ≤ 2 ^ bt e L := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The language is not decided by circuits of linear size. -/
theorem no_linear_circuits (hTab : StTab) (hCode : StCode) (hChain : StChain) (hV : StVars) (hG : StGreedy) (hAlg : StAlg) : ¬HasLinearCircuits L0 := by
  rintro ⟨c₀, hc⟩
  obtain ⟨N, hfin, hsound, hcomp⟩ := hAlg c₀
  obtain ⟨e, he⟩ := hTab N hfin
  obtain ⟨m₀, hm₀⟩ := hcomp e
  obtain ⟨a, ha, hae⟩ := hCode e (m₀ + (4 * (kb e + lam e) + 64))
  have h2a : a < 2 ^ a := Nat.lt_two_pow_self
  obtain ⟨p, hp⟩ : ∃ p : ℕ → ℕ, ∀ s, p s = 2 ^ a * (2 * s + 1) := ⟨_, fun _ => rfl⟩
  have hnu : ∀ s, nu (p s) = a := fun s => by rw [hp]; exact (hChain a s).1
  have hpos : ∀ s, pos (p s) = s := fun s => by rw [hp]; exact (hChain a s).2
  have hnext : ∀ s, next (p s) = p (s + 1) := fun s => by rw [next, hnu, hp, hp, pow_succ]; ring
  have hbig : ∀ s, 2 ^ a ≤ p s := fun s => by rw [hp]; exact Nat.le_mul_of_pos_right _ (by omega)
  have h3 : ∀ s, p (s + 1) ≤ 3 * p s := fun s => by
    rw [hp, hp]
    have : 0 < 2 ^ a := by positivity
    nlinarith
  -- the machine accepts a number of the chain if and only if its formula is satisfiable
  have hacc : ∀ s, s ≤ top a → Sat (Phi (p s)) → Acc N (p s) (2 ^ (p s / 8)) := by
    intro s hs hsat
    obtain ⟨C, hlen, hC⟩ := hc (p s)
    exact hm₀ (p s) (by have := hbig s; omega) (by rw [hnu, hae]) (by rw [hnu, hpos]; exact hs) C hlen (sat_by_circuit hG hV hC hsat)
  -- one link of the chain
  have hlink : ∀ s, s < top a → (Sat (Phi (p s)) ↔ Sat (Phi (p (s + 1)))) := by
    intro s hs
    obtain ⟨hfit, htime⟩ := room (e := e) (L := p s) (P := p (s + 1)) (by have := hbig s; omega) (h3 s)
    have hPhi : Phi (p s) = tabF e (p s) (p (s + 1)) := by
      unfold Phi
      rw [hnu, hpos, hnext, hae, if_pos hs, if_pos hfit]
    rw [hPhi, he _ _ hfit]
    exact ⟨fun h => hsound _ _ h, fun h => (hacc (s + 1) hs h).mono (Nat.pow_le_pow_right (by norm_num) htime)⟩
  have hall : ∀ s, s ≤ top a → (Sat (Phi (p 0)) ↔ Sat (Phi (p s))) := by
    intro s
    induction s with
    | zero => intro _; exact Iff.rfl
    | succ s ih => intro hs; exact (ih (by omega)).trans (hlink s hs)
  -- the two ends
  have hp0 : p 0 = 2 ^ a := by rw [hp]; ring
  obtain ⟨hfit, htime⟩ := room (e := e) (L := 2 ^ a) (P := 2 ^ a) (by omega) (by omega)
  have hfirst : Sat (Phi (p 0)) ↔ Sat (tabF e (2 ^ a) (2 ^ a)) := by
    rw [he _ _ hfit]
    constructor
    · intro h
      have := hacc 0 (Nat.zero_le _) h
      rw [hp0] at this
      exact this.mono (Nat.pow_le_pow_right (by norm_num) htime)
    · intro h
      rw [hp0]
      exact hsound _ _ h
  have hlast : Sat (Phi (p (top a))) ↔ ¬Sat (tabF e (2 ^ a) (2 ^ a)) := by
    unfold Phi
    rw [hnu, hpos, hae, if_neg (lt_irrefl _), if_pos rfl]
    by_cases h : Sat (tabF e (2 ^ a) (2 ^ a))
    · rw [if_pos ⟨hfit, h⟩]
      exact ⟨fun h' => absurd h' not_sat_nil_clause, fun h' => absurd h h'⟩
    · rw [if_neg fun h' => h h'.2]
      exact ⟨fun _ => h, fun _ => sat_nil⟩
  have := (hall (top a) le_rfl).trans hlast
  rw [hfirst] at this
  exact (iff_not_self this)

/-- The circuit lower bound for E^NP (Section 7), with the second form of E^NP, from the interface
statements. -/
theorem corCircuits'_of (hTab : StTab) (hCode : StCode) (hChain : StChain) (hV : StVars) (hG : StGreedy) (hAlg : StAlg) (hE : StENP') : CorCircuits' :=
  ⟨L0, hE, no_linear_circuits hTab hCode hChain hV hG hAlg⟩

/-- The circuit lower bound for E^NP (Section 7), from the interface statements. -/
theorem corCircuits_of (hTab : StTab) (hCode : StCode) (hChain : StChain) (hV : StVars) (hG : StGreedy) (hAlg : StAlg) (hE : StENP) : CorCircuits :=
  ⟨L0, hE, no_linear_circuits hTab hCode hChain hV hG hAlg⟩

end CircuitLowerBound
