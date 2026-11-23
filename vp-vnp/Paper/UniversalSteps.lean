/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.Bounds

/-!
# The paper, section "Cutting computations": the universal automaton is exact
-/

set_option linter.unusedSectionVars false

namespace Paper

open Finset NS1 Nc Nc.Uni

section General

variable {A : Type} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K] {P : Mach A M K}

/-- **Paper: proof of Proposition prop:universal, the automaton is exact.** "So accepting runs correspond to matched
sequences of length t, provided that these are long enough": the value of the automaton's program is the sum of the
weights of the accepting runs of the machine. -/
theorem prop_universal_automaton {S₀ : Series A (Zc K × Sy M K)} (h : IsRuns S₀ (emX P) fun x => (x.2.2.1.map fun s => P.wt s.1).prod)
    {bits : List Bool} (hc : Mach.Closed (σi P bits)) (R : Finset (List P.Step))
    (hR : ∀ tr, tr ∈ R ↔ Mach.GV (σi P bits) tr) {Tm : ℕ} (hTm : ∀ tr ∈ R, tr.length ≤ Tm) :
    Bdd (tU (Fintype.card (Bl K)) Tm (Nat.size (Tm + 1))) S₀ (fun _ => bits.map .bit) ∧
      val (tU (Fintype.card (Bl K)) Tm (Nat.size (Tm + 1))) S₀ (fun _ => bits.map .bit) = ∑ tr ∈ R, Mach.wts tr := by
  classical
  have hle : ∀ x : XP P, Mt (emX P) (fun _ => bits.map .bit) x →
      ∑ s, (emX P x (.tp s true)).length ≤ tU (Fintype.card (Bl K)) Tm (Nat.size (Tm + 1)) := by
    intro x hx
    rw [mt_X] at hx
    have h1 : x.2.2.1.length ≤ Tm := by
      have := hTm _ ((hR _).2 hx.gv)
      simpa using this
    rw [hx.total]
    refine tU_mono h1 ?_
    rw [← hx.size_eq]
    exact Nat.size_le_size (by omega)
  refine ⟨h.bdd hle, ?_⟩
  have hex : ∀ tr, ∃ x : XP P, tr ∈ R → MX x bits ∧ x.2.2.1.map nst = tr := by
    intro tr
    by_cases htr : tr ∈ R
    · have hgv := (hR tr).1 htr
      have hseq := (Mach.gv_iff hc tr).1 hgv
      have hb := hseq.le hc
      obtain ⟨x, hx⟩ := exists_MX hgv (by
        intro st hst i
        have := hb st hst i
        simpa [σi] using this)
      exact ⟨x, fun _ => hx⟩
    · exact ⟨([], [], [], ([], []), [], ([], [], ([], [], (false, [])))), fun h => absurd h htr⟩
  choose f hf using hex
  have hinj : ∀ tr ∈ R, ∀ tr' ∈ R, f tr = f tr' → tr = tr' := by
    intro tr htr tr' htr' e
    rw [← (hf tr htr).2, ← (hf tr' htr').2, e]
  rw [h.val_eq _ _ (R.image f), Finset.sum_image hinj]
  · refine Finset.sum_congr rfl fun tr htr => ?_
    have e := (hf tr htr).2
    rw [Mach.wts]
    conv_rhs => rw [← e]
    rw [List.map_map]
    rfl
  · intro x
    rw [Finset.mem_image]
    constructor
    · rintro ⟨tr, htr, rfl⟩
      have hx := (mt_X (f tr) bits).2 (hf tr htr).1
      exact ⟨hx, hle _ hx⟩
    · rintro ⟨hx, -⟩
      have hx' := (mt_X x bits).1 hx
      have htr : x.2.2.1.map nst ∈ R := (hR _).2 hx'.gv
      exact ⟨_, htr, MX.unique (hf _ htr).1 hx' (hf _ htr).2⟩

end General

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- **Paper: proof of Proposition prop:universal, the pointer machine is exact.** "So an accepting run of cost c gives
exactly one accepting run of the machine with the same weight, of at most O(|z|+c) steps, and there are no others", as
used: the accepting runs of the machine form a finite set, their weights sum to pv(z), and they have O(|z|+τ) steps. -/
theorem prop_universal_machine (hθ : ∀ q, q ∉ supp → θ q = 0) {τ : ℕ} {z : Tree} (h : Plain θ τ z) :
    ∃ R : Finset (List (UM θ supp).Step), (∀ tr, tr ∈ R ↔ Mach.GV (σ0 supp z) tr) ∧
      ∑ tr ∈ R, Mach.wts tr = pv θ z ∧ ∀ tr ∈ R, (tr.length : ℤ) ≤ 3 * z.size + Cc supp * τ + 10 := by
  obtain ⟨R, h1, h2, h3⟩ := sum_machine (supp := supp) hθ h
  refine ⟨R, fun tr => ?_, h2, h3⟩
  rw [h1, Mach.gv_iff (closed_σ0 z)]

variable (θ supp) in
/-- **Paper: proof of Proposition prop:universal, exactness and time.** The series of the automaton has the value pv(z) in
O((|z|+τ) lg(|z|+τ)²) letters. -/
theorem prop_universal_series (hθ : ∀ q, q ∉ supp → θ q = 0) :
    ∃ S₀ : Series A (Ch (Tp Kd) Unit × Sy (Md (Nm supp)) Kd), RatLe (dimX (UM θ supp)) S₀ ∧
      ∃ C : ℕ, ∀ (τ : ℕ) (z : Tree), Plain θ τ z →
        Bdd (C * ((z.size + τ + 2) * lg (z.size + τ + 2) ^ 2)) S₀ (fun _ => (word z).map .bit) ∧
        Nc.val (C * ((z.size + τ + 2) * lg (z.size + τ + 2) ^ 2)) S₀ (fun _ => (word z).map .bit) = pv θ z := by
  obtain ⟨S₀, h1, h2⟩ := runs_X (UM θ supp)
  let c := 41 + 2 * Lm supp
  let d := Nat.size c + 2
  refine ⟨S₀, h1, (50 + Fintype.card (Bl Kd)) * (c * d ^ 2), fun τ z hz => ?_⟩
  obtain ⟨R, r1, r2, r3⟩ := prop_universal_machine (supp := supp) hθ hz
  have hT : ∀ tr ∈ R, tr.length ≤ stepsU supp τ z.size := by
    intro tr htr
    have h3 := r3 tr htr
    have : (3 * z.size + Cc supp * τ + 10 : ℤ) = ((stepsU supp τ z.size : ℕ) : ℤ) := by
      unfold stepsU Cc
      push_cast
      ring
    rw [this] at h3
    exact_mod_cast h3
  obtain ⟨a1, a2⟩ := prop_universal_automaton h2 (closed_σ0 z) R r1 hT
  replace a2 := a2.trans r2
  set N := z.size + τ + 2 with hN
  have hT : stepsU supp τ z.size + 1 ≤ c * N := by
    have hs := Tree.size_pos z
    simp only [stepsU, c, hN]
    nlinarith [Nat.zero_le (Lm supp * z.size), Nat.zero_le (Lm supp)]
  have hlg : 1 ≤ lg N := Nat.le_add_left 1 _
  have hL : Nat.size (stepsU supp τ z.size + 1) + 1 ≤ d * lg N := by
    have h3 : Nat.size (stepsU supp τ z.size + 1) ≤ Nat.size c + lg N :=
      (Nat.size_le_size hT).trans ((size_mul_le c N).trans (Nat.add_le_add_left (size_le_lg N) _))
    have h4 : Nat.size c ≤ Nat.size c * lg N := Nat.le_mul_of_pos_right _ hlg
    simp only [d]
    nlinarith
  have ht : tU (Fintype.card (Bl Kd)) (stepsU supp τ z.size) (Nat.size (stepsU supp τ z.size + 1)) ≤
      (50 + Fintype.card (Bl Kd)) * (c * d ^ 2) * (N * lg N ^ 2) := by
    refine (tU_le _ _ _).trans ?_
    calc (50 + Fintype.card (Bl Kd)) * ((stepsU supp τ z.size + 1) * (Nat.size (stepsU supp τ z.size + 1) + 1) ^ 2)
        ≤ (50 + Fintype.card (Bl Kd)) * (c * N * (d * lg N) ^ 2) := by gcongr
      _ = _ := by ring
  exact ⟨fun W hW => (a1 W hW).trans ht, by rw [val_eq_of_bdd a1 ht, a2]⟩

end Paper
