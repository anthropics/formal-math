/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Sat3Graph.Defs
import SplitSat.Simulate
import GraphProblems.Read
import ToTuring.Machine.EndTM
import Mathlib.Tactic

/-! # From steps of a step machine to steps of a Turing machine, for the deciders on graphs used for the decision problems of Corollary 7 («In particular, they decide …»)

No sentence of the paper stands behind this file; the paper counts operations.
* `decidesGraph_mono`, `decidesColor_mono`: a bound in steps stays true when δ and c are made
  larger.
* `outputs_of_simulates`: let the Turing machine M simulate the machine Ms, cut into steps, with
  polynomial overhead (`SplitSat.Simulates`). If Ms, started on a word x of length at most 2·(n+2)²,
  ends with a bit b within c·2^{(δ/2)n} steps on states of size at most c·(n+2)^c, then M, started
  on x, halts with b within ⌊C·2^{δn}⌋ steps: the overhead is a polynomial in n, which is at most a
  constant times 2^{(δ/2)n}. The computation is that of `SplitSat.decidesTM_of_simulates`.
* `hostedFor_of`, `hostedColor_of`: so a decider with polynomial-time steps and the exponent δ/2 is
  hosted by a Turing machine with the exponent δ. -/

public section

namespace Sat3Graph

open Groundwork Groundwork.Prog GraphProblems Paper SplitSat

/-- The machine Ms, cut into steps, says on the code of a graph G on n vertices whether G can be
colored with k colors, within c·2^{δn} steps, on states of size at most c·(n+2)^c. (The body of
`StColoring`.) -/
@[expose] def DecidesColor (Ms : StepMachine (List Bool) Bool) (k : ℕ) (δ : ℝ) (c : ℕ) : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
  ∃ (T : ℕ) (b : Bool), Ms.Runs (code G) T (c * (n + 2) ^ c) b ∧ (b = true ↔ G.Colorable k) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n)

/-- c·(n+2)^c grows with c. -/
theorem size_mono {c c' : ℕ} (hc : c ≤ c') (n : ℕ) : c * (n + 2) ^ c ≤ c' * (n + 2) ^ c' :=
  Nat.mul_le_mul hc (Nat.pow_le_pow_right (by omega) hc)

/-- c·2^{δn} grows with c and δ. -/
theorem time_mono {c c' : ℕ} {δ δ' : ℝ} (hδ : δ ≤ δ') (hc : c ≤ c') (n : ℕ) : (c : ℝ) * (2 : ℝ) ^ (δ * n) ≤ c' * (2 : ℝ) ^ (δ' * n) := by
  have h1 : (c : ℝ) ≤ c' := by exact_mod_cast hc
  have h2 : (2 : ℝ) ^ (δ * n) ≤ (2 : ℝ) ^ (δ' * n) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg n))
  exact mul_le_mul h1 h2 (by positivity) (Nat.cast_nonneg _)

/-- `DecidesGraph Ms p δ c` stays true when δ and c are made larger. -/
theorem decidesGraph_mono {Ms : StepMachine (List Bool) Bool} {p : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → Prop} {δ δ' : ℝ} {c c' : ℕ}
    (hδ : δ ≤ δ') (hc : c ≤ c') (h : DecidesGraph Ms p δ c) : DecidesGraph Ms p δ' c' := by
  intro n G s hs
  obtain ⟨T, b, r, hb, hT⟩ := h n G s hs
  exact ⟨T, b, r.mono le_rfl (size_mono hc n), hb, hT.trans (time_mono hδ hc n)⟩

/-- `DecidesColor Ms k δ c` stays true when δ and c are made larger. -/
theorem decidesColor_mono {Ms : StepMachine (List Bool) Bool} {k : ℕ} {δ δ' : ℝ} {c c' : ℕ}
    (hδ : δ ≤ δ') (hc : c ≤ c') (h : DecidesColor Ms k δ c) : DecidesColor Ms k δ' c' := by
  intro n G
  obtain ⟨T, b, r, hb, hT⟩ := h n G
  exact ⟨T, b, r.mono le_rfl (size_mono hc n), hb, hT.trans (time_mono hδ hc n)⟩

/-- Let M simulate Ms with polynomial overhead. There is C such that: whenever Ms, started on a word
x of length at most 2·(n+2)², ends with the bit b within T ≤ c·2^{(δ/2)n} steps on states of size at
most c·(n+2)^c, then M, started on x, halts with b within ⌊C·2^{δn}⌋ steps. -/
theorem outputs_of_simulates {M : Turing.TM2ComputableAux Bool Bool} {Ms : StepMachine (List Bool) Bool} {q : ℕ} (hs : Simulates M Ms q)
    {δ : ℝ} (hδ : 0 < δ) (c : ℕ) : ∃ C : ℕ, ∀ (n : ℕ) (x : List Bool) (b : Bool) (T : ℕ), x.length ≤ 2 * (n + 2) ^ 2 →
      Ms.Runs x T (c * (n + 2) ^ c) b → (T : ℝ) ≤ c * (2 : ℝ) ^ (δ / 2 * n) → Outputs M x [b] ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨G, hG⟩ : ∃ G, G = (c + 3) ^ q := ⟨_, rfl⟩
  obtain ⟨C₁, hC₁⟩ := exists_pow_le ((c + 2) * q) hδ2
  refine ⟨q * (c + 1) * (G * C₁), fun n x b T hx hr hT => ?_⟩
  obtain ⟨ev⟩ := hs x b T _ hr
  obtain ⟨X, hX⟩ : ∃ X, X = n + 2 := ⟨_, rfl⟩
  rw [← hX] at hx ev
  have hX1 : 1 ≤ X := by omega
  have hbase : x.length + c * X ^ c + 1 ≤ (c + 3) * X ^ (c + 2) := by
    have e0 : 1 ≤ X ^ (c + 2) := Nat.one_le_pow _ _ hX1
    have e1 : X ^ 2 ≤ X ^ (c + 2) := Nat.pow_le_pow_right hX1 (by omega)
    have e2 : X ^ c ≤ X ^ (c + 2) := Nat.pow_le_pow_right hX1 (by omega)
    have e3 : c * X ^ c ≤ c * X ^ (c + 2) := Nat.mul_le_mul_left _ e2
    have e4 : (c + 3) * X ^ (c + 2) = c * X ^ (c + 2) + 3 * X ^ (c + 2) := by ring
    omega
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (x.length + c * X ^ c + 1) ^ q := ⟨_, rfl⟩
  have hpow : Y ≤ G * (n + 2) ^ ((c + 2) * q) := by
    rw [hY, hG, ← hX]
    calc (x.length + c * X ^ c + 1) ^ q ≤ ((c + 3) * X ^ (c + 2)) ^ q := Nat.pow_le_pow_left hbase q
      _ = (c + 3) ^ q * X ^ ((c + 2) * q) := by rw [mul_pow, ← pow_mul]
  rw [← hY] at ev
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 2 * n) := ⟨_, rfl⟩
  have hCn := hC₁ n
  rw [← hE] at hCn hT
  have hE1 : (1 : ℝ) ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
  have hle : q * (T + 1) * Y ≤ ⌊((q * (c + 1) * (G * C₁) : ℕ) : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
    refine Nat.le_floor ?_
    have h1 : ((T : ℝ) + 1) ≤ ((c : ℝ) + 1) * E := by nlinarith
    have h2 : (Y : ℝ) ≤ (G : ℝ) * (C₁ * E) := by
      have h5 : (Y : ℝ) ≤ (G : ℝ) * ((n : ℝ) + 2) ^ ((c + 2) * q) := by exact_mod_cast hpow
      exact h5.trans (mul_le_mul_of_nonneg_left hCn (Nat.cast_nonneg _))
    have h7 : (2 : ℝ) ^ (δ * n) = E * E := by
      rw [hE, ← Real.rpow_add two_pos]
      congr 1
      ring
    push_cast
    rw [h7]
    calc (q : ℝ) * ((T : ℝ) + 1) * (Y : ℝ) ≤ (q : ℝ) * (((c : ℝ) + 1) * E) * ((G : ℝ) * (C₁ * E)) := by gcongr
      _ = ((q : ℝ) * ((c : ℝ) + 1) * ((G : ℝ) * C₁)) * (E * E) := by ring
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans hle⟩⟩

/-- A decider for a property of (G, s) with polynomial-time steps and the exponent δ/2 is simulated
with polynomial overhead by a Turing machine with finite alphabets that decides the property within
⌊C·2^{δn}⌋ steps. -/
theorem hostedFor_of {Ms : StepMachine (List Bool) Bool} {p : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → Prop} {δ : ℝ} {c : ℕ} (hδ : 0 < δ)
    (hp : PolyTimeSteps Ms) (h : DecidesGraph Ms p (δ / 2) c) : HostedFor Ms p δ := by
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates Ms hp
  obtain ⟨C, hC⟩ := outputs_of_simulates hs hδ c
  refine ⟨M, C, q, hfin, hs, fun n G s hsn => ?_⟩
  obtain ⟨T, b, hr, hb, hT⟩ := h n G s hsn
  refine ⟨b, hb, hC n _ b T ?_ hr hT⟩
  rw [length_codeWith stMatrixLength]
  have e : (n + 2) ^ 2 = n * n + 4 * n + 4 := by ring
  omega

/-- The same for k-Coloring. -/
theorem hostedColor_of {Ms : StepMachine (List Bool) Bool} {k : ℕ} {δ : ℝ} {c : ℕ} (hδ : 0 < δ) (hp : PolyTimeSteps Ms) (h : DecidesColor Ms k (δ / 2) c) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Simulates M Ms q ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)), ∃ b : Bool, (b = true ↔ G.Colorable k) ∧ Outputs M (code G) [b] ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates Ms hp
  obtain ⟨C, hC⟩ := outputs_of_simulates hs hδ c
  refine ⟨M, C, q, hfin, hs, fun n G => ?_⟩
  obtain ⟨T, b, hr, hb, hT⟩ := h n G
  refine ⟨b, hb, hC n _ b T ?_ hr hT⟩
  rw [length_code stMatrixLength]
  have e : (n + 2) ^ 2 = n * n + 4 * n + 4 := by ring
  omega

end Sat3Graph
