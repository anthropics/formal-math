/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Complement.Defs
import Complement.Readers
import GraphProblems.Read
import GraphProblems.Sets
import GraphProblems.Host
import ToTuring.Poly.Basic
import Mathlib.Tactic

/-! # Section 7, Corollary 7 for cliques and vertex covers, on Turing machines, through the formula for independent sets

`tm_of_reader`: let Ms be a machine cut into polynomial-time steps that, on `codeWith G s` with s ≤
n, returns a number f(G, s) within c·2^{(δ/2)n} steps on states of size at most c·(n + n² + 2)^c,
and let `post` be a polynomial-time map from numbers to words. Then a Turing machine of Mathlib with
finite alphabets, started on `codeWith G s`, halts with `post` (f(G, s)) within ⌊C·2^{δn}⌋ steps. It
is `GraphProblems.tm_of_stepped` on the instances (G, s).
`stOnTuringMachines`: the machine Z of `stFromSized` after `readClique` and `readCover`, with the
number written by `Nat.bits` (counting) or with «the number is not 0» as the output (deciding;
«subsets of … cliques, and supersets of vertex covers …, are again such sets»,
`GraphProblems.stDecide`). -/

public section

namespace Complement

open Groundwork Groundwork.Prog CountKSat GraphProblems Turing

/-- From a machine cut into steps on the words `codeWith G s` to a Turing machine: if Ms has
polynomial-time steps and returns f(G, s), for s ≤ n, within c·2^{(δ/2)n} steps on states of size at
most c·(n + n² + 2)^c, and `post` is polynomial time, then a Turing machine with finite alphabets
halts on `codeWith G s` with `post (f(G, s))` within ⌊C·2^{δn}⌋ steps. -/
theorem tm_of_reader (Ms : Stepped (List Bool) ℕ) (hp : Nonempty (IsPolyT Ms)) (f : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → ℕ) {δ : ℝ} (hδ : 0 < δ) (c : ℕ)
    (h : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n → ∃ T : ℕ, Ms.Runs (codeWith G s) T (c * (n + n * n + 2) ^ c) (f n G s) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ / 2 * n))
    (post : ℕ → List Bool) (hpost : PolyT post) :
    ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : ℕ), s ≤ n →
      Outputs M (codeWith G s) (post (f n G s)) ⌊(C : ℝ) * (2 : ℝ) ^ (δ * n)⌋₊ := by
  obtain ⟨hp⟩ := hp
  have := IsPolyT.mapOut (M := Ms) hpost
  obtain ⟨M, C, hfin, hM⟩ := tm_of_stepped (Stepped.mapOut Ms post) (ι := Inst)
    (fun x => codeWith x.2.1 x.2.2.1) (fun x => post (f x.1 x.2.1 x.2.2.1)) (fun x => x.1) hδ (2 * c) 1 2
    (fun x => by
      obtain ⟨n, G, s, hs⟩ := x
      simp only [length_codeWith stMatrixLength]
      nlinarith)
    (fun x => by
      obtain ⟨n, G, s, hs⟩ := x
      obtain ⟨T, hr, hT⟩ := h n G s hs
      refine ⟨T, (Stepped.mapOut_runs hr).mono le_rfl ?_, hT.trans ?_⟩
      · have h1 : n + n * n + 2 ≤ (n + 2) ^ 2 := by nlinarith
        calc c * (n + n * n + 2) ^ c ≤ c * ((n + 2) ^ 2) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 c)
          _ = c * (n + 2) ^ (2 * c) := by rw [← pow_mul]
          _ ≤ 2 * c * (n + 2) ^ (2 * c) := Nat.mul_le_mul_right _ (by omega)
      · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        push_cast
        have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
        linarith)
  exact ⟨M, C, hfin, fun n G s hs => hM ⟨n, G, s, hs⟩⟩

/-- The two clauses of `GraphProblems.CorGraphsCount` and the two of `GraphProblems.CorGraphsDecide`
on cliques and vertex covers, on Mathlib's Turing machines, from the interface
`GraphProblems.StSized`: for every δ > 0 Turing machines compute the numbers of cliques and of
vertex covers of size s, and decide whether there is a clique with at least s vertices and whether
there is a vertex cover with at most s vertices, in time O(2^{δn}). -/
theorem stOnTuringMachines : StOnTuringMachines := fun hS δ hδ => by
  obtain ⟨Z, hp1, hp2, c, h⟩ := stFromSized hS (δ / 2) (by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact tm_of_reader _ hp1 (fun _ G s => numCliques G s) hδ c (fun n G s hs => (h n G s hs).1) Nat.bits bits_polyT
  · exact tm_of_reader _ hp2 (fun _ G s => numVertexCovers G s) hδ c (fun n G s hs => (h n G s hs).2) Nat.bits bits_polyT
  · obtain ⟨M, C, hf, hM⟩ := tm_of_reader _ hp1 (fun _ G s => numCliques G s) hδ c (fun n G s hs => (h n G s hs).1) nzW nzW_polyT
    exact ⟨M, C, hf, fun n G s hs => ⟨_, by
      rw [decide_eq_true_iff]
      exact (stDecide n G s hs).2.1.symm, hM n G s hs⟩⟩
  · obtain ⟨M, C, hf, hM⟩ := tm_of_reader _ hp2 (fun _ G s => numVertexCovers G s) hδ c (fun n G s hs => (h n G s hs).2) nzW nzW_polyT
    exact ⟨M, C, hf, fun n G s hs => ⟨_, by
      rw [decide_eq_true_iff]
      exact (stDecide n G s hs).2.2.1.symm, hM n G s hs⟩⟩

end Complement
