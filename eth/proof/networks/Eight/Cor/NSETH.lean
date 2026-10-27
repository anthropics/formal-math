/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.Cor.NSETHDefs
public import Eight.Cor.Defs
public import Eight.Level.End
public import WidthK.Top.Poly
public import KSatStatement
public import ToTuring.PolyT
public import ToTuring.Machine.EndTM
public import WidthK.Top.EndLemmas
public import WidthK.Decode
public import SparsifyWidthK.DefsProg
import GraphProblems.Host
import Mathlib.Tactic

/-! # Section 7, the sentence after Corollary 5: k-DNF tautologies, and taking a witness off an input

The paper's sentence on NSETH rests on two facts: «a k-DNF is a tautology exactly if its negation, a
k-CNF, is unsatisfiable», and a deterministic algorithm is a nondeterministic one. The definitions
are in proof/networks/Eight/Cor/NSETHDefs.lean.
This file proves the first fact, `tautology_iff`, and two facts on `stripW`, which takes a witness
off an input word: it returns the word without the witness (`stripW_withWitness`),
and it is polynomial-time (`stripW_polyT`).

Different from the paper: the negation of a k-DNF ψ is the k-CNF with the same lists and all
literals negated. That formula is satisfiable exactly if the k-CNF with the same lists and the same
literals is (negate the assignment), so the
lemma `tautology_iff` is stated for the k-CNF with the same lists as ψ. -/

public section

namespace Eight

open Groundwork Groundwork.Prog Paper Turing

/-- «A k-DNF is a tautology exactly if its negation, a k-CNF, is unsatisfiable», in this form: the
DNF ψ is a tautology exactly if the CNF with the same lists of literals is unsatisfiable. An
assignment a falsifies the DNF exactly if the
assignment with all values negated satisfies the CNF. -/
theorem tautology_iff {n : ℕ} (ψ : DNF n) : Tautology ψ ↔ ¬ Sat3.Satisfiable ψ := by
  constructor
  · rintro h ⟨a, ha⟩
    obtain ⟨D, hD, hl⟩ := h fun i => !a i
    obtain ⟨l, hlD, hal⟩ := ha D hD
    have := hl l hlD
    rw [← hal] at this
    simp at this
  · intro h a
    by_contra hc
    refine h ⟨fun i => !a i, fun D hD => ?_⟩
    by_contra hn
    refine hc ⟨D, hD, fun l hl => ?_⟩
    by_contra hne
    refine hn ⟨l, hl, ?_⟩
    cases h1 : a l.1 <;> cases h2 : l.2 <;> simp_all

/-- `stripW` takes the witness off. -/
theorem stripW_withWitness (w x : List Bool) : stripW (withWitness w x) = x := by
  have h1 : (withWitness w x).dropWhile id = false :: (w ++ x) := by
    unfold withWitness
    rw [List.dropWhile_append_of_pos (by simp)]
    simp
  have h2 : (withWitness w x).takeWhile id = List.replicate w.length true := by
    unfold withWitness
    rw [List.takeWhile_append_of_pos (by simp)]
    simp
  simp [stripW, h1, h2]

/-- `stripW` is polynomial-time. -/
theorem stripW_polyT : PolyT stripW := by unfold stripW; fun_prop

end Eight
