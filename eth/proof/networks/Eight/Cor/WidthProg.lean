/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.Cor.Width
public import CountKSat.InOut
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 6: the width reduction is polynomial-time

`splitN n x` is the width reduction of `WidthDefs.lean` (the same `splitAll`, then `List.dedup`) for
a formula x whose variables are natural numbers below n; the fresh variables are n, n + 1, ….
`widthP` takes the number of variables in unary with the formula, the form in which
the programs of this development take an input, and returns the number of variables of the image in
unary with the image. `widthP_polyT`: it is polynomial-time in the sense of `Groundwork.PolyT`.
For the certificate the two recursions are written without recursion (`clauseP`, `allP`) and shown
to give the same lists (`splitClause_eq`, `splitAll_eq`).
`toN_widthReduce`: on an instance φ, read with numbers as variables (`Decode.toN`), the program
returns `widthReduce φ` read in the same way. `cntN_splitN`: so it keeps the number of satisfying
assignments, in the form `CountKSat.cntN` of the counting programs.
No machine and no bound on its time is made from this here. -/

@[expose] public section

namespace Eight.Width

open Groundwork Groundwork.Prog CountKSat

/-- The fresh variables n, n + 1, …, n + N − 1. -/
def freshN (n N : ℕ) : List ℕ := (List.range N).map fun i => n + i

/-- The width reduction of a formula with numbers as variables, all below n. -/
def splitN (n : ℕ) (x : Fml) : Fml := (splitAll (freshN n (numFresh x)) x).dedup

/-- The same with the numbers of variables in unary. -/
def widthP (p : List Unit × Fml) : List Unit × Fml :=
  (List.replicate (p.1.length + numFresh p.2) (), splitN p.1.length p.2)

/-- `splitClause` without recursion, for at most s − 3 fresh variables, s the number of literals of
C. Counting from 0, the i-th fresh variable stands for the disjunction of the literal before it (the
first literal of C, or the fresh variable number i − 1) and the literal number i + 1 of C; the last
clause is the last fresh variable with the rest of C. -/
def clauseP (ys : List ℕ) (C : List (ℕ × Bool)) : Fml :=
  (ys.zip ((C.headD (0, false) :: ys.map fun y => (y, true)).zip C.tail)).flatMap (fun q => forced q.1 q.2.1 q.2.2) ++
    [if ys.isEmpty then C else (ys.getLast?.getD 0, true) :: C.drop (ys.length + 1)]

/-- `splitAll` without recursion: the clause number j takes its fresh variables after those of the
clauses before it. -/
def allP (ys : List ℕ) (x : Fml) : Fml :=
  (List.range x.length).flatMap fun j =>
    clauseP ((ys.drop (numFresh (x.take j))).take ((x.getD j []).length - 3)) (x.getD j [])

theorem splitClause_eq : ∀ (ys : List ℕ) (C : List (ℕ × Bool)), ys.length ≤ C.length - 3 → splitClause ys C = clauseP ys C
  | [], C, _ => by simp [splitClause_nil, clauseP]
  | y :: ys, C, h => by
    have hC : ¬ C.length ≤ 3 := by simp at h; omega
    obtain ⟨l₁, l₂, l₃, l₄, r, rfl⟩ := exists_four hC
    rw [splitClause_step, splitClause_eq ys _ (by simp at h ⊢; omega)]
    cases ys with
    | nil => simp [clauseP]
    | cons z zs => simp [clauseP, List.getLast?_cons_cons]

theorem splitAll_eq : ∀ (x : Fml) (ys : List ℕ), splitAll ys x = allP ys x
  | [], _ => by simp [splitAll, allP]
  | C :: x, ys => by
    rw [splitAll_cons, splitAll_eq x, splitClause_eq _ _ (by simp)]
    simp only [allP, List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map, List.take_zero,
      List.getD_cons_zero, List.getD_cons_succ, List.take_succ_cons, numFresh_cons, List.drop_drop]
    simp [numFresh]

theorem forced_polyT : PolyT fun q : ℕ × (ℕ × Bool) × (ℕ × Bool) => forced q.1 q.2.1 q.2.2 := by
  unfold forced neg
  fun_prop

theorem clauseP_polyT : PolyT fun p : List ℕ × List (ℕ × Bool) => clauseP p.1 p.2 := by
  have := forced_polyT
  unfold clauseP
  fun_prop

theorem numFresh_polyT : PolyT fun x : Fml => numFresh x := by
  unfold numFresh
  fun_prop

theorem allP_polyT : PolyT fun p : List ℕ × Fml => allP p.1 p.2 := by
  have h1 := clauseP_polyT
  have h2 := numFresh_polyT
  have hr : PolyT fun p : List ℕ × Fml => List.range p.2.length := PolyT.range (Unary.of_length (by fun_prop))
  unfold allP
  fun_prop

/-- The number of fresh variables in unary: it is at most the number of literals written. -/
theorem numFresh_unary : Unary fun x : Fml => numFresh x := by
  refine Unary.of_le (g := fun x : Fml => x.flatten.length) (Unary.of_length (by fun_prop)) numFresh_polyT fun x => ?_
  induction x with
  | nil => simp [numFresh]
  | cons C x ih => rw [numFresh_cons]; simp only [List.flatten_cons, List.length_append]; omega

theorem splitN_polyT : PolyT fun p : ℕ × Fml => splitN p.1 p.2 := by
  have h1 := allP_polyT
  have hr : PolyT fun p : ℕ × Fml => List.range (numFresh p.2) := PolyT.range (numFresh_unary.comp (by fun_prop))
  have h : PolyT fun p : ℕ × Fml => (allP (freshN p.1 (numFresh p.2)) p.2).dedup := by
    unfold freshN
    fun_prop
  exact h.congr fun p => by rw [splitN, splitAll_eq]

/-- The width reduction, with the numbers of variables in unary, is polynomial-time. -/
theorem widthP_polyT : PolyT widthP := by
  have h1 := splitN_polyT
  have hu : Unary fun p : List Unit × Fml => p.1.length + numFresh p.2 :=
    (Unary.of_length (by fun_prop)).add (numFresh_unary.comp (by fun_prop))
  have h2 : PolyT fun p : List Unit × Fml => splitN p.1.length p.2 := by fun_prop
  exact PolyT.prodMk hu h2

/-! ### The program gives the width reduction of `WidthDefs.lean` -/

/-- Renaming the variables commutes with `splitClause`. -/
theorem splitClause_map {V W : Type} (f : V → W) : ∀ (ys : List V) (C : List (V × Bool)),
    (splitClause ys C).map (fun D => D.map fun l => (f l.1, l.2)) = splitClause (ys.map f) (C.map fun l => (f l.1, l.2))
  | [], C => by simp [splitClause_nil]
  | y :: ys, C => by
    by_cases hC : C.length ≤ 3
    · rw [splitClause_short _ hC, splitClause_short _ (by simpa using hC)]
      rfl
    · obtain ⟨l₁, l₂, l₃, l₄, r, rfl⟩ := exists_four hC
      simp only [List.map_cons, splitClause_step, List.map_append, splitClause_map f ys]
      simp [forced, neg]

/-- Renaming the variables commutes with `splitAll`. -/
theorem splitAll_map {V W : Type} (f : V → W) : ∀ (φ : List (List (V × Bool))) (ys : List V),
    (splitAll ys φ).map (fun D => D.map fun l => (f l.1, l.2)) = splitAll (ys.map f) (φ.map fun D => D.map fun l => (f l.1, l.2))
  | [], _ => rfl
  | C :: φ, ys => by
    simp only [List.map_cons, splitAll_cons, List.map_append, splitClause_map, splitAll_map f φ, List.map_take, List.map_drop,
      List.length_map]

theorem numFresh_toN {n : ℕ} (φ : Sat3.CNF n) : numFresh (Decode.toN φ) = numFresh φ := by
  simp [numFresh, Decode.toN, Function.comp_def]

/-- `widthReduce φ`, with its variables read as numbers, is what the program returns on φ with its
variables read as numbers. -/
theorem toN_widthReduce {n : ℕ} (φ : Sat3.CNF n) : Decode.toN (widthReduce φ) = splitN n (Decode.toN φ) := by
  have hinj : Function.Injective fun D : List (Sat3.Lit (n + numFresh φ)) => D.map fun l => (l.1.val, l.2) := by
    refine List.map_injective_iff.2 fun a b h => ?_
    exact Prod.ext (Fin.ext (Prod.mk.inj h).1) (Prod.mk.inj h).2
  rw [widthReduce_eq, splitN, Decode.toN, ← List.dedup_map_of_injective hinj, splitAll_map, numFresh_toN]
  congr 2
  · simp [freshFin, freshN, List.finRange_eq_pmap_range, List.map_pmap]
  · simp [lift, Decode.toN, Function.comp_def]

/-- The number of satisfying assignments in the form of the counting programs of this development:
on the formula of an instance, the program keeps it. -/
theorem cntN_splitN {n : ℕ} (φ : Sat3.CNF n) :
    cntN (n + numFresh (Decode.toN φ)) (splitN n (Decode.toN φ)) = cntN n (Decode.toN φ) := by
  rw [← toN_widthReduce, numFresh_toN, stCntToN, stCntToN, numSat_widthReduce]

end Eight.Width
