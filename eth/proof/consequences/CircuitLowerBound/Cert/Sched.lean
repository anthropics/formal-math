/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.InterfacesPolyT
public import ToTuring.Lib.Unary
public import ToTuring.Lib.Nat2
public import ToTuring.Lib.Nat1b
public import ToTuring.Lib.List3
public import ToTuring.Poly.Words
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): the chains are computed in polynomial time

From m in unary, in polynomial time: the number `nu m` of the chain of m, its table `codeOf (nu m)`,
the next number of the chain, whether m stands before or at the last place of its chain, and
whether a table has room (`stCertSched`). The last place 2^2^2^a of chain a is never computed: it is
compared with s through two binary logarithms of s (`top_le_iff`). -/

public section

namespace CircuitLowerBound.Sched

open ENP Groundwork

variable {α : Type} [Enc α]

/-! ### Comparison with the last place of a chain -/

/-- «2^2^2^a ≤ s», by two logarithms. -/
@[expose] def leTop (a s : ℕ) : Bool := decide (s ≠ 0) && (decide (Nat.log2 s ≠ 0) && decide (2 ^ a ≤ Nat.log2 (Nat.log2 s)))

/-- The program decides «the last place of chain a is at most s». -/
theorem top_le_iff (a s : ℕ) : top a ≤ s ↔ leTop a s = true := by
  simp only [leTop, Bool.and_eq_true, decide_eq_true_eq, top]
  constructor
  · intro h
    have h0 : s ≠ 0 := by
      have : 0 < 2 ^ 2 ^ 2 ^ a := by positivity
      omega
    have h1 : 2 ^ 2 ^ a ≤ Nat.log2 s := (Nat.le_log2 h0).2 h
    have h2 : Nat.log2 s ≠ 0 := by
      have : 0 < 2 ^ 2 ^ a := by positivity
      omega
    exact ⟨h0, h2, (Nat.le_log2 h2).2 h1⟩
  · rintro ⟨h0, h2, h3⟩
    exact (Nat.le_log2 h0).1 ((Nat.le_log2 h2).1 h3)

/-- «s comes before the last place of chain a». -/
theorem lt_top_iff (a s : ℕ) : s < top a ↔ (!leTop a s) = true := by
  rw [Bool.not_eq_true', ← Bool.not_eq_true, ← top_le_iff]
  omega

/-- «s is the last place of chain a»: it is at most s and not at most s − 1. -/
theorem eq_top_iff (a s : ℕ) : s = top a ↔ (leTop a s && !leTop a (s - 1)) = true := by
  rw [Bool.and_eq_true, ← top_le_iff, ← lt_top_iff]
  have : 0 < top a := by unfold top; positivity
  omega

/-! ### Certificates -/

/-- The number of the chain is given in unary. -/
theorem nu_unary {m : α → ℕ} (hm : PolyT m) : Unary fun x => nu (m x) := by
  unfold nu
  exact Unary.of_length (by fun_prop)

/-- The place of m in its chain. -/
theorem pos_polyT {m : α → ℕ} (hm : PolyT m) : PolyT fun x => pos (m x) := by
  have h1 : PolyT fun x => 2 ^ nu (m x) := PolyT.two_pow (nu_unary hm)
  exact PolyT.div (PolyT.div hm h1) (PolyT.const 2)

/-- The next number of the chain. -/
theorem next_polyT {m : α → ℕ} (hm : PolyT m) : PolyT fun x => next (m x) :=
  PolyT.add hm (PolyT.two_pow ((nu_unary hm).add (Unary.const 1)))

/-- The comparison with the last place of chain a, for a in unary. -/
theorem leTop_polyT {a s : α → ℕ} (ha : Unary a) (hs : PolyT s) : PolyT fun x => leTop (a x) (s x) := by
  have h1 : PolyT fun x => 2 ^ a x := PolyT.two_pow ha
  have key : ∀ p : α → ℕ, PolyT p → PolyT fun x => decide (s x ≠ 0) && (decide (Nat.log2 (s x) ≠ 0) && decide (p x ≤ Nat.log2 (Nat.log2 (s x)))) := by
    intro p _
    fun_prop
  exact key _ h1

/-- The number of ones at the start of a word. -/
theorem ones_polyT {w : α → List Bool} (hw : PolyT w) : PolyT fun x => ones (w x) := by unfold ones; fun_prop
/-- The word after its first ones and the zero that ends them. -/
theorem rest_polyT {w : α → List Bool} (hw : PolyT w) : PolyT fun x => rest (w x) := by unfold rest; fun_prop

/-- A number of W bits in a word. -/
theorem fld_polyT {W i : α → ℕ} {w : α → List Bool} (hW : PolyT W) (hw : PolyT w) (hi : PolyT i) : PolyT fun x => fld (W x) (w x) (i x) := by
  unfold fld; fun_prop

/-- Five numbers of a word as a literal of a table. -/
theorem litOf_polyT {W i : α → ℕ} {w : α → List Bool} (hW : PolyT W) (hw : PolyT w) (hi : PolyT i) : PolyT fun x => litOf (W x) (w x) (i x) := by
  have h0 := fld_polyT hW hw hi
  have h1 := fld_polyT hW hw (i := fun x => i x + 1) (by fun_prop)
  have h2 := fld_polyT hW hw (i := fun x => i x + 2) (by fun_prop)
  have h3 := fld_polyT hW hw (i := fun x => i x + 3) (by fun_prop)
  have h4 := fld_polyT hW hw (i := fun x => i x + 4) (by fun_prop)
  unfold litOf
  fun_prop

/-- The table written by a word. -/
theorem codeOfWord_polyT {u : α → List Bool} (hu : PolyT u) : PolyT fun x => codeOfWord (u x) := by
  have hW := ones_polyT hu
  have hw := rest_polyT hu
  have hn : Unary fun x => ((rest (u x)).length - 2 * ones (u x)) / (15 * ones (u x)) :=
    Unary.of_le (Unary.of_length hw) (PolyT.div (by fun_prop) (by fun_prop)) fun x => (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hl : ∀ c : ℕ, PolyT fun p : α × ℕ => litOf (ones (u p.1)) (rest (u p.1)) (2 + 15 * p.2 + c) := fun c =>
    litOf_polyT (ones_polyT (by fun_prop)) (rest_polyT (by fun_prop)) (by fun_prop)
  have hl0 : PolyT fun p : α × ℕ => litOf (ones (u p.1)) (rest (u p.1)) (2 + 15 * p.2) :=
    litOf_polyT (ones_polyT (by fun_prop)) (rest_polyT (by fun_prop)) (by fun_prop)
  have hm : PolyT fun x => (List.range (((rest (u x)).length - 2 * ones (u x)) / (15 * ones (u x)))).map fun r =>
      (litOf (ones (u x)) (rest (u x)) (2 + 15 * r), litOf (ones (u x)) (rest (u x)) (2 + 15 * r + 5), litOf (ones (u x)) (rest (u x)) (2 + 15 * r + 10)) :=
    PolyT.map (f := fun x r => (litOf (ones (u x)) (rest (u x)) (2 + 15 * r), litOf (ones (u x)) (rest (u x)) (2 + 15 * r + 5),
      litOf (ones (u x)) (rest (u x)) (2 + 15 * r + 10))) (hl0.prodMk ((hl 5).prodMk (hl 10))) (PolyT.range hn)
  exact (fld_polyT hW hw (PolyT.const 0)).prodMk ((fld_polyT hW hw (PolyT.const 1)).prodMk hm)

/-- The table with the number a. -/
theorem codeOf_polyT {a : α → ℕ} (ha : PolyT a) : PolyT fun x => codeOf (a x) :=
  codeOfWord_polyT (rest_polyT (by fun_prop))

/-- The three components of a table. -/
theorem kb_polyT {e : α → MCode} (he : PolyT e) : PolyT fun x => kb (e x) := by unfold kb; fun_prop
theorem lam_polyT {e : α → MCode} (he : PolyT e) : PolyT fun x => lam (e x) := by unfold lam; fun_prop
theorem tab_polyT {e : α → MCode} (he : PolyT e) : PolyT fun x => tab (e x) := by unfold tab; fun_prop

/-- A time has at most L bits. -/
theorem bt_le (e : MCode) (L : ℕ) : bt e L ≤ L := by
  unfold bt
  omega

/-- The number of bits of a time is given in unary if L is. -/
theorem bt_unary {e : α → MCode} {L : α → ℕ} (he : PolyT e) (hL : Unary L) : Unary fun x => bt (e x) (L x) := by
  have h1 := kb_polyT he
  have h2 := lam_polyT he
  have h3 := hL.poly
  exact Unary.of_le hL (PolyT.div (by fun_prop) (PolyT.const 2)) fun x => bt_le _ _

/-- «There is room». -/
theorem fits_polyT {e : α → MCode} {L P : α → ℕ} (he : PolyT e) (hL : Unary L) (hP : PolyT P) : PolyT fun x => decide (Fits (e x) (L x) (P x)) := by
  have h1 := kb_polyT he
  have h2 := lam_polyT he
  have h3 := hL.poly
  have h4 : PolyT fun x => 2 ^ bt (e x) (L x) := PolyT.two_pow (bt_unary he hL)
  have key : ∀ k l p : α → ℕ, PolyT k → PolyT l → PolyT p → PolyT fun x => decide (k x + l x + 4 ≤ L x ∧ P x + 2 ≤ p x) := by
    intro k l p _ _ _
    fun_prop
  exact key _ _ _ h1 h2 h4

end CircuitLowerBound.Sched

namespace CircuitLowerBound

open ENP Groundwork Sched

/-- The chains are computed in polynomial time from m in unary. -/
theorem stCertSched : StCertSched := by
  have hm : PolyT fun u : List Unit => u.length := by fun_prop
  refine ⟨codeOf_polyT (nu_unary hm).poly, next_polyT hm, (nu_unary hm).poly, ?_, ?_, fits_polyT (by fun_prop) (Unary.of_length (by fun_prop)) (by fun_prop)⟩
  · exact (PolyT.not' (leTop_polyT (nu_unary hm) (pos_polyT hm))).congr fun u => by
      rw [Bool.eq_iff_iff, decide_eq_true_eq, lt_top_iff]
  · have h1 := leTop_polyT (nu_unary hm) (pos_polyT hm)
    have h2 := leTop_polyT (nu_unary hm) (s := fun u : List Unit => pos u.length - 1) (PolyT.sub (pos_polyT hm) (PolyT.const 1))
    exact (PolyT.and' h1 (PolyT.not' h2)).congr fun u => by
      rw [Bool.eq_iff_iff, decide_eq_true_eq, eq_top_iff]

end CircuitLowerBound
