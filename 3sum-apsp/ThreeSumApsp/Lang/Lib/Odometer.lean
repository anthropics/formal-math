/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Util.Odometer

/-!
# An odometer in the memory

`incStmt vb vn j len` adds 1 to the number whose len digits in base n, least significant first, are
in the cells base + j, base + j + 1, …; a carry out of the last digit is dropped (`incStmt_ends`).
Local vb holds base and local vn holds n.  The number of digits is known when the program is
written, so the statement has no loop: it is a chain of len tests, and the proof is an induction on
the list of the digits.  The pure model is `ThreeSumApsp.incDigits`.
-/

@[expose] public section

namespace Light

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Add 1 to the number with the digits at base + j, …, base + j + len - 1. -/
def incStmt (vb vn : ℕ) : ℕ → ℕ → Stmt
  | _, 0 => .skip
  | j, len + 1 =>
    .ite (M (v vb +' k j) +' k 1 <' v vn)
      (.store (v vb +' k j) (M (v vb +' k j) +' k 1))
      (.store (v vb +' k j) (k 0) ;; incStmt vb vn (j + 1) len)

/-- **incStmt** replaces the digits l by `ThreeSumApsp.incDigits n l`, changes nothing else, and
takes at
most 14 len + 5 steps. -/
theorem incStmt_ends {vb vn base n j : ℕ} {l : List ℕ} {μ loc : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : (n : ℤ) ≤ lim.word) (eb : loc vb = base)
    (en : loc vn = n) (hspace : base + j + l.length ≤ lim.space) (hlt : ∀ x ∈ l, x < n)
    (hseg : SegN μ (base + j) l) :
    Ends lim P d (incStmt vb vn j l.length) ⟨loc, μ⟩ (14 * l.length + 5) fun σ' =>
      σ'.loc = loc ∧ SegN σ'.mem (base + j) (ThreeSumApsp.incDigits n l) ∧
      SameOutside μ σ'.mem (base + j) l.length := by
  induction l generalizing j μ with
  | nil => exact Ends.skip ⟨rfl, by simpa [ThreeSumApsp.incDigits] using hseg, .refl⟩
  | cons x l ih =>
    simp only [List.length_cons] at hspace ⊢
    have hx : x < n := hlt x (by simp)
    obtain ⟨hread, hrest⟩ : μ (base + j) = x ∧ SegN μ (base + j + 1) l := seg_cons.1 hseg
    have haddr : ((base : ℤ) + j).toNat = base + j := by omega
    rw [incStmt, ThreeSumApsp.incDigits]
    -- if digit + 1 < n
    refine Ends.iteLast (fun hc => ?_) (fun hc => ?_)
      (by light_side [eb, haddr, hread])
    · have hc' : x + 1 < n := by
        have : (x : ℤ) + 1 < n := by simpa [eb, en, haddr, hread] using hc
        omega
      rw [if_pos hc']
      -- digit := digit + 1
      refine Ends.storeLast ⟨rfl, ?_, ?_⟩ (by light_side [eb, haddr, hread])
      · simp only [Expr.val, Op.eval, eb, haddr, hread]
        exact seg_cons.2 ⟨by simp, hrest.update_out (Or.inl (by omega)) _⟩
      · simp only [Expr.val, Op.eval, eb, haddr]
        exact SameOutside.refl.update ⟨le_rfl, by omega⟩ _
    · have hc' : ¬ x + 1 < n := fun h =>
        hc (by simpa [eb, en, haddr, hread] using (by omega : (x : ℤ) + 1 < n))
      rw [if_neg hc']
      -- digit := 0, and the carry goes to the next digit
      refine Ends.storeThen ?_ (by light_side [eb])
      simp only [Expr.val, Op.eval, eb, haddr]
      light_piece (ih (j := j + 1) (by omega) (fun y hy => hlt y (by simp [hy]))
        (hrest.update_out (Or.inl (by omega)) _)) with σ' ⟨hloc, hseg', hsame⟩
      refine ⟨hloc, seg_cons.2 ⟨?_, hseg'⟩, fun b hb => ?_⟩
      · rw [hsame _ (Or.inl (by omega))]
        simp
      · rw [hsame b (by omega), Function.update_of_ne (by omega)]

end Light
