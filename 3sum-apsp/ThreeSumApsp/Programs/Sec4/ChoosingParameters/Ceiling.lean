/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Parameters

/-!
# Corollaries 26 and 31 in the light language: ⌈a m / b⌉ by counting

Proof of Corollary 26: "Let L := 21m and t := ⌈m/9⌉"; proof of Corollary 31: "with L := ⌈cm⌉ and t
:= ⌈θm⌉". For rational c = a/b the number ⌈a m / b⌉ is found without division: count in steps of b
up to a m. The numbers a and b are constants of the program text.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp

namespace CeilMul

/-- The locals of ceilMul: the argument m, which the result replaces; the product a m; a counter
that goes up in steps of b; and the number of its steps. -/
abbrev Arg : ℕ := 0
@[inherit_doc Arg] abbrev Goal : ℕ := 1
@[inherit_doc Arg] abbrev Reached : ℕ := 2
@[inherit_doc Arg] abbrev Steps : ℕ := 3

end CeilMul

open CeilMul in
/-- ceilMul(m) counts up to a m in steps of b. For m = 0 the result is 0, and the constant a is not
touched (it need not fit in a word then). -/
def ceilMulBody (a b : ℕ) : Stmt :=
  .ite (v Arg =' k 0) .skip
    (.set Goal (k a *' v Arg) ;; .set Reached (k 0) ;; .set Steps (k 0) ;;
      .while (v Reached <' v Goal)
        (.set Reached (v Reached +' k b) ;; .set Steps (v Steps +' k 1)) ;;
      .set Arg (v Steps))

theorem ceilMul_meets {lim : Limits} {P : Program} {pn a b : ℕ} (hb : 1 ≤ b)
    (hP : P[pn]? = some (ceilMulBody a b)) : CeilMulSpec lim P pn a b := by
  intro m μ hw
  refine fun d _ => ⟨ceilMulBody a b, hP, ?_⟩
  unfold ceilMulBody tCeilMul
  -- if m = 0
  refine Ends.iteLast (fun h0 => ?_) (fun h0 => ?_)
  · -- return m
    obtain rfl : m = 0 := by simpa using h0
    exact Ends.skip ⟨by simp [Nat.div_eq_of_lt (by omega : b - 1 < b)], rfl⟩
  · have hm : m ≠ 0 := by simpa using h0
    have hax : a ≤ a * m := Nat.le_mul_of_pos_right a (by omega)
    have hxZ : (a : ℤ) * m = (a * m : ℕ) := by push_cast; rfl
    generalize a * m = x at hw hax hxZ ⊢
    have hlt : ∀ i, i < (x + b - 1) / b ↔ i * b < x := fun i => Nat.lt_ceilDiv_iff hb
    have hnx : (x + b - 1) / b ≤ x := by
      by_contra hc
      have := (hlt x).1 (by omega)
      have := Nat.le_mul_of_pos_right x hb
      omega
    generalize (x + b - 1) / b = n at hlt hnx ⊢
    -- am := a * m ; c := 0 ; steps := 0
    light_set x using hxZ
    light_set 0
    light_set 0
    -- while c < am: c := c + b ; steps := steps + 1.  Before round i, c = i b and steps = i.
    refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [m, x, ((i * b : ℕ) : ℤ), i], μ⟩) n
      (by simp) ?round ?done (hT := le_rfl))
    case round =>
      rintro i _ hi rfl
      have hbi := (hlt i).1 hi
      rw [Nat.succ_mul]
      generalize i * b = c at hbi ⊢
      exact ⟨by light_side, by simp; omega, by light_side, by simp [update_frame_setLocal]⟩
    case done =>
      rintro _ rfl
      have hbn := mt (hlt n).2 (lt_irrefl n)
      generalize n * b = c at hbn ⊢
      -- return steps
      exact ⟨by light_side, by simp; omega, Ends.setTo (n : ℤ) ⟨rfl, rfl⟩⟩

end Light.Sec4
