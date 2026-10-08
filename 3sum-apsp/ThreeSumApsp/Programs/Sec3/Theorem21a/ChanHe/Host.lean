/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.HostContracts
public import ThreeSumApsp.Programs.Tasks

/-!
# The host of the reduction from 3SUM to Convolution-3SUM

Theorem 21(a), after [CH20, Theorem 5.1]: 3SUM on n numbers reduces to
instances of Convolution-3SUM.  This file holds the outermost procedure of the reduction.

s3(n, U, x, fr), with a parameter κ that is fixed with the program: the host replaces the bound U by
U' = max U (n^κ) and calls core(n, 2U', x, fr) (`CoreSpec`).  So on all inputs with U ≤ n^κ the
solver of Convolution-3SUM is asked for instances of one and the same length and bound (`chTime`).
The power n^κ is computed by κ multiplications; the text of the program has one assignment for each
of them (`hostPow_ends`).  `hostCall_ends` is the call of core, and `host_spec` the whole.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Host

/-- The number n of numbers, and at the end the answer. -/
abbrev Num : ℕ := 0
/-- The bound U. -/
abbrev Bound : ℕ := 1
/-- The address of the numbers. -/
abbrev Addr : ℕ := 2
/-- The free pointer. -/
abbrev Free : ℕ := 3
/-- n^κ, and then max U (n^κ). -/
abbrev Power : ℕ := 4

end Host

open Host

/-- κ multiplications of Power by n. -/
def hostPow : ℕ → Stmt
  | 0 => .skip
  | κ + 1 => .set Power (v Power *' v Num) ;; hostPow κ

/-- s3(n, U, x, fr): Power := max U (n^κ), and then the answer of the procedure number pCore (core)
on (n, 2 Power, x, fr). -/
def hostBody (κ pCore : ℕ) : Stmt :=
  .set Power (k 1) ;;
  hostPow κ ;;
  .ite (v Power <' v Bound) (.set Power (v Bound)) .skip ;;
  .call pCore [v Num, v Power +' v Power, v Addr, v Free] Num

/-- **The κ multiplications** take n^j to n^(j + κ), if all these powers fit in a word. -/
theorem hostPow_ends {n B : ℕ} {U a fr : ℤ} {μ : ℕ → ℤ} (hB : (B : ℤ) ≤ lim.word) (κ : ℕ) :
    ∀ j : ℕ, (∀ i ≤ j + κ, n ^ i ≤ B) →
      Ends lim P d (hostPow κ) ⟨frame [n, U, a, fr, (n ^ j : ℕ)], μ⟩ (4 * κ) fun σ' =>
        σ' = ⟨frame [n, U, a, fr, (n ^ (j + κ) : ℕ)], μ⟩ := by
  induction κ with
  | zero => exact fun j _ => Ends.skip rfl
  | succ κ ih =>
    intro j hb
    have hfits : (n : ℤ) ^ j * n ≤ lim.word :=
      le_trans (by exact_mod_cast hb (j + 1) (by omega)) hB
    have hpos : 0 ≤ (n : ℤ) ^ j * n := by positivity
    unfold hostPow
    -- Power := Power * Num
    light_set (n ^ (j + 1) : ℕ) using pow_succ
    rw [show j + (κ + 1) = j + 1 + κ by omega]
    exact (ih (j + 1) fun i hi => hb i (by omega)).mono (by simp; omega) fun _ h => h

/-- **The call of core**, with max U (n^κ) in Power. -/
theorem hostCall_ends {κ pCore : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (hC : CoreSpec lim P pCore T r) {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hok : (chNeed κ r x.N x.U).Ok lim fr d) :
    Ends lim P d (.call pCore [v Num, v Power +' v Power, v Addr, v Free] Num)
      ⟨frame [(x.N : ℤ), x.U, x.a, fr, (max x.U (x.N ^ κ) : ℕ)], μ⟩
      (8 + coreTime T x.N (2 * max x.U (x.N ^ κ))) fun σ' =>
        σ'.loc 0 = flag (ThreeSum (vecOf x.N x.X)) ∧ Kept μ σ'.mem fr := by
  have hword := hok.word
  have hdepth := hok.depth
  simp only [chNeed] at hword hdepth
  have hU := hpre.U_pos
  have hUle : x.U ≤ max x.U (x.N ^ κ) := le_max_left _ _
  have hle : max x.U (x.N ^ κ) ≤ x.N ^ κ + x.U := max_le (by omega) (by omega)
  have hcells : fr + (coreNeed r x.N (2 * max x.U (x.N ^ κ))).cells ≤ lim.space := hok.cells
  generalize max x.U (x.N ^ κ) = U' at *
  have hentries : AbsLe x.X U' := fun y hy => (hpre.le y hy).trans (by exact_mod_cast hUle)
  have hneed : (coreNeed r x.N (2 * U')).Ok lim fr (d + 1) :=
    { word := le_trans (by exact_mod_cast (by omega)) hword
      cells := hcells
      space := hok.space
      depth := by omega }
  -- Num := pCore(Num, Power + Power, Addr, Free)
  exact Ends.callTo (hC (d + 1) x.N U' x.a fr x.X μ hpre.len hentries hpre.seg hpre.below
    hpre.N_pos (hU.trans hUle) hneed) (fun res μ' h => h)

/-- **The host**: from the specification of core to what the task 3SUM asks. -/
theorem host_spec {κ pCore : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (hC : CoreSpec lim P pCore T r) {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hok : (chNeed κ r x.N x.U).Ok lim fr d) :
    Ends lim P d (hostBody κ pCore) ⟨frame [(x.N : ℤ), x.U, x.a, fr], μ⟩ (chTime κ T x.N x.U)
      fun σ' => σ'.loc 0 = flag (ThreeSum (vecOf x.N x.X)) ∧ Kept μ σ'.mem fr := by
  have hword := hok.word
  simp only [chNeed] at hword
  have hpow : 1 ≤ x.N ^ κ := Nat.one_le_pow _ _ hpre.N_pos
  have hB : ((x.N ^ κ : ℕ) : ℤ) ≤ lim.word := le_trans (by exact_mod_cast (by omega)) hword
  have hcall := hostCall_ends hC hpre hok
  unfold hostBody chTime
  -- Power := 1
  light_set (x.N ^ 0 : ℕ)
  -- the κ multiplications
  light_piece (hostPow_ends hB κ 0 fun i hi =>
    Nat.pow_le_pow_right hpre.N_pos (by omega)) with _ rfl
  rw [Nat.zero_add]
  -- if Power < Bound then Power := Bound
  refine Ends.iteThen (fun hc => ?_) (fun hc => ?_)
  · have hc' : x.N ^ κ < x.U := by exact_mod_cast (show ((x.N ^ κ : ℕ) : ℤ) < x.U from hc)
    rw [max_eq_left hc'.le] at hcall ⊢
    -- Power := Bound, and the call
    light_set x.U
    exact hcall.mono (by light_time) fun _ h => h
  · have hc' : ¬ x.N ^ κ < x.U := fun h => hc (show ((x.N ^ κ : ℕ) : ℤ) < x.U by exact_mod_cast h)
    rw [max_eq_right (not_lt.1 hc')] at hcall ⊢
    -- skip, and the call
    exact Ends.next _ (Ends.skip (T := 0) (hcall.mono (by light_time) fun _ h => h))

end Light.Sec3.ChanHe
