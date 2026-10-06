/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

/-!
# Horner's rule: the code of a string of decimal digits

horner(a, L) returns the number whose L decimal digits, most significant first, are in the cells
from a.  It is used to index an encoding by a leaf (Section 4.3: "The encodings are indexed by the
leaves (Section 2.4.1) […].  Thus reading the product at a leaf […] takes O(L) operations").

After i rounds the routine holds the number formed by the first i digits (`Horner.Inv`).  One more
digit multiplies it by ten and adds the digit (`ofDigitList_take_succ`), and it stays below 10^L
(`ofDigitList_lt`), which fits in a word.  `horner_spec` is the specification.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

namespace Horner

/-- The local variables of horner: the arguments (the address of the string and its length), the
level, and the number formed so far.  Local 0 also takes the result. -/
abbrev Str : ℕ := 0
@[inherit_doc Str] abbrev Result : ℕ := 0
@[inherit_doc Str] abbrev Len : ℕ := 1
@[inherit_doc Str] abbrev Level : ℕ := 2
@[inherit_doc Str] abbrev Acc : ℕ := 3

/-- Before round i the number formed by the first i digits has been computed.  The memory is not
changed. -/
def Inv (a : ℕ) (l : List ℕ) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [a, l.length, i, (ofDigitList 10 (l.take i) : ℕ)], μ⟩

end Horner

open Horner in
/-- horner(str, len): multiply by ten and add the next digit, from the most significant digit on. -/
def hornerBody : Stmt :=
  .set Level (k 0) ;;
  .set Acc (k 0) ;;
  .while (v Level <' v Len) (
    .set Acc (v Acc *' k 10 +' M (v Str +' v Level)) ;;
    .set Level (v Level +' k 1)) ;;
  .set Result (v Acc)

open Horner in
/-- **horner** returns the number with the given decimal digits, and leaves the memory as it
was. -/
theorem horner_spec {lim : Limits} {P : Program} (hP : P[Proc.horner]? = some hornerBody)
    (hs : Std lim) : HornerSpec lim P := by
  rintro a _ l μ hseg rfl hd ha hpow
  refine fun d _ => ⟨hornerBody, hP, ?_⟩
  light_facts hs
  -- every number formed on the way is below 10^L, so it fits in a word
  have hfits : ∀ i ≤ l.length, ((ofDigitList 10 (l.take i) : ℕ) : ℤ) < lim.word := fun i hi => by
    have hlt := ofDigitList_lt (b := 10) (l.take i) fun x hx => hd x (List.mem_of_mem_take hx)
    have hpow' : 10 ^ (l.take i).length ≤ 10 ^ l.length :=
      Nat.pow_le_pow_right (by norm_num) (List.length_take_le' _ _)
    exact lt_of_lt_of_le (by exact_mod_cast hlt.trans_le hpow') hpow
  unfold tHorner
  -- level := 0; acc := 0
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  -- while level < len
  refine Ends.next _ (Ends.whileBlock (Inv a l μ) l.length ?start ?round ?done (hT := le_rfl))
  case start => rfl
  case round =>
    rintro i _ hi rfl
    have hcell : μ (a + i) = (l.getD i 0 : ℕ) := hseg.read hi
    have hnext : ((ofDigitList 10 (l.take (i + 1)) : ℕ) : ℤ)
        = (ofDigitList 10 (l.take i) : ℕ) * 10 + (l.getD i 0 : ℕ) := by
      exact_mod_cast ofDigitList_take_succ 10 l hi
    have hfit := hfits (i + 1) hi
    generalize l.getD i 0 = digit at hcell hnext
    -- acc := acc * 10 + mem[str + level]; level := level + 1
    refine ⟨by light_side, by light_side, by light_side [hcell], ?_⟩
    simp [Horner.Inv, update_frame_setLocal, hcell, hnext]
  case done =>
    rintro _ rfl
    refine ⟨by light_side, by light_side, ?_⟩
    -- return acc
    light_set (ofDigitList 10 l : ℕ) using List.take_length
    exact ⟨rfl, rfl⟩

end Light.Sec4
