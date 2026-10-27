/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
public import PaddedDescent.F.LenList

/-! # The descent through all levels computes Z (`StBrute` and `StD`)

`descend pad sched I` turns one instance into the list of all its descendants at the bottom level,
and `bruteF` evaluates each by brute force. Here: if
the pad is long enough (`Fits`), the sum of the results is the sum Z of the instance I (`stD`). What
one level does (`StE`) and that a well-formed
instance has a short word (`StT3b`) are taken as hypotheses; other files prove them. `Fits.head`
says that the current work list fits under the pad. -/

public section

namespace PaddedDescent.F

open Groundwork Groundwork.Prog Finset Lists

/-! ### The bottom: brute force under fuel computes Z -/

/-- `StBrute`: brute force computes the sum Z of an instance if the pad has a unit for every
labelling. -/
theorem stBrute : StBrute := by
  intro pad K I h
  unfold bruteF zval Inst.ZW
  rw [sumF_eq h, ← sum_blocks_pairs K I.1.length [] fun Λ => ∏ v, instOf (K := K) I.2 v (star Λ v), ← sum_toWord]
  refine sum_congr rfl fun y _ => ?_
  rw [prodL_eq, prod_range]
  refine prod_congr rfl fun v _ => ?_
  rw [query0_eq]
  rfl

/-! ### The budget of the work list -/

namespace Descend

end Descend

open Descend

/-- The current work list fits under the pad. -/
theorem Fits.head {F : ℕ} : ∀ {sched : List Lvl} {Kup Λ B cnt : ℕ}, Fits F Kup Λ B cnt sched → cnt * instLen Kup Λ B + 2 ≤ F
  | [], _, _, _, _, h => h.1
  | _ :: _, _, _, _, _, h => h.1

/-! ### `StD` -/

/-- `StD` for a work list: the steps of the schedule followed by brute force do not change the sum
of Z over the list. -/
theorem Descend.descend_list (h3 : StT3b) (hE : StE) {pad : U} : ∀ (sched : List Lvl) {Kup Λ B cnt : ℕ} (w : List PInst),
    Chain Kup sched → Fits pad.length Kup Λ B cnt sched → w.length ≤ cnt → (∀ I ∈ w, WF Kup Λ B I) →
    ((sched.foldl (fun w L => cap pad [] (w.flatMap (expand pad L))) w).map (bruteF pad 256)).sum = (w.map (zval Kup)).sum
  | [], Kup, Λ, B, cnt, w, hC, hF, _, hw => by
    have hK : Kup = 256 := hC
    subst hK
    rw [List.foldl_nil]
    refine congrArg List.sum (List.map_congr_left fun I hI => stBrute pad 256 I (le_trans ?_ hF.2))
    exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ (hw I hI).lam_le)
  | L :: r, Kup, Λ, B, cnt, w, hC, hF, hc, hw => by
    obtain ⟨hK, h2, h8, hC'⟩ := hC
    obtain ⟨-, hB, hF'⟩ := hF
    subst hK
    have hE' := fun I (hI : I ∈ w) => hE pad L Λ B I h2 h8 (hw I hI) hB
    have hlen : (w.flatMap (expand pad L)).length ≤ cnt * (Λ + 1) ^ nRect L.2.length :=
      (length_flatMap_le w _ _ fun I hI => (hE' I hI).2.2).trans (Nat.mul_le_mul_right _ hc)
    have hWF : ∀ J ∈ w.flatMap (expand pad L),
        WF L.1.length (lamNext L.1.length L.2.length Λ) (bNext L.1.length L.2.length Λ B) J := by
      intro J hJ
      obtain ⟨I, hI, hJ'⟩ := List.mem_flatMap.1 hJ
      exact (hE' I hI).2.1 J hJ'
    have hfit : len (w.flatMap (expand pad L)) ≤ pad.length :=
      (len_list_le' _ _ hlen fun J hJ => h3 _ _ _ J (hWF J hJ)).trans hF'.head
    rw [List.foldl_cons, cap_eq hfit, Descend.descend_list h3 hE r _ hC' hF' hlen hWF, sum_map_flatMap]
    exact congrArg List.sum (List.map_congr_left fun I hI => (hE' I hI).1)

/-- `StD`: all levels and then brute force compute the sum Z of the instance at the top. -/
theorem stD (h3 : StT3b) (hE : StE) : StD := by
  intro pad sched Kup Λ B I hC hF hI
  have hw : ∀ J ∈ [I], WF Kup Λ B J := fun J hJ => by rw [List.mem_singleton.1 hJ]; exact hI
  have hfit : len [I] ≤ pad.length := (len_list_le [I] _ fun J hJ => h3 _ _ _ J (hw J hJ)).trans hF.head
  unfold descend
  rw [cap_eq hfit, descend_list h3 hE sched [I] hC hF le_rfl hw]
  simp

end PaddedDescent.F
