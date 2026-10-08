/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# Theorem 5 as a program: the report

Section 2.4.4: "and report, for each (I, J) ∈ W, the value at its output string."

The pruned recursions leave the values in the sorted order of the wanted positions.  report puts
them back in the order in which the positions were given: OUT[PERM[i]] := SV[i].  It is the
counterpart of gather, which reads through the permutation.  `report_entry` is one loop with the
invariant `ReportInv`; the places PERM[i] are different, so no value is overwritten
(`ReportInv.write`).
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-- report(w, perm, sv, out): OUT[PERM[i]] := SV[i] for all i < w.  π is the list in PERM, a list of
w different indices below w; the output lies below PERM and SV. -/
def ReportSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (w perm sv out : ℕ) (π : List ℕ) (vals : List ℤ) (μ : ℕ → ℤ),
    SegN μ perm π → Seg μ sv vals → π.length = w → vals.length = w → π.Nodup →
    (∀ i ∈ π, i < w) → out + w ≤ perm → out + w ≤ sv → perm + w ≤ lim.space →
    sv + w ≤ lim.space →
    ∀ d, d ≤ lim.depth → Meets lim P pReport d [w, perm, sv, out] μ (c * (w + 1)) fun _ μ' =>
      (∀ i < w, μ' (out + π.getD i 0) = vals.getD i 0) ∧ SameOutside μ μ' out w

namespace ReportLocal

/-- The number w of wanted positions. -/
abbrev LEN : ℕ := 0
/-- The permutation, sorted order to given order. -/
abbrev PERM : ℕ := 1
/-- The values, in sorted order. -/
abbrev VALS : ℕ := 2
/-- The output. -/
abbrev OUT : ℕ := 3
/-- The place i in the sorted order. -/
abbrev POS : ℕ := 4

end ReportLocal

open ReportLocal in
/-- report(w, perm, sv, out): OUT[PERM[i]] := VALS[i] for i < w, where VALS is the array at sv. -/
def reportBody : Stmt :=
  .for POS (v LEN) (.store (v OUT +' M (v PERM +' v POS)) (M (v VALS +' v POS)))

variable {lim : Limits} {P : Program} {c i : ℕ} {μ μ' : ℕ → ℤ}

/-! ## The report -/

/-- The first i values have been put in their places, and only the output has changed. -/
structure ReportInv (w out : ℕ) (π : List ℕ) (vals : List ℤ) (μ : ℕ → ℤ) (i : ℕ) (μ' : ℕ → ℤ) :
    Prop where
  done : ∀ j < i, μ' (out + π.getD j 0) = vals.getD j 0
  rest : SameOutside μ μ' out w

/-- One more value is put in its place; the places are different, so no earlier value is lost. -/
theorem ReportInv.write {w out : ℕ} {π : List ℕ} {vals : List ℤ}
    (inv : ReportInv w out π vals μ i μ') (hlen : π.length = w) (hnodup : π.Nodup)
    (hlt : ∀ x ∈ π, x < w) (hi : i < w) :
    ReportInv w out π vals μ (i + 1)
      (Function.update μ' (out + π.getD i 0) (vals.getD i 0)) := by
  have hplace : π.getD i 0 < w := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact hlt _ (List.getElem_mem _)
  refine ⟨fun j hj => ?_, inv.rest.update ⟨by omega, by omega⟩ _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hlt' | rfl
  · have hne : π.getD j 0 ≠ π.getD i 0 := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
      exact fun h => by have := (List.Nodup.getElem_inj_iff hnodup).1 h; omega
    rw [Function.update_of_ne (by omega)]
    exact inv.done j hlt'
  · exact Function.update_self _ _ _

/-- **report** does what `ReportSpec` says: OUT[π[i]] = SV[i] for i < w, and no cell outside the
output has changed, in at most 20 (w + 1) steps. -/
theorem report_entry (std : Std lim) (hP : P[pReport]? = some reportBody) (hc : 20 ≤ c) :
    ReportSpec lim P c := by
  intro w perm sv out π vals μ hπ hvals hlenπ hlenv hnodup hlt hperm hsv hpermle hsvle d _
  have hw := std.space_le
  have h100 := std.const_le
  refine .mono_const (.of_body hP ?_) hc
  -- for i < w
  refine Ends.forFrame (ReportInv w out π vals μ) w ?start ?round ?done
  case start => exact ⟨fun _ h => absurd h (by omega), .refl⟩
  case round =>
    intro i μ' hi inv
    have hplace : π.getD i 0 < w := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact hlt _ (List.getElem_mem _)
    have hreadP : μ' (perm + i) = (π.getD i 0 : ℕ) := by
      rw [inv.rest _ (by omega), hπ i (by simpa [hlenπ] using hi), List.getElem_map,
        List.getD_eq_getElem _ _ (by omega)]
    have hreadV : μ' (sv + i) = vals.getD i 0 := by
      rw [inv.rest _ (by omega), hvals.getD (by omega) 0]
    simp only [List.getD_eq_getElem?_getD] at hplace hreadP
    -- mem[out + mem[perm + i]] := mem[sv + i]
    light_store (out + π.getD i 0) (vals.getD i 0) using hreadP, hreadV
    exact ⟨rfl, inv.write hlenπ hnodup hlt hi⟩
  case done => exact fun μ' inv => ⟨inv.done, inv.rest⟩

end Light.Sec2
