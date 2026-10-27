/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.HalfTabSpec
public import ClauseBound.Boson.KF
public import ClauseBound.Boson.Half

/-! # The tables of the parts of a^μ by weight: correctness

If the list of monomials is in order (`FlatOK`), all parts of μ are at most W and the pad has at
least `padKF` entries, then the table number w of `tabKF` holds the matrices of
(the part of weight w of a^μ)[r] (`tabKF_rep`), and `topF` computes the entries of
`ClauseBound.Boson.topK` (`topF_eq`). The proof goes part by part through μ: one round of the
program is the
recursion `KF_cons`, and the bound `abs_KF_le` on the entries shows that the pad does not cut the
tables off. -/

public section

namespace ClauseBound.Inst.Half

open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson

namespace HalfTabKF

/-- A sum over 1, …, n as a sum over 0, …, n − 1. -/
theorem sum_Icc_one (f : ℕ → ℤ) (n : ℕ) : ∑ j ∈ Icc 1 n, f j = ∑ i ∈ range n, f (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- The member number w of a list made from 0, …, h. -/
theorem getD_map_range {h w : ℕ} (hw : w ≤ h) (f : ℕ → List ℤ) : ((List.range (h + 1)).map f).getD w [] = f w := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; omega), List.getElem_map, List.getElem_range]

/-- `padKF` grows with the sum and with the number of parts. -/
theorem padKF_mono (W Δ h : ℕ) {s s' L L' : ℕ} (hs : s ≤ s') (hL : L ≤ L') : padKF W Δ h s L ≤ padKF W Δ h s' L' := by
  unfold padKF
  gcongr

/-- h + 1 tables that have the entries of the families F 0, …, F h, bounded by 2^B, are not cut off
by a pad of the length given, and hold these families. -/
theorem rep_cap {pad : U} {W h B : ℕ} {flat : List (List ℕ)} (hf : FlatOK W flat) {G : ℕ → List ℕ → List ℕ → ℤ} {F : ℕ → ℤ → Ker}
    (hG : ∀ w ≤ h, ∀ π ∈ flat, ∀ σ ∈ flat, G w π σ = F w ((π.sum : ℤ) - σ.sum) π σ)
    (hB : ∀ w r (π σ : Multiset ℕ), π.sum ≤ W → σ.sum ≤ W → |F w r π σ| ≤ 2 ^ B)
    (hp : (h + 1) * (flat.length ^ 2 * (3 * B + 10) + 4) + 2 ≤ pad.length) :
    ∀ w ≤ h, Rep flat ((cap pad [] ((List.range (h + 1)).map fun w => tab flat (G w))).getD w []) (F w) := by
  have hlen : len ((List.range (h + 1)).map fun w => tab flat (G w)) ≤ pad.length := by
    refine le_trans ?_ hp
    have h1 := Lists.len_list_le ((List.range (h + 1)).map fun w => tab flat (G w)) (flat.length ^ 2 * (3 * B + 10) + 4) fun T hT => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hT
      have hw' : w ≤ h := Nat.lt_succ_iff.1 (List.mem_range.1 hw)
      have := len_tab_le (flat := flat) (f := G w) (B := B) fun π hπ σ hσ => by
        rw [hG w hw' π hπ σ hσ]
        exact hB w _ _ _ (by rw [Multiset.sum_coe]; exact hf.sum_le π hπ) (by rw [Multiset.sum_coe]; exact hf.sum_le σ hσ)
      omega
    rwa [List.length_map, List.length_range] at h1
  intro w hw
  rw [cap_eq hlen, getD_map_range hw]
  exact rep_tab (hG w hw)

/-- The tables at the start, as tables of functions. -/
theorem kfInit_eq (h : ℕ) (flat : List (List ℕ)) :
    kfInit h flat = (List.range (h + 1)).map fun w => tab flat fun π σ => if w = 0 then (if π = σ then 1 else 0) else 0 := by
  unfold kfInit oneT
  refine List.map_congr_left fun w _ => ?_
  split_ifs <;> rfl

/-- One round of the program is the recursion for one more factor. -/
theorem kfStep_entry {W h n w : ℕ} {flat : List (List ℕ)} {S : List (List ℤ)} {μ : List ℕ} (hf : FlatOK W flat) (hn : n ≤ W)
    (hS : ∀ w ≤ h, Rep flat (S.getD w []) (KF μ w)) (hw : w ≤ h) {π σ : List ℕ} (hπ : π ∈ flat) (hσ : σ ∈ flat) :
    (sumR (min n W) fun j =>
      if j + 1 ≤ w then sgnZ ((n - 1 : ℕ) : ℤ) * chooseZ (n : ℤ) (j + 1) * nopE W (j + 1) flat (S.getD (w - (j + 1)) []) π σ else 0) =
      KF (n :: μ) w ((π.sum : ℤ) - σ.sum) π σ := by
  rw [KF_cons, sum_Icc_one, sumR_eq, min_eq_left hn]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j + 1 ≤ W := (Nat.succ_le_of_lt (mem_range.1 hj)).trans hn
  refine if_congr Iff.rfl ?_ rfl
  rw [sgnZ_eq, ClauseBound.Rec.ite_even_natCast, chooseZ_eq, Ring.choose_natCast, nopE_eq hf hj' (hS _ ((Nat.sub_le _ _).trans hw)) hπ hσ]

end HalfTabKF

open HalfTabKF

/-- The table number w holds the matrices of (the part of weight w of a^μ)[r]. -/
theorem tabKF_rep {pad : U} {W h : ℕ} {flat : List (List ℕ)} {μ : List ℕ} (hW : 1 ≤ W) (hf : FlatOK W flat) (hμ : ∀ n ∈ μ, n ≤ W)
    (hp : padKF W flat.length h μ.sum μ.length ≤ pad.length) : ∀ w ≤ h, Rep flat ((tabKF pad W flat h μ).getD w []) (ClauseBound.Boson.KF μ w) := by
  induction μ with
  | nil =>
    have e : tabKF pad W flat h [] = cap pad [] (kfInit h flat) := rfl
    rw [e, kfInit_eq]
    refine rep_cap (B := 0 + (4 * W + 1) * 0) hf (fun w _ π hπ σ hσ => ?_) (fun w r π σ h1 h2 => abs_KF_le hW [] hμ w r h1 h2) hp
    rw [KF_nil]
    refine if_congr Iff.rfl ?_ rfl
    have h0 := oneT_rep hf π hπ σ hσ
    rwa [oneT, lookT_tab _ hπ hσ] at h0
  | cons n μ ih =>
    have e : tabKF pad W flat h (n :: μ) = cap pad [] (kfStep W h n flat (tabKF pad W flat h μ)) := by
      unfold tabKF
      rw [List.reverse_cons, List.foldl_append]
      rfl
    have hS := ih (fun m hm => hμ m (List.mem_cons_of_mem _ hm))
      ((padKF_mono W flat.length h (by rw [List.sum_cons]; omega) (by rw [List.length_cons]; omega)).trans hp)
    rw [e]
    exact rep_cap hf (fun w hw π hπ σ hσ => kfStep_entry hf (hμ n List.mem_cons_self) hS hw hπ hσ)
      (fun w r π σ h1 h2 => abs_KF_le hW (n :: μ) hμ w r h1 h2) hp

/-- The program for the first factor of a term of a piece computes it. -/
theorem topF_eq {pad : U} {W h : ℕ} {flat : List (List ℕ)} {μ : List ℕ} (hW : 1 ≤ W) (hf : FlatOK W flat) (hμ : ∀ n ∈ μ, n ≤ W) (hs : μ.sum = h)
    (hp : padKF W flat.length h μ.sum μ.length ≤ pad.length) (i : ℕ) (r : ℤ) {π σ : List ℕ} (hπ : π ∈ flat) (hσ : σ ∈ flat) :
    topF pad W flat h μ i r π σ = ClauseBound.Boson.topK μ h i r ↑π ↑σ := by
  unfold topF topK
  split_ifs with hr
  · rw [sum_aFam_eq μ (fun w => ((w + h).choose i : ℤ)), hs, sgnZ_eq, ClauseBound.Rec.ite_even_natCast, sumR_eq]
    congr 1
    refine sum_congr rfl fun w hw => ?_
    rw [tabKF_rep hW hf hμ hp w (Nat.lt_succ_iff.1 (mem_range.1 hw)) π hπ σ hσ, chooseZ_eq, ← Nat.cast_add, Ring.choose_natCast, hr]
  · have h0 : ∀ c : ℤ × List ℕ, op c.2 r (π : Multiset ℕ) (σ : Multiset ℕ) = 0 := fun c => by
      by_contra hne
      have := op_grade hne
      rw [Multiset.sum_coe, Multiset.sum_coe] at this
      exact hr (by omega)
    simp [h0]

end ClauseBound.Inst.Half
