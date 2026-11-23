/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.SumSeg
import Nc.Grp.SumPut

/-!
# The sum over what a base party does
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {A' K E U0 U1 ub c T : ℕ} {Gr : Type} [DecidableEq Gr]
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}
  {F : Type} [CommRing F] {M : Sys F (K + K + A') E} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}
  {key : Cell M U0 U1 → List Bool} {dkey : Fin (K + K) × Fin U0 → List Bool}

/-- The trie has the contents `σ`. -/
def Rep (ub : ℕ) (key : Cell M U0 U1 → List Bool) (t : Tree) (σ : Cell M U0 U1 → UW ub) : Prop :=
  TOk ub t ∧ ∀ c, tget (key c) t = ofBits (uwBits (σ c))

/-- All tapes, as an equivalence. -/
noncomputable def tapeEquiv (S : Type) [Fintype S] [DecidableEq S] : Fin (nT S) ≃ Option S :=
  List.Nodup.getEquivOfForallMemList (tapes S) (Finset.nodup_toList _) fun s => Finset.mem_toList.2 (mem_univ s)

theorem tapeEquiv_apply (i : Fin (nT S)) : tapeEquiv S i = (tapes S).get i := rfl

theorem joined_tapes (X : Option S → List Γ) :
    joined (code cb) (sepOf cb) (fun i : Fin (nT S) => X ((tapes S).get i)) = strOf cb X := by
  have h1 : (List.ofFn fun i : Fin (nT S) => (X ((tapes S).get i)).flatMap (code cb) ++ sepOf cb) =
      (tapes S).map fun s => (X s).flatMap (code cb) ++ sepOf cb := by
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp
  rw [joined, h1, strOf, joinSeg, bitsOf, ← List.flatMap_def, List.flatMap_assoc]
  refine List.flatMap_congr fun s _ => ?_
  rw [List.flatMap_append, List.flatMap_map]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

theorem flags_rowOk {m : ℕ} {d : RowData m} (hd : d.1 = false → d.2.1 ≤ d.2.2) (X : Fin m → List Γ) :
    (∀ b, okFlag (rowFlag d b) (decide (X b ≠ [])) = true) ↔ RowOk d X := by
  unfold RowOk
  by_cases h : d.1 = true
  · rw [if_pos h]
    refine forall_congr' fun b => ?_
    simp [rowFlag, h, okFlag]
  · rw [if_neg h]
    have h' : d.1 = false := by simpa using h
    have hle := hd h'
    constructor
    · intro hb
      refine ⟨?_, ?_, fun b hXb => ?_⟩
      · have := hb d.2.1
        simpa [rowFlag, h', okFlag] using this
      · have := hb d.2.2
        simpa [rowFlag, h', okFlag] using this
      · have := hb b
        by_cases e1 : b = d.2.1 ∨ b = d.2.2
        · rcases e1 with rfl | rfl
          · exact ⟨le_rfl, hle⟩
          · exact ⟨hle, le_rfl⟩
        · by_cases e2 : d.2.1 ≤ b ∧ b ≤ d.2.2
          · exact e2
          · simp [rowFlag, h', e1, e2, okFlag, hXb] at this
    · rintro ⟨h1, h2, h3⟩ b
      by_cases e1 : b = d.2.1 ∨ b = d.2.2
      · have : X b ≠ [] := by
          rcases e1 with rfl | rfl
          · exact h1
          · exact h2
        simp [rowFlag, h', e1, okFlag, this]
      · by_cases e2 : d.2.1 ≤ b ∧ b ≤ d.2.2
        · simp [rowFlag, h', e1, e2, okFlag]
        · have : X b = [] := by
            by_contra hne
            exact e2 (h3 b hne)
          simp [rowFlag, h', e1, e2, okFlag, this]

/-- Two functions with values in a finite set. -/
theorem sum_pi_pi_coe {ι κ β : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [DecidableEq β]
    (s : Finset β) (f : (ι → κ → β) → A) :
    ∑ x ∈ Fintype.piFinset fun _ : ι => Fintype.piFinset fun _ : κ => s, f x =
      ∑ x : ι → κ → s, f fun i j => (x i j : β) := by
  symm
  refine Finset.sum_bij (fun (x : ι → κ → s) _ => fun i j => (x i j : β)) ?_ ?_ ?_ ?_
  · intro x _
    exact Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 fun j => (x i j).2
  · intro x _ y _ h
    funext i j
    exact Subtype.ext (congrFun (congrFun h i) j)
  · intro y hy
    exact ⟨fun i j => ⟨y i j, Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hy i) j⟩, Finset.mem_univ _, rfl⟩
  · intro x _
    rfl

/-- The words of a base party, with their tapes. -/
abbrev Segs (S Γ : Type) [Fintype Γ] [DecidableEq Γ] (m T : ℕ) := Option S → Fin m → Wt Γ T

/-- As words. -/
def Segs.words {m : ℕ} (X : Segs S Γ m T) : Option S → Fin m → List Γ := fun s b => (X s b : List Γ)

/-- The keys of the units that are written. -/
noncomputable def kRl (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (key : Cell M U0 U1 → List Bool) (p b : Fin (K + K)) :
    List (List Bool) := ((List.finRange U0).filter fun k => k.1 < (n p b).1).map fun k =>
  key (Fin.castAdd A' p, .init p b k)

/-- The keys of the units that are read. -/
noncomputable def kCl (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (key : Cell M U0 U1 → List Bool)
    (dkey : Fin (K + K) × Fin U0 → List Bool) (p b : Fin (K + K)) :
    List (List Bool) := ((List.finRange U0).filter fun k => k.1 < (n b p).1).map fun k =>
  if b = p then dkey (p, k) else key (Fin.castAdd A' p, .init b p k)

/-- The list of what is written. -/
noncomputable def PR (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (key : Cell M U0 U1 → List Bool)
    (cb : Option Γ → Fin c → Bool) (p : Fin (K + K)) (R : Option S → Fin (K + K) → List Γ) :
    List (List (List Bool) × List Bool) := List.ofFn fun b => (kRl n key p b, strOf cb fun s => R s b)

/-- The list of what is read. -/
noncomputable def PC (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (key : Cell M U0 U1 → List Bool)
    (dkey : Fin (K + K) × Fin U0 → List Bool) (cb : Option Γ → Fin c → Bool) (p : Fin (K + K))
    (C : Option S → Fin (K + K) → List Γ) :
    List (List (List Bool) × List Bool) := List.ofFn fun b => (kCl n key dkey p b, strOf cb fun s => C s b)

theorem sum_segs_equiv {m : ℕ} (f : (Fin (nT S) → Fin m → Wt Γ T) → A) :
    ∑ X, f X = ∑ X : Segs S Γ m T, f fun i => X ((tapes S).get i) :=
  Fintype.sum_equiv ((tapeEquiv S).arrowCongr (Equiv.refl _)) _ _ fun X => by
    congr 1
    funext i
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id]
    rw [← tapeEquiv_apply, Equiv.symm_apply_apply]

theorem forall_tapes {p : Option S → Prop} : (∀ i : Fin (nT S), p ((tapes S).get i)) ↔ ∀ s, p s := by
  constructor
  · intro h s
    obtain ⟨i, rfl⟩ := (tapeEquiv S).surjective s
    exact h i
  · intro h i
    exact h _

open Classical in
/-- **Cutting and writing, as a sum.** -/
theorem sumL_pack (hub : 0 < ub) (hK : 0 < K + K) {p : Fin (K + K)}
    (hρ : ∀ s, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) {wl rl : Option S → List Γ}
    (hwl : ∀ s, (wl s).length ≤ T) (hrl : ∀ s, (rl s).length ≤ T) {out : Outs S}
    (h1 : ∀ i, out (Fin.castAdd (nT S) i) = ((wl ((tapes S).get i)).map (code cb)).reverse)
    (h2 : ∀ i, out (Fin.natAdd (nT S) i) = ((rl ((tapes S).get i)).map (code cb)).reverse) (t : Tree) (Ψ : Tree → A) :
    sumL (packSem A (sepOf cb) ub (bodyOf ρ n key dkey p) out t) Ψ =
      ∑ R : Segs S Γ (K + K) T, ∑ C : Segs S Γ (K + K) T,
        if (∀ s, cat (R.words s) = wl s) ∧ (∀ s, cat (C.words s) = rl s) ∧ (∀ s, RowOk (ρ s p) (R.words s)) ∧
          (∀ b, ucount ub (strOf cb fun s => R.words s b) = n p b) ∧
          (∀ b, ucount ub (strOf cb fun s => C.words s b) = n b p) then
          Ψ (putsAll ub (PC n key dkey cb p C.words) (putsAll ub (PR n key cb p R.words) t)) else 0 := by
  have hm : (bodyOf ρ n key dkey p).kR.length = K + K := by simp [bodyOf]
  have hrep : List.replicate (K + K) [true] = (List.ofFn fun _ : Fin (K + K) => [true]).reverse := by
    rw [List.ofFn_const, List.reverse_replicate]
  have hflags : ∀ i : Fin (nT S), (bodyOf ρ n key dkey p).flags.getD i.rev [] =
      (List.ofFn fun b => rowFlag (ρ ((tapes S).get i.rev) p) b).reverse := by
    intro i
    have hlt : (i.rev : ℕ) < (bodyOf ρ n key dkey p).flags.length := by
      simp only [bodyOf, List.length_map]
      exact i.rev.2
    rw [List.getD_eq_getElem _ _ hlt]
    simp only [bodyOf, List.getElem_map]
    rfl
  have eR : itemsR (bodyOf ρ n key dkey p).flags out = List.ofFn fun i : Fin (nT S) =>
      ((List.ofFn fun b => rowFlag (ρ ((tapes S).get i.rev) p) b).reverse,
        ((wl ((tapes S).get i.rev)).map (code cb)).reverse) := by
    rw [itemsR]
    congr 1
    funext i
    rw [hflags, h1]
  have eC : itemsC (K + K) out = List.ofFn fun i : Fin (nT S) =>
      ((List.ofFn fun _ : Fin (K + K) => 2).reverse, ((rl ((tapes S).get i.rev)).map (code cb)).reverse) := by
    rw [itemsC]
    congr 1
    funext i
    rw [h2, List.ofFn_const, List.reverse_replicate]
  have hlenR : ∀ b, (kRl n key p b).length = n p b := by
    intro b
    rw [kRl, List.length_map, filter_finRange (by have := (n p b).2; omega), List.length_ofFn]
  have hlenC : ∀ b, (kCl n key dkey p b).length = n b p := by
    intro b
    rw [kCl, List.length_map, filter_finRange (by have := (n b p).2; omega), List.length_ofFn]
  rw [packSem, hm, hrep, sumL_bindL, eR,
    sumL_segs (sepOf cb) hK (code cb) T (fun i b => rowFlag (ρ ((tapes S).get i) p) b) (fun i => wl ((tapes S).get i))
      (fun i => hwl _), sum_segs_equiv]
  refine Finset.sum_congr rfl fun R _ => ?_
  have cR : (∀ i : Fin (nT S), CutOk (fun b => rowFlag (ρ ((tapes S).get i) p) b) (wl ((tapes S).get i))
      fun b => (R ((tapes S).get i) b : List Γ)) ↔ (∀ s, cat (R.words s) = wl s) ∧ ∀ s, RowOk (ρ s p) (R.words s) := by
    rw [forall_tapes (p := fun s => CutOk (fun b => rowFlag (ρ s p) b) (wl s) fun b => (R s b : List Γ)), ← forall_and]
    refine forall_congr' fun s => ?_
    unfold CutOk
    rw [flags_rowOk (hρ s)]
    rfl
  by_cases hR : (∀ s, cat (R.words s) = wl s) ∧ ∀ s, RowOk (ρ s p) (R.words s)
  swap
  · rw [if_neg fun h => hR (cR.1 h)]
    symm
    refine Finset.sum_eq_zero fun C _ => if_neg fun h => hR ⟨h.1, h.2.2.1⟩
  rw [if_pos (cR.2 hR), List.reverse_reverse, sumL_bindL]
  have sR : (List.ofFn fun b => joined (code cb) (sepOf cb) (fun i : Fin (nT S) => (R ((tapes S).get i) b : List Γ)) ++ [true]) =
      (PR n key cb p R.words).map fun z => z.2 ++ [true] := by
    rw [PR, List.map_ofFn]
    congr 1
    funext b
    show _ = strOf cb (fun s => R.words s b) ++ [true]
    rw [← joined_tapes]
    rfl
  have kR : (bodyOf ρ n key dkey p).kR = (PR n key cb p R.words).map Prod.fst := by
    rw [PR, List.map_ofFn]
    rfl
  rw [sR, kR, putsL_eq hub]
  have cR2 : (∀ z ∈ PR n key cb p R.words, ucount ub z.2 = z.1.length) ↔
      ∀ b, ucount ub (strOf cb fun s => R.words s b) = n p b := by
    rw [PR, List.forall_mem_ofFn_iff]
    refine forall_congr' fun b => ?_
    rw [hlenR]
  by_cases hR2 : ∀ b, ucount ub (strOf cb fun s => R.words s b) = n p b
  swap
  · rw [if_neg fun h => hR2 (cR2.1 h)]
    symm
    refine Finset.sum_eq_zero fun C _ => if_neg fun h => hR2 h.2.2.2.1
  rw [if_pos (cR2.2 hR2)]
  simp only [encT, List.map_cons, List.map_nil, sumL_single]
  rw [sumL_bindL, eC, sumL_segs (sepOf cb) hK (code cb) T (fun _ _ => 2) (fun i => rl ((tapes S).get i))
    (fun i => hrl _), sum_segs_equiv]
  refine Finset.sum_congr rfl fun C _ => ?_
  have cC : (∀ i : Fin (nT S), CutOk (fun _ => 2) (rl ((tapes S).get i)) fun b => (C ((tapes S).get i) b : List Γ)) ↔
      ∀ s, cat (C.words s) = rl s := by
    rw [forall_tapes (p := fun s => CutOk (fun _ => 2) (rl s) fun b => (C s b : List Γ))]
    refine forall_congr' fun s => ?_
    unfold CutOk
    refine and_iff_left fun b => ?_
    simp [okFlag]
  by_cases hC : ∀ s, cat (C.words s) = rl s
  swap
  · rw [if_neg fun h => hC (cC.1 h), if_neg fun h => hC h.2.1]
  rw [if_pos (cC.2 hC), List.reverse_reverse]
  have sC : (List.ofFn fun b => joined (code cb) (sepOf cb) (fun i : Fin (nT S) => (C ((tapes S).get i) b : List Γ)) ++ [true]) =
      (PC n key dkey cb p C.words).map fun z => z.2 ++ [true] := by
    rw [PC, List.map_ofFn]
    congr 1
    funext b
    show _ = strOf cb (fun s => C.words s b) ++ [true]
    rw [← joined_tapes]
    rfl
  have kC : (bodyOf ρ n key dkey p).kC = (PC n key dkey cb p C.words).map Prod.fst := by
    rw [PC, List.map_ofFn]
    rfl
  rw [sC, kC, putsL_eq hub]
  have cC2 : (∀ z ∈ PC n key dkey cb p C.words, ucount ub z.2 = z.1.length) ↔
      ∀ b, ucount ub (strOf cb fun s => C.words s b) = n b p := by
    rw [PC, List.forall_mem_ofFn_iff]
    refine forall_congr' fun b => ?_
    rw [hlenC]
  by_cases hC2 : ∀ b, ucount ub (strOf cb fun s => C.words s b) = n b p
  · rw [if_pos (cC2.2 hC2), if_pos ⟨hR.1, hC, hR.2, hR2, hC2⟩]
    simp only [List.map_cons, List.map_nil, sumL_single]
  · rw [if_neg fun h => hC2 (cC2.1 h), if_neg fun h => hC2 h.2.2.2.2]
    rfl

end Nc.Grp
