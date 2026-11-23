/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Uni.CmpU

/-!
# The sorting loop: specification
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Nc.Uni

open Finset

section Blocks

variable {Γ : Type*}

/-- Words without the letter a, followed by a, are cut in one way. -/
theorem cut_inj {a : Γ} {w w' x x' : List Γ} (hw : a ∉ w) (hw' : a ∉ w') (h : w ++ a :: x = w' ++ a :: x') :
    w = w' ∧ x = x' := by
  induction w generalizing w' with
  | nil =>
    rcases w' with _ | ⟨b, w'⟩
    · simpa using h
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by simp [h.1]) hw'
  | cons b w ih =>
    rcases w' with _ | ⟨b', w'⟩
    · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (by simp [h.1]) hw
    · simp only [List.cons_append, List.cons.injEq, List.mem_cons, not_or] at h hw hw'
      obtain ⟨h1, h2⟩ := ih hw.2 hw'.2 h.2
      exact ⟨by rw [h.1, h1], h2⟩

/-- Words, each followed by the letter a. -/
def blocks (a : Γ) (ws : List (List Γ)) : List Γ := ws.flatMap fun w => w ++ [a]

theorem blocks_cons (a : Γ) (w : List Γ) (ws : List (List Γ)) : blocks a (w :: ws) = w ++ a :: blocks a ws := by
  simp [blocks]

theorem blocks_append (a : Γ) (ws ws' : List (List Γ)) : blocks a (ws ++ ws') = blocks a ws ++ blocks a ws' := by
  simp [blocks]

theorem blocks_inj {a : Γ} {ws ws' : List (List Γ)} (h : ∀ w ∈ ws, a ∉ w) (h' : ∀ w ∈ ws', a ∉ w)
    (e : blocks a ws = blocks a ws') : ws = ws' := by
  induction ws generalizing ws' with
  | nil =>
    rcases ws' with _ | ⟨w', ws'⟩
    · rfl
    · rw [blocks_cons] at e
      simp [blocks] at e
  | cons w ws ih =>
    rcases ws' with _ | ⟨w', ws'⟩
    · rw [blocks_cons] at e
      simp [blocks] at e
    · rw [blocks_cons, blocks_cons] at e
      obtain ⟨h1, h2⟩ := cut_inj (h w (by simp)) (h' w' (by simp)) e
      rw [h1, ih (fun w hw => h w (by simp [hw])) (fun w hw => h' w (by simp [hw])) h2]

theorem length_blocks (a : Γ) (ws : List (List Γ)) : (blocks a ws).length = (ws.map List.length).sum + ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [blocks_cons, List.length_append, List.length_cons, ih, List.map_cons, List.sum_cons, List.length_cons]
    omega

end Blocks

variable {A : Type*} [CommRing A] {M K : Type} [Fintype M] [DecidableEq M] [Fintype K] [DecidableEq K]

theorem rw'_inj {f f' : Bool} {w w' : List (Option (Bl K))} {u v : List (Sy M K)}
    (h : rw' f w ++ u = rw' f' w' ++ v) : f = f' ∧ w = w' ∧ u = v := by
  simp only [rw', List.cons_append, List.cons.injEq, Sy.flag.injEq, List.append_assoc, List.singleton_append] at h
  obtain ⟨rfl, h⟩ := h
  have hd : ∀ w : List (Option (Bl K)), (Sy.dot : Sy M K) ∉ w.map ol := by
    intro w hw
    rw [List.mem_map] at hw
    obtain ⟨o, -, ho⟩ := hw
    exact ol_ne_dot o ho
  obtain ⟨h1, h2⟩ := cut_inj (hd w) (hd w') h
  exact ⟨rfl, List.map_injective_iff.2 ol_inj h1, h2⟩

/-- Lists of records. -/
def encW (l : List (Bool × List (Option (Bl K)))) : List (Sy M K) := l.flatMap fun r => rw' r.1 r.2

theorem encW_inj : Function.Injective (encW : List (Bool × List (Option (Bl K))) → List (Sy M K)) := by
  refine flatMap_inj (fun r => by simp [rw']) ?_
  rintro ⟨f, w⟩ ⟨f', w'⟩ u v h
  obtain ⟨rfl, rfl, -⟩ := rw'_inj h
  rfl

theorem bar_rw' (f : Bool) (w : List (Option (Bl K))) : (Sy.bar : Sy M K) ∉ rw' f w := by
  simp only [rw', List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil, or_false, not_or]
  refine ⟨by simp, ?_, by simp⟩
  rintro ⟨o, -, ho⟩
  exact ol_ne_bar o ho

theorem bar_encW (l : List (Bool × List (Option (Bl K)))) : (Sy.bar : Sy M K) ∉ encW l := by
  rw [encW, List.mem_flatMap]
  rintro ⟨r, -, h⟩
  exact bar_rw' _ _ h

/-- What a pass of the distribution reads. -/
def dIn (d : List (Dr K)) : List (Bool × List (Option (Bl K))) := d.map fun d => (d.1, some d.2.1 :: d.2.2)

/-- What it writes to the bucket b. -/
def dOut (b : Bl K) (d : List (Dr K)) : List (Bool × List (Option (Bl K))) :=
  (d.filter fun d => d.2.1 = b).map fun d => (d.1, d.2.2 ++ [some d.2.1])

/-- What the last reading reads. -/
def fIn (l : List (Rk K)) : List (Bool × List (Option (Bl K))) := l.map fun r => (r.1, none :: r.2.map some)

/-- What it writes. -/
def fOut (l : List (Rk K)) : List (Bool × List (Option (Bl K))) := l.map fun r => (r.1, r.2.map some)

/-- What a collection writes. -/
noncomputable def cOut (m : Bl K → List (NB M K)) : List (Sy M K) := ((bsl K).flatMap m).map Subtype.val

/-- Runs of the sort. -/
abbrev XU (M K : Type) := List (Ps M K) × List (Rk K) × XG (List (Bl K))

/-- Emissions of the sort. -/
noncomputable def emU (x : XU M K) : Zc K → List (Sy M K) := fun z =>
  (x.1.flatMap fun p => emPs p z) ++ (emFi x.2.1 z ++ emCm x.2.2 z)

/-- Dimension of the sort. -/
def dimU (m k : ℕ) : ℕ := (dimPs m k + 1) + ((14 + 3 + (k * 7 + 1) + 7 + 1 + 3) + dimCm k)

theorem runs_U : Runs (dimU (Fintype.card (Sy M K)) (Fintype.card (Bl K)))
    (emU : XU M K → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have h := ((runs_ps (A := A) (M := M) (K := K)).kstar fun p => ⟨lsT, by
    intro h
    have := congrArg List.length h
    simp [emPs, on, barSet] at this⟩).mul ((runs_fi (A := A) (M := M) (K := K)).mul (runs_cm (A := A) (M := M) (K := K)))
  refine h.congr (Equiv.refl _) (fun y z => rfl) fun y => ?_
  simp

section Values

theorem mem_barSet_lsT : (lsT : Zc K) ∈ barSet := by simp [barSet]

theorem mem_barSet_bk (b : Bl K) : (.tp (.bk b) false : Zc K) ∈ barSet := by simp [barSet]

theorem not_barSet {z : Zc K} (h1 : z ≠ lsT) (h2 : ∀ b, z ≠ .tp (.bk b) false) : z ∉ barSet := by
  simp only [barSet, mem_insert, mem_image, mem_univ, true_and, not_or, not_exists]
  exact ⟨h1, fun b e => h2 b e.symm⟩

theorem emCo_lsF (m : Bl K → List (NB M K)) : emCo m lsF = cOut m ++ [Sy.bar] := by
  unfold emCo cOut
  have h1 : ∀ i : Fin (Fintype.card (Bl K)), on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF}
      ((m ((Fintype.equivFin (Bl K)).symm i)).map Subtype.val) (lsF : Zc K) ++
      on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true} [(Sy.bar : Sy M K)] lsF =
      (m ((Fintype.equivFin (Bl K)).symm i)).map Subtype.val := by
    intro i
    simp [on]
  simp only [h1]
  rw [bsl, List.map_flatMap, List.flatMap_def, List.map_ofFn]
  simp only [on, mem_singleton, if_true]
  rfl

theorem emCo_bk_true (m : Bl K → List (NB M K)) (b : Bl K) :
    emCo m (.tp (.bk b) true) = (m b).map Subtype.val ++ [Sy.bar] := by
  unfold emCo
  rw [flatten_ofFn_single (Fintype.equivFin (Bl K) b)]
  · simp [on]
  · intro k hk
    have : b ≠ (Fintype.equivFin (Bl K)).symm k := by
      rintro rfl
      simp at hk
    simp [on, this]

theorem emCo_other (m : Bl K → List (NB M K)) {z : Zc K} (h1 : z ≠ lsF) (h2 : ∀ b, z ≠ .tp (.bk b) true) :
    emCo m z = [] := by
  unfold emCo
  rw [flatten_ofFn_nil]
  · simp [on, h1]
  · intro i
    simp [on, h1, h2]

theorem emPs_lsT (p : Ps M K) : emPs p lsT = encW (dIn p.1) ++ [Sy.bar] := by
  have h1 : emCo p.2 (lsT : Zc K) = [] := emCo_other _ (by simp) (by simp)
  have h2 : ∀ d : Dr K, (emDr d lsT : List (Sy M K)) = rw' d.1 (some d.2.1 :: d.2.2) := by
    intro d; simp [emDr, on]
  unfold emPs
  rw [h1]
  simp only [h2, on, mem_barSet_lsT, if_true, List.append_nil]
  rw [encW, dIn, List.flatMap_map]

theorem emPs_lsF (p : Ps M K) : emPs p lsF = cOut p.2 ++ [Sy.bar] := by
  have h1 : (lsF : Zc K) ∉ barSet := not_barSet (by simp) (by simp)
  have h2 : ∀ d : Dr K, (emDr d lsF : List (Sy M K)) = [] := by
    intro d; simp [emDr, on]
  unfold emPs
  rw [emCo_lsF]
  simp [h2, on, h1]

theorem emPs_bk_false (p : Ps M K) (b : Bl K) : emPs p (.tp (.bk b) false) = encW (dOut b p.1) ++ [Sy.bar] := by
  have h1 : emCo p.2 (.tp (.bk b) false : Zc K) = [] := emCo_other _ (by simp) (by simp)
  have h2 : ∀ d : Dr K, (emDr d (.tp (.bk b) false) : List (Sy M K)) =
      if d.2.1 = b then rw' d.1 (d.2.2 ++ [some d.2.1]) else [] := by
    intro d
    by_cases h : d.2.1 = b
    · subst h; simp [emDr, on]
    · simp [emDr, on, h, Ne.symm h]
  have h3 : ∀ l : List (Dr K), (l.flatMap fun d => (if d.2.1 = b then rw' d.1 (d.2.2 ++ [some d.2.1]) else [] : List (Sy M K))) =
      (l.filter fun d => d.2.1 = b).flatMap fun d => rw' d.1 (d.2.2 ++ [some d.2.1]) := by
    intro l
    induction l with
    | nil => rfl
    | cons d l ih =>
      rw [List.flatMap_cons, ih, List.filter_cons]
      by_cases h : d.2.1 = b <;> simp [h]
  unfold emPs
  rw [h1]
  simp only [h2, on, mem_barSet_bk, if_true, List.append_nil]
  rw [h3, encW, dOut, List.flatMap_map]

theorem emPs_bk_true (p : Ps M K) (b : Bl K) : emPs p (.tp (.bk b) true) = (p.2 b).map Subtype.val ++ [Sy.bar] := by
  have h1 : (.tp (.bk b) true : Zc K) ∉ barSet := not_barSet (by simp) (by simp)
  have h2 : ∀ d : Dr K, (emDr d (.tp (.bk b) true) : List (Sy M K)) = [] := by
    intro d; simp [emDr, on]
  unfold emPs
  rw [emCo_bk_true]
  simp [h2, on, h1]

theorem emPs_other (p : Ps M K) {z : Zc K} (h1 : z ≠ lsT) (h2 : z ≠ lsF) (h3 : ∀ b s, z ≠ .tp (.bk b) s) : emPs p z = [] := by
  have e1 : emCo p.2 z = [] := emCo_other _ h2 fun b => h3 b true
  have e2 : ∀ d : Dr K, (emDr d z : List (Sy M K)) = [] := by
    intro d; simp [emDr, on, h1, h3]
  have e3 : z ∉ (barSet : Finset (Zc K)) := not_barSet h1 fun b => h3 b false
  unfold emPs
  rw [e1]
  simp [e2, on, e3]

theorem emFi_lsT (l : List (Rk K)) : (emFi l lsT : List (Sy M K)) = encW (fIn l) ++ [Sy.bar] := by
  simp [emFi, on, encW, fIn, List.flatMap_map]

theorem emFi_cm (l : List (Rk K)) (k : Bool) : (emFi l (.tp (.cm k) false) : List (Sy M K)) = encW (fOut l) := by
  cases k <;> simp [emFi, on, encW, fOut, List.flatMap_map]

theorem emFi_other (l : List (Rk K)) {z : Zc K} (h1 : z ≠ lsT) (h2 : ∀ k, z ≠ .tp (.cm k) false) :
    (emFi l z : List (Sy M K)) = [] := by
  simp [emFi, on, h1, h2]

theorem rk_flatMap (l : List (Rk K)) : (l.flatMap rk : List (Sy M K)) = encW (fOut l) := by
  rw [encW, fOut, List.flatMap_map]; rfl

theorem emCm_true (y : XG (List (Bl K))) (k : Bool) :
    (emCm y (.tp (.cm k) true) : List (Sy M K)) = encW (fOut (if k then QlG y else PlG y)) := by
  cases k <;> simp [emCm, on, ← rk_flatMap]

theorem emCm_other (y : XG (List (Bl K))) {z : Zc K} (h : ∀ k, z ≠ .tp (.cm k) true) :
    (emCm y z : List (Sy M K)) = [] := by
  simp [emCm, on, h]

theorem emU_lsT (x : XU M K) : emU x lsT = blocks Sy.bar (x.1.map (fun p => encW (dIn p.1)) ++ [encW (fIn x.2.1)]) := by
  unfold emU
  rw [emFi_lsT, emCm_other _ (by simp), blocks_append]
  simp only [emPs_lsT]
  simp [blocks, List.flatMap_map]

theorem emU_lsF (x : XU M K) : emU x lsF = blocks Sy.bar (x.1.map fun p => cOut p.2) := by
  unfold emU
  rw [emFi_other _ (by simp) (by simp), emCm_other _ (by simp)]
  simp only [emPs_lsF]
  simp [blocks, List.flatMap_map]

theorem emU_bk_false (x : XU M K) (b : Bl K) :
    emU x (.tp (.bk b) false) = blocks Sy.bar (x.1.map fun p => encW (dOut b p.1)) := by
  unfold emU
  rw [emFi_other _ (by simp) (by simp), emCm_other _ (by simp)]
  simp only [emPs_bk_false]
  simp [blocks, List.flatMap_map]

theorem emU_bk_true (x : XU M K) (b : Bl K) :
    emU x (.tp (.bk b) true) = blocks Sy.bar (x.1.map fun p => (p.2 b).map Subtype.val) := by
  unfold emU
  rw [emFi_other _ (by simp) (by simp), emCm_other _ (by simp)]
  simp only [emPs_bk_true]
  simp [blocks, List.flatMap_map]

theorem emU_cm_false (x : XU M K) (k : Bool) : emU x (.tp (.cm k) false) = encW (fOut x.2.1) := by
  have h : ∀ p : Ps M K, emPs p (.tp (.cm k) false) = [] := fun p => emPs_other p (by simp) (by simp) (by simp)
  unfold emU
  rw [emFi_cm, emCm_other _ (by simp)]
  simp [h]

theorem emU_cm_true (x : XU M K) (k : Bool) :
    emU x (.tp (.cm k) true) = encW (fOut (if k then QlG x.2.2 else PlG x.2.2)) := by
  have h : ∀ p : Ps M K, emPs p (.tp (.cm k) true) = [] := fun p => emPs_other p (by simp) (by simp) (by simp)
  unfold emU
  rw [emFi_other _ (by simp) (by simp), emCm_true]
  simp [h]

theorem emU_other (x : XU M K) {z : Zc K} (h1 : z ≠ lsT) (h2 : z ≠ lsF) (h3 : ∀ b s, z ≠ .tp (.bk b) s)
    (h4 : ∀ k s, z ≠ .tp (.cm k) s) : emU x z = [] := by
  have h : ∀ p : Ps M K, emPs p z = [] := fun p => emPs_other p h1 h2 h3
  unfold emU
  rw [emFi_other _ h1 (fun k => h4 k false), emCm_other _ (fun k => h4 k true)]
  simp [h]

end Values

end Nc.Uni
