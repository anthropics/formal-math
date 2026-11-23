/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Lists

/-!
# Cuts one after the other
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- The product of the plain sums of a list of instances. -/
noncomputable def pvs (θ : List Bool → A) (o : Tree) : A := (o.toList.map (pv θ)).prod

/-- A program `G` that cuts plain sums of `τ` steps on instances of size `s` into at most `P` pieces of `τ'` steps on
instances of size `s'`, in `t` steps. -/
def CutD (θ : List Bool → A) (τ s τ' s' P t : ℕ) (G : Tree) : Prop :=
  ∀ z, z.size ≤ s → ∃ Q, Does θ (Fm.ofTree G) z Q t ∧
    (∀ q ∈ Q, q.2.toList.length ≤ P ∧ ∀ y ∈ q.2.toList, y.size ≤ s') ∧
    (Plain θ τ z → (∀ q ∈ Q, ∀ y ∈ q.2.toList, Plain θ τ' y) ∧ pv θ z = wsum Q (pvs θ))

/-- A cut gives the program of the cut hypothesis. -/
theorem CutD.cutProg {H v τ s P t : ℕ} {G : Tree} (h : CutD θ τ s (v ^ H) (v ^ (H - 32)) P t G) (hG : G.size ≤ v ^ H)
    (ht : t * v ^ 24 ≤ τ) (hP : P * v ^ H ≤ τ * v ^ 2) : CutProg θ H v τ s G := by
  refine ⟨hG, fun z hz => ?_, fun z hz hp => ?_⟩
  · obtain ⟨Q, hD, hQ, -⟩ := h z hz
    refine ⟨hD.hl, fun r hr => ?_⟩
    obtain ⟨h1, h2, q, hq, h3⟩ := hD.evl.1 r hr
    obtain ⟨h4, h5⟩ := hQ q hq
    rw [← h3]
    exact ⟨h1, (Nat.mul_le_mul_right _ h2).trans ht, (Nat.mul_le_mul_right _ h4).trans hP, h5⟩
  · obtain ⟨Q, hD, hQ, hv⟩ := h z hz
    obtain ⟨h1, h2⟩ := hv hp
    refine ⟨fun r hr y hy => ?_, ?_⟩
    · obtain ⟨-, -, q, hq, h3⟩ := hD.evl.1 r hr
      rw [← h3] at hy
      exact h1 q hq y hy
    · rw [h2, ← hD.evl.2 (pvs θ)]
      rfl

/-- One more cut for every element: the argument is (element, list of pieces so far). -/
def stepC (G : Tree) : Fm := lett (.cons (app G (.hd .id)) (.tl .id)) (appF (.hd .id) (.tl .id))

/-- First `G`, then `G'` on every piece. -/
def compC (G G' : Tree) : Fm := lett (app G .id) (foldF (stepC G') (.quote .nil) .id)

theorem wsum_foldW_pvs {f : Tree → Tree → List (A × Tree)} {xs : List Tree} {Inv : List Tree → Tree → Prop}
    (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ → (∀ q ∈ f x σ, Inv ys q.2) ∧ wsum (f x σ) (pvs θ) = pv θ x * pvs θ σ)
    {σ : Tree} (hσ : Inv xs σ) : wsum (foldW f xs σ) (pvs θ) = (xs.map (pv θ)).prod * pvs θ σ := by
  induction xs generalizing σ with
  | nil => simp [foldW]
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := h x xs σ List.mem_cons_self hσ
    rw [foldW, wsum_bindW, wsum_congr (φ' := fun o => (xs.map (pv θ)).prod * pvs θ o) fun q hq =>
      ih (fun y ys σ hy => h y ys σ (List.mem_cons_of_mem _ hy)) (h1 q hq)]
    have h3 : wsum (f x σ) (fun o => (xs.map (pv θ)).prod * pvs θ o) = (xs.map (pv θ)).prod * wsum (f x σ) (pvs θ) := by
      unfold wsum
      rw [← List.sum_map_mul_left]
      congr 1
      exact List.map_congr_left fun q _ => by ring
    rw [h3, h2, List.map_cons, List.prod_cons]
    ring

theorem mem_foldW {f : Tree → Tree → List (A × Tree)} {xs : List Tree} {Inv : List Tree → Tree → Prop}
    (h : ∀ x ys σ, x ∈ xs → Inv (x :: ys) σ → ∀ q ∈ f x σ, Inv ys q.2) {σ : Tree} (hσ : Inv xs σ) :
    ∀ q ∈ foldW f xs σ, Inv [] q.2 := by
  induction xs generalizing σ with
  | nil =>
    intro q hq
    simp only [foldW, List.mem_singleton] at hq
    subst hq
    exact hσ
  | cons x xs ih =>
    intro q hq
    obtain ⟨q', hq', r, hr, h1, -⟩ := mem_bindW hq
    rw [h1]
    exact ih (fun y ys σ hy => h y ys σ (List.mem_cons_of_mem _ hy)) (h x xs σ List.mem_cons_self hσ q' hq') r hr

/-- **Paper: Theorem thm:cut, composition of cuts.** "Composing the programs: the next one is run on every piece in
the list ... The sum formulas compose." -/
theorem _root_.Paper.thm_cut_compose {τ s τ₁ s₁ P₁ t₁ τ₂ s₂ P₂ t₂ : ℕ} {G₁ G₂ : Tree} (h₁ : CutD θ τ s τ₁ s₁ P₁ t₁ G₁)
    (h₂ : CutD θ τ₁ s₁ τ₂ s₂ P₂ t₂ G₂) :
    CutD θ τ s τ₂ s₂ (P₁ * P₂) (t₁ + P₁ * (t₂ + 62 * P₂ + 110) + 100) (compC G₁ G₂).code := by
  intro z hz
  obtain ⟨Q₁, hD₁, hQ₁, hv₁⟩ := h₁ z hz
  choose! R hR using h₂
  -- one step
  let f : Tree → Tree → List (A × Tree) := fun x σ =>
    (R x).map fun q => (q.1, listT (q.2.toList ++ σ.toList))
  have hstep : ∀ x σ, x.size ≤ s₁ → Does θ (stepC G₂) (.cons x σ) (f x σ) (t₂ + 62 * P₂ + 70) := by
    intro x σ hx
    obtain ⟨hD, hq, -⟩ := hR x hx
    have e1 : Does θ (app G₂ (.hd .id)) (.cons x σ) (R x) (2 + t₂ + 2) := by
      have := Does.app (p := G₂) (R := fun _ => R x) (Gives.id (θ := θ) (.cons x σ)).hd (d := t₂) (by
        intro q hq
        rw [List.mem_singleton] at hq
        subst hq
        exact hD)
      simpa [bindW] using this
    have e2 := Does.cons e1 (Gives.id (θ := θ) (.cons x σ)).tl
    have e3 := Gives.after (G := appF (.hd .id) (.tl .id)) (f := fun o => listT (o.hd.toList ++ o.tl.toList))
      (d := 62 * P₂ + 50) e2 (by
      intro q hq'
      simp only [List.mem_flatMap, List.map_cons, List.map_nil, List.mem_singleton] at hq'
      obtain ⟨q1, hq1, rfl⟩ := hq'
      have h1 : Gives θ (.hd .id) (.cons q1.2 σ) (listT q1.2.toList) 2 := by
        rw [listT_toList]; exact (Gives.id _).hd
      have h2 : Gives θ (.tl .id) (.cons q1.2 σ) (listT σ.toList) 2 := by
        rw [listT_toList]; exact (Gives.id _).tl
      refine (appF_gives h1 h2).mono ?_
      have := Nat.mul_le_mul_right 62 (hq q1 hq1).1
      omega)
    refine (e3.congr ?_ fun φ => ?_).mono (by omega)
    · intro q hq'
      simp only [List.mem_map, List.mem_flatMap, List.map_cons, List.map_nil, List.mem_singleton] at hq'
      obtain ⟨q1, ⟨q2, hq2, rfl⟩, rfl⟩ := hq'
      exact ⟨_, List.mem_map.2 ⟨q2, hq2, rfl⟩, rfl⟩
    · simp only [f, wsum, List.map_map, List.map_cons, List.map_nil, mul_one, flatMap_single,
        Function.comp_def, hd_cons, tl_cons]
  -- the fold
  have hfold : ∀ q ∈ Q₁, Does θ (foldF (stepC G₂) (.quote .nil) .id) q.2 (foldW f q.2.toList .nil)
      (P₁ * (t₂ + 62 * P₂ + 100) + 30) := by
    intro q hq
    have hl : Gives θ .id q.2 (listT q.2.toList) 1 := by rw [listT_toList]; exact Gives.id _
    have := foldF_does (f := f) (Inv := fun ys _ => ∀ y ∈ ys, y.size ≤ s₁) (d := fun _ => t₂ + 62 * P₂ + 70)
      (Gives.quote (θ := θ) .nil q.2) hl (fun x ys σ _ hI => ⟨hstep x σ (hI x List.mem_cons_self), fun _ _ y hy =>
        hI y (List.mem_cons_of_mem _ hy)⟩) (hQ₁ q hq).2
    refine this.mono ?_
    rw [List.map_const', List.sum_replicate, smul_eq_mul, show t₂ + 62 * P₂ + 70 + 30 = t₂ + 62 * P₂ + 100 by omega]
    have := Nat.mul_le_mul_right (t₂ + 62 * P₂ + 100) (hQ₁ q hq).1
    omega
  have hDz : Does θ (app G₁ .id) z Q₁ (1 + t₁ + 2) := by
    have := Does.app (p := G₁) (R := fun _ => Q₁) (Gives.id (θ := θ) z) (d := t₁) (by
      intro q hq
      rw [List.mem_singleton] at hq
      subst hq
      exact hD₁)
    simpa [bindW] using this
  refine ⟨bindW Q₁ fun o => foldW f o.toList .nil, ?_, ?_, ?_⟩
  · rw [Fm.ofTree_code]
    refine (hDz.lett (R := fun o => foldW f o.toList .nil) hfold).mono ?_
    have : P₁ * (t₂ + 62 * P₂ + 100) ≤ P₁ * (t₂ + 62 * P₂ + 110) := Nat.mul_le_mul_left _ (by omega)
    omega
  · intro p hp
    obtain ⟨q, hq, r, hr, h1, -⟩ := mem_bindW hp
    rw [h1]
    have hinv : ∀ r ∈ foldW f q.2.toList .nil, (r.2.toList.length + ([] : List Tree).length * P₂ ≤ P₁ * P₂ ∧
        ∀ y ∈ r.2.toList, y.size ≤ s₂) ∧ ∀ y ∈ ([] : List Tree), y.size ≤ s₁ := by
      refine mem_foldW (f := f) (Inv := fun ys σ => (σ.toList.length + ys.length * P₂ ≤ P₁ * P₂ ∧
        ∀ y ∈ σ.toList, y.size ≤ s₂) ∧ ∀ y ∈ ys, y.size ≤ s₁) ?_ ?_
      · rintro x ys σ - ⟨⟨a1, a2⟩, a3⟩ q' hq'
        simp only [f, List.mem_map] at hq'
        obtain ⟨q2, hq2, rfl⟩ := hq'
        obtain ⟨-, b1, -⟩ := hR x (a3 x List.mem_cons_self)
        obtain ⟨b2, b3⟩ := b1 q2 hq2
        refine ⟨⟨?_, ?_⟩, fun y hy => a3 y (List.mem_cons_of_mem _ hy)⟩
        · simp only [toList_listT, List.length_append]
          simp only [List.length_cons, add_mul, one_mul] at a1
          omega
        · intro y hy
          rw [toList_listT, List.mem_append] at hy
          rcases hy with hy | hy
          · exact b3 y hy
          · exact a2 y hy
      · refine ⟨⟨?_, by simp [toList]⟩, (hQ₁ q hq).2⟩
        have := Nat.mul_le_mul_right P₂ (hQ₁ q hq).1
        simpa [toList] using this
    have := (hinv r hr).1
    simpa using this
  · intro hp
    obtain ⟨hp1, hv⟩ := hv₁ hp
    have hpiece : ∀ q ∈ Q₁, wsum (foldW f q.2.toList .nil) (pvs θ) = pvs θ q.2 := by
      intro q hq
      rw [wsum_foldW_pvs (θ := θ) (Inv := fun ys _ => ∀ y ∈ ys, y.size ≤ s₁ ∧ Plain θ τ₁ y)]
      · simp [pvs, toList]
      · intro x ys σ _ hI
        refine ⟨fun _ _ y hy => hI y (List.mem_cons_of_mem _ hy), ?_⟩
        obtain ⟨hx, hpx⟩ := hI x List.mem_cons_self
        obtain ⟨-, -, b⟩ := hR x hx
        obtain ⟨-, b2⟩ := b hpx
        rw [b2]
        simp only [f, wsum, List.map_map, Function.comp_def, pvs, toList_listT, List.map_append, List.prod_append]
        rw [← List.sum_map_mul_right]
        congr 1
        exact List.map_congr_left fun q _ => by ring
      · exact fun y hy => ⟨(hQ₁ q hq).2 y hy, hp1 q hq y hy⟩
    refine ⟨?_, ?_⟩
    · intro p hp' y hy
      obtain ⟨q, hq, r, hr, h1, -⟩ := mem_bindW hp'
      rw [h1] at hy
      have hinv : ∀ r ∈ foldW f q.2.toList .nil, (∀ y ∈ r.2.toList, Plain θ τ₂ y) ∧
          ∀ y ∈ ([] : List Tree), y.size ≤ s₁ ∧ Plain θ τ₁ y := by
        refine mem_foldW (f := f) (Inv := fun ys σ => (∀ y ∈ σ.toList, Plain θ τ₂ y) ∧
          ∀ y ∈ ys, y.size ≤ s₁ ∧ Plain θ τ₁ y) ?_ ?_
        · rintro x ys σ - ⟨a1, a2⟩ q' hq'
          simp only [f, List.mem_map] at hq'
          obtain ⟨q2, hq2, rfl⟩ := hq'
          obtain ⟨hx, hpx⟩ := a2 x List.mem_cons_self
          obtain ⟨-, -, b⟩ := hR x hx
          obtain ⟨b1, -⟩ := b hpx
          refine ⟨fun y hy => ?_, fun y hy => a2 y (List.mem_cons_of_mem _ hy)⟩
          rw [toList_listT, List.mem_append] at hy
          rcases hy with hy | hy
          · exact b1 q2 hq2 y hy
          · exact a1 y hy
        · exact ⟨by simp [toList], fun y hy => ⟨(hQ₁ q hq).2 y hy, hp1 q hq y hy⟩⟩
      exact (hinv r hr).1 y hy
    · rw [hv, wsum_bindW]
      exact wsum_congr fun q hq => (hpiece q hq).symm

theorem size_compC (G G' : Tree) : (compC G G').code.size ≤ G.size + 3 * G'.size + 3000 := by
  simp only [compC, stepC, appF, foldF, foldB, lett, app, Fm.code, Tree.size, size_num]
  omega

end NS1
