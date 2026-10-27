/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.TM.Frag

/-! A fragment written for few stacks, run on some of the stacks of a machine with more: stacks are
renamed along an injective
map, and the stacks outside its image are not touched. All stacks have one alphabet A. -/

@[expose] public section

namespace Groundwork.TM

open Turing

variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {A Λ σ : Type} (φ : K₁ → K₂)

/-- The statement on the renamed stacks. -/
def renK : TM2.Stmt (fun _ : K₁ => A) Λ σ → TM2.Stmt (fun _ : K₂ => A) Λ σ
  | .push k f q => .push (φ k) f (renK q)
  | .peek k f q => .peek (φ k) f (renK q)
  | .pop k f q => .pop (φ k) f (renK q)
  | .load f q => .load f (renK q)
  | .branch p q₁ q₂ => .branch p (renK q₁) (renK q₂)
  | .goto l => .goto l
  | .halt => .halt

/-- The fragment on the renamed stacks. -/
def Frag.ren (P : Frag (fun _ : K₁ => A) σ) : Frag (fun _ : K₂ => A) σ where
  Λ := P.Λ
  entry := P.entry
  m l := renK φ (P.m l)

variable {φ} in
/-- Stacks that agree along φ still agree after the same stack was overwritten on both sides. -/
private theorem agree_update (hφ : Function.Injective φ) {T : K₁ → List A} {S : K₂ → List A} (hS : ∀ k, S (φ k) = T k) (k : K₁)
    (w : List A) (k' : K₁) : Function.update S (φ k) w (φ k') = Function.update T k w k' := by
  by_cases h : k' = k
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne (hφ.ne h), hS]

variable {φ} in
/-- One statement: on stacks that agree along φ, the renamed statement ends at the same label with
the same local state, on
stacks that agree along φ, and it leaves the stacks outside the image of φ alone. -/
theorem stepAux_renK (hφ : Function.Injective φ) (q : TM2.Stmt (fun _ : K₁ => A) Λ σ) (v : σ) (T : K₁ → List A)
    (S : K₂ → List A) (hS : ∀ k, S (φ k) = T k) :
    (TM2.stepAux (renK φ q) v S).l = (TM2.stepAux q v T).l ∧ (TM2.stepAux (renK φ q) v S).var = (TM2.stepAux q v T).var ∧
      (∀ k, (TM2.stepAux (renK φ q) v S).stk (φ k) = (TM2.stepAux q v T).stk k) ∧
      ∀ k, (∀ a, φ a ≠ k) → (TM2.stepAux (renK φ q) v S).stk k = S k := by
  induction q generalizing v T S with
  | push k f q ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih v _ _ (agree_update hφ hS k (f v :: T k))
    simp only [renK, TM2.stepAux, hS]
    exact ⟨h1, h2, h3, fun k' hk' => (h4 k' hk').trans (Function.update_of_ne (hk' k).symm _ _)⟩
  | peek k f q ih =>
    simp only [renK, TM2.stepAux, hS]
    exact ih _ _ _ hS
  | pop k f q ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (f v (T k).head?) _ _ (agree_update hφ hS k (T k).tail)
    simp only [renK, TM2.stepAux, hS]
    exact ⟨h1, h2, h3, fun k' hk' => (h4 k' hk').trans (Function.update_of_ne (hk' k).symm _ _)⟩
  | load f q ih => exact ih _ _ _ hS
  | branch p q₁ q₂ ih₁ ih₂ =>
    simp only [renK, TM2.stepAux]
    cases p v
    · exact ih₂ _ _ _ hS
    · exact ih₁ _ _ _ hS
  | goto l => exact ⟨rfl, rfl, hS, fun _ _ => rfl⟩
  | halt => exact ⟨rfl, rfl, hS, fun _ _ => rfl⟩

variable {φ} in
/-- Runs of a machine become runs of the renamed machine. -/
theorem run_renK (hφ : Function.Injective φ) {M : Λ → TM2.Stmt (fun _ : K₁ => A) Λ σ} :
    ∀ {n : ℕ} {l l' : Option Λ} {v v' : σ} {T T' : K₁ → List A}, Run (TM2.step M) ⟨l, v, T⟩ n ⟨l', v', T'⟩ →
      ∀ {S S' : K₂ → List A}, (∀ k, S (φ k) = T k) → (∀ k, S' (φ k) = T' k) → (∀ k, (∀ a, φ a ≠ k) → S' k = S k) →
        Run (TM2.step fun l => renK φ (M l)) ⟨l, v, S⟩ n ⟨l', v', S'⟩
  | 0, _, _, _, _, _, _, h, S, S', hS, hS', ho => by
    cases h
    have : S = S' := by
      funext k
      by_cases hk : ∃ a, φ a = k
      · obtain ⟨a, rfl⟩ := hk; rw [hS, hS']
      · exact (ho k fun a ha => hk ⟨a, ha⟩).symm
    subst this; exact rfl
  | n + 1, none, _, _, _, _, _, ⟨c, hc, _⟩, _, _, _, _, _ => by simp [TM2.step] at hc
  | n + 1, some l, l', v, v', T, T', ⟨c, hc, h⟩, S, S', hS, hS', ho => by
    simp only [TM2.step, Option.some.injEq] at hc
    subst hc
    obtain ⟨h1, h2, h3, h4⟩ := stepAux_renK hφ (M l) v T S hS
    refine ⟨TM2.stepAux (renK φ (M l)) v S, rfl, ?_⟩
    have := run_renK hφ (S := (TM2.stepAux (renK φ (M l)) v S).stk) (S' := S') h h3 hS'
      fun k hk => (ho k hk).trans (h4 k hk).symm
    rw [← h1, ← h2] at this
    exact this

/-- If S and S' agree with T and T' along φ and with each other outside the image of φ, a run of P
from T to T' becomes a
run of `P.ren φ` from S to S' with the same number of steps. -/
theorem Frag.ren_runs (hφ : Function.Injective φ) {P : Frag (fun _ : K₁ => A) σ} {v : σ} {T T' : K₁ → List A} {n : ℕ}
    (h : P.Runs v T n T') {S S' : K₂ → List A} (hS : ∀ k, S (φ k) = T k) (hS' : ∀ k, S' (φ k) = T' k)
    (ho : ∀ k, (∀ a, φ a ≠ k) → S' k = S k) : (P.ren φ).Runs v S n S' :=
  run_renK hφ h hS hS' ho

end Groundwork.TM
