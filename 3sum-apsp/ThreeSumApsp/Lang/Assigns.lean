/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Logic

/-!
# A statement changes only the local variables that it assigns

`s.assigns` lists the local variables that the statement `s` assigns: the targets of its
assignments and the result variables of its calls.  A run of `s` leaves every other local variable
as it was (`Exec.loc_eq_of_notMem_assigns`), so every fact about `s` may be extended by "all other
locals are as before" (`Ends.keeping`).  A lemma about a piece of program text therefore speaks
about the memory and about the locals that the piece assigns, and about no other local.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The local variables that a statement assigns: the targets of its assignments and the result
variables of its calls. -/
@[simp] def Stmt.assigns : Stmt → List ℕ
  | .skip => []
  | .set x _ => [x]
  | .store _ _ => []
  | .seq s t => s.assigns ++ t.assigns
  | .ite _ s t => s.assigns ++ t.assigns
  | .while _ s => s.assigns
  | .call _ _ x => [x]

/-- A run leaves a local variable that the statement does not assign as it was. -/
theorem Exec.loc_eq_of_notMem_assigns {s : Stmt} {σ σ' : State} {c y : ℕ}
    (h : Exec lim P d s σ σ' c) (hy : y ∉ s.assigns) : σ'.loc y = σ.loc y := by
  induction h with
  | skip => rfl
  | set _ => exact Function.update_of_ne (by simpa using hy) _ _
  | store _ _ _ => rfl
  | seq _ _ ih₁ ih₂ =>
    exact (ih₂ fun h => hy (List.mem_append_right _ h)).trans
      (ih₁ fun h => hy (List.mem_append_left _ h))
  | iteTrue _ _ _ ih => exact ih fun h => hy (List.mem_append_left _ h)
  | iteFalse _ _ _ ih => exact ih fun h => hy (List.mem_append_right _ h)
  | whileFalse _ _ => rfl
  | whileTrue _ _ _ _ ih₁ ih₂ => exact (ih₂ hy).trans (ih₁ hy)
  | call _ _ _ _ _ => exact Function.update_of_ne (by simpa using hy) _ _

/-- **All other locals are as before.**  Whatever holds after a statement, it also holds that the
locals that the statement does not assign are unchanged. -/
theorem Ends.keeping {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) :
    Ends lim P d s σ T fun σ' => Q σ' ∧ ∀ y ∉ s.assigns, σ'.loc y = σ.loc y := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he, hc, hq, fun _ hy => he.loc_eq_of_notMem_assigns hy⟩

/-- **All other locals are as before**, for a list `xs` that contains the locals that the statement
assigns. -/
theorem Ends.keepingBut {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop}
    (h : Ends lim P d s σ T Q) (xs : List ℕ) (hxs : s.assigns ⊆ xs := by simp) :
    Ends lim P d s σ T fun σ' => Q σ' ∧ ∀ y ∉ xs, σ'.loc y = σ.loc y :=
  h.keeping.mono le_rfl fun _ hq => ⟨hq.1, fun y hy => hq.2 y fun hmem => hy (hxs hmem)⟩

end Light
