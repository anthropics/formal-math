/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.Facts

/-!
# The program GROUP: the theorem

For a fixed automaton and a fixed list of roles of laws there is one formula GROUP. Its plain sum at the script of a group
is the value of the group; accepting runs exist only if the numbers of units are bounded.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q] {c : ℕ}

/-- The time of GROUP at a script. -/
def grpTime (bT bub : List Bool) (l : List Ins) : ℕ :=
  (bT.length + 1) * (bval bT + 1) + (bub.length + 1) * (bval bub + 1) + (l.map (insCost (bval bT) (bval bub))).sum + l.length

/-- **GROUP.** -/
theorem exists_group (mu : Letter S Unit Γ → Matrix Q Q A) (cb : Option Γ → Fin c → Bool)
    (kinds : List (Σ L : G.Law A, L.Ro)) (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q')
    (htab : ∀ z ∈ kinds, ∀ i y h, ∃ e : WE, e.val θ = z.1.tab z.2 i y h) :
    ∃ (GROUP : Fm) (κ : ℕ), ∀ {A' K E U0 U1 cap : ℕ} {Gr : Type} [DecidableEq Gr] [Fintype Gr]
      {M : Sys A (K + K + A') E} (P : G.Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
      (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
      (o : M.N → Fin U1) (grp : Fin (K + K + A') → Gr) (g : Gr) (key : Cell M U0 U1 → List Bool)
      (dkey : Fin (K + K) × Fin U0 → List Bool) (tg : M.R → ℕ) (bT bub : List Bool)
      (b : G.Uid (K + K) U0 M.N U1 → UW (bval bub)),
      Function.Injective (Sum.elim key dkey) → 0 < bval bub → P.Ok cap → (∀ κ, (x κ).length ≤ bval bT) →
      (∀ s p, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) → (∀ r, kinds[tg r]? = some ⟨M.kind r.1, r.2⟩) →
      Plain θ (κ * grpTime bT bub (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b))
        (.cons GROUP.code (scriptT bT bub (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b))) ∧
      pv θ (.cons GROUP.code (scriptT bT bub (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b))) =
        G.grpVal mu (bval bT) cb P q x ρ n o grp g b ∧
      (evl θ GROUP (scriptT bT bub (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b)) ≠ [] →
        (∀ p, grp (Fin.castAdd A' p) = g → ∑ b, ((n p b : ℕ) + n b p) ≤
          2 * ((bval bT + (K + K) * (Fintype.card S + 1)) * c / bval bub + (K + K))) ∧
        ∀ r : M.R, grp (M.rp r) = g → ∃ ι : Fin (P.num n o r.1 * bval bub) → (M.kind r.1).I,
          ∀ ν : (M.kind r.1).CnAt r.2,
            (o ⟨r.1, ν.1⟩ : ℕ) = (∑ k, ((M.kind r.1).lam + (M.kind r.1).len (ι k) ν.1)) / bval bub) := by
  obtain ⟨F, κ, hF⟩ := ex_group (S := S) (θ := θ) mu cb kinds (by simp [sepOf])
  refine ⟨F, κ, fun {A' K E U0 U1 cap Gr} _ _ {M} P q x ρ n o grp g key dkey tg bT bub b hkey hub hP hx hρ hkind => ?_⟩
  have h1 := hF bT bub (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b) (insOk_script hkind b)
  have htab' : ∀ (r : M.R) i y h, ∃ e : WE, e.val θ = (M.kind r.1).tab r.2 i y h := fun r =>
    htab ⟨M.kind r.1, r.2⟩ (List.mem_of_getElem? (hkind r))
  have h2 := sumL_script (cb := cb) (kinds := kinds) (tg := tg) hkey hub hP hmu hx hρ hkind htab' (q := q) (o := o) (n := n)
    (grp := grp) (g := g) b
  obtain ⟨p1, p2⟩ := h1.plain
  refine ⟨p1, ?_, fun hacc => ?_⟩
  · rw [p2, ← h2, sumL, List.map_map]
    congr 1
    exact List.map_congr_left fun z _ => by simp
  · have hne : scriptSem (S := S) θ mu cb kinds (bval bT) (bval bub)
        (script (fun z => (qn Q z : ℕ)) cb P q x ρ n o grp g key dkey tg b) .nil ≠ [] := by
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil _ hacc
      obtain ⟨-, -, z, hz, -⟩ := h1.evl.1 r hr
      obtain ⟨z', hz', -⟩ := List.mem_map.1 hz
      exact List.ne_nil_of_mem hz'
    exact ⟨fun p hp => count_of_accept hub hx hρ hne hp, fun r hr => outcome_of_accept hub hkind hne hr⟩

end Nc.Grp
