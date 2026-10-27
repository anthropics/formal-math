/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.ViaGrouping.SatPsiDefs
public import Eight.ViaGrouping.Bridge
public import ToTuring.Poly.Count
public import ToTuring.Poly.Comb
import all StepMachines.Math.SatNet
import all StepMachines.Prog.CountNet
import all StepMachines.Prog.Count
import Mathlib.Tactic

/-! # Section 6, «Clusters, occurrences, equality tests»: Ψ_{a,b} of the network of Φ, and «Definition 2 holds»

For the definitions of proof/networks/Eight/ViaGrouping/SatPsiDefs.lean, for clauses of at most k
literals (the paper: k = 3):
* «factorized by f_{a,b}(z_a, θ) = [z_a|_b = θ]»: `satF_eq` (the f of the network `wordNet` is this
  function);
* «Put Ψ_{a,b}(z_a, z_b) = [z_a|_b = z_b|_a]»: `satPsi_eq` (this is the Ψ of the network `wordNet`,
  which is defined there as the sum over θ);
* the procedure answers in one step (`satPsiM_runs`), and this step takes polynomial time
  (`satPsi_polyT`, `satProcs_keepsP`);
* «Definition 2 holds», with B = 1 and P = max{1, 2k·m̄} (the paper: k = 3, P = 6m̄):
  `satNet_isNetworkP`, by the bridge `stBridge` of proof/networks/Eight/ViaGrouping/Bridge.lean. -/

public section

namespace Eight.ViaGrouping

open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight.SecNetworks

variable {g k : ℕ} {Φ : Fml}

/-! ## z_a|_b, f and Ψ -/

theorem restr_of_lt {a b : ℕ} (h : a < b) (z : List Bool) : restr g k Φ a b z = (links g k Φ a b).map fun p => z.getD p.1 false := if_pos h

theorem restr_of_gt {a b : ℕ} (h : b < a) (z : List Bool) : restr g k Φ a b z = (links g k Φ b a).map fun p => z.getD p.2 false := if_neg (by omega)

/-- «f_{a,b}(z_a, θ) = [z_a|_b = θ]», θ ∈ {0,1}^{c_{a,b}}: the function f of the network `wordNet`
is the one that the paper prints. -/
theorem satF_eq (a b : ℕ) (z : List Bool) {θ : List Bool} (hθ : θ.length = capF g k Φ a b) : fF g k (Φ, ((a, b), (z, θ))) = if restr g k Φ a b z = θ then 1 else 0 := by
  unfold fF restr
  unfold capF at hθ
  by_cases h : a < b
  · rw [min_eq_left h.le, max_eq_right h.le] at hθ
    simp only [if_pos h]
    exact boole_congr ((zip_all_iff (fun p : ℕ × ℕ => z.getD p.1 false) _ θ hθ).trans eq_comm)
  · rw [min_eq_right (not_lt.1 h), max_eq_left (not_lt.1 h)] at hθ
    simp only [if_neg h]
    exact boole_congr ((zip_all_iff (fun p : ℕ × ℕ => z.getD p.2 false) _ θ hθ).trans eq_comm)

/-- **Ψ of the network of Φ.** «Put Ψ_{a,b}(z_a, z_b) = [z_a|_b = z_b|_a]»: the function `satPsi` is
the Ψ_{a,b} of the network `wordNet` (there: the sum over θ of f_{a,b}·f_{b,a}). -/
theorem satPsi_eq {a b : Fin g} (hab : a ≠ b) (z z' : List Bool) : satPsi g k Φ ((a.val, b.val), (z, z')) = (wordNet g k Φ).Ψ a b z z' := by
  unfold satPsi
  rcases lt_or_gt_of_ne hab with h | h
  · have h' : a.val < b.val := h
    rw [wordNet_Ψ_lt h]
    simp only [restr_of_lt h', restr_of_gt h']
    refine boole_congr ?_
    simp only [List.all_eq_true, beq_iff_eq, List.map_inj_left]
  · have h' : b.val < a.val := h
    rw [Network.Ψ_comm, wordNet_Ψ_lt h]
    simp only [restr_of_lt h', restr_of_gt h']
    refine boole_congr ?_
    simp only [List.all_eq_true, beq_iff_eq, List.map_inj_left]
    exact forall₂_congr fun _ _ => eq_comm

/-! ## The procedure: one step, which takes polynomial time -/

@[fun_prop] theorem restr_polyT {α : Type} [Enc α] (g k : ℕ) {φ : α → Fml} {a b : α → ℕ} {z : α → List Bool} (hφ : PolyT φ) (ha : PolyT a) (hb : PolyT b) (hz : PolyT z) :
    PolyT fun x => restr g k (φ x) (a x) (b x) (z x) := by
  unfold restr; fun_prop

/-- A value of Ψ is computed in polynomial time from Φ and the query. -/
theorem satPsi_polyT (g k : ℕ) : PolyT fun x : Fml × PsiQ => satPsi g k x.1 x.2 := by
  unfold satPsi; fun_prop

/-- The procedure for Ψ has polynomial-time steps. -/
theorem satPsiM_isPolyT (g k : ℕ) : Nonempty (IsPolyT (satPsiM g k)) := ⟨IsPolyT.ofFun (satPsi_polyT g k)⟩

/-- The procedure for Ψ answers a query on two settings in one step, on states of the size within
which the procedures for W and f answer. -/
theorem satPsiM_runs (a b : Fin g) {z z' : List Bool} (hz : z.length = mu g Φ * k) (hz' : z'.length = mu g Φ * k) :
    (satPsiM g k).Runs (Φ, ((a.val, b.val), (z, z'))) 1 (size Φ + 2 * g + 6 * (mu g Φ * k) + 8) (satPsi g k Φ ((a.val, b.val), (z, z'))) := by
  refine (Stepped.ofFun_runs (fun x : Fml × PsiQ => satPsi g k x.1 x.2) (Φ, ((a.val, b.val), (z, z')))).mono le_rfl ?_
  have h1 := size_fin a
  have h1' := size_fin b
  have h2 : size (satPsi g k Φ ((a.val, b.val), (z, z'))) ≤ 2 := size_boole _
  simp only [size_prod, size_word, hz, hz'] at *
  omega

/-- P is given in unary. -/
theorem satPf_unary (g k : ℕ) : Unary (satPf g k) := by
  have h1 : Unary fun φ : Fml => φ.length := Unary.of_length (by fun_prop)
  have h2 : Unary fun φ : Fml => mu g φ := h1.of_le (by fun_prop) fun φ => mu_le_length g φ
  have h3 : Unary fun φ : Fml => 1 + 2 * k * mu g φ := (Unary.const 1).add ((Unary.const (2 * k)).mul h2)
  exact h3.of_le (by unfold satPf; fun_prop) fun φ => by unfold satPf; omega

/-- The procedures of the network of a formula have polynomial-time steps, the lengths P_a, c_{a,b}
and the number P are given in unary. -/
theorem satProcs_keepsP (g k : ℕ) : KeepsP (satProcs g k) := keepsP_ofProcs (satP_keeps g k) (satPf_unary g k) (satPsiM_isPolyT g k)

/-! ## «Definition 2 holds» -/

/-- **Section 6.** «The network of Φ is the following network on [g] with P = 6m̄ and B = 1. …
Definition 2 holds: Σ_{b ≠ a} c_{a,b} ≤ 2·3m̄ = P, all values are 0 or 1, and τ is polynomial in m».
The network of Φ, with the procedure `satPsiM` for Ψ, is a network in the sense
of Definition 2 (without the part of condition (iii) that gives B to the algorithm as input), with
parameters P = max{1, 2k·m̄}, B = 1, τ = 1; it has the value and the total of the network `wordNet`.
Different from the paper: k literals per clause in place of 3; P ≥ 1 also if Φ has no clause; τ = 1,
since a value is computed in
one step, which takes polynomial time (`satProcs_keepsP`); every string of k·m̄ bits is a setting (a
clause has k places, and W is 0 unless the bits at places without a literal are 0). -/
theorem satNet_isNetworkP (hg : 0 < g) (k : ℕ) (Φ : Fml) :
    IsNetworkP (satProcs g k) Φ (satNet g k Φ) (satPf g k Φ) 1 1 (size Φ + 2 * g + 6 * (mu g Φ * k) + 8 + 2) ∧ (satNet g k Φ).value = (wordNet g k Φ).value ∧ (satNet g k Φ).U = (wordNet g k Φ).U :=
  stBridge Fml g (satP g k) (satPf g k) (satPsiM g k) Φ (wordNet g k Φ) (satPf g k Φ) 0 1 _ (le_max_left _ _) le_rfl
    ⟨sized_mono (sized_wordNet hg 0) (le_max_right _ _), presents hg Φ⟩ rfl
    fun a b hab z hz z' hz' => satPsi_eq hab z z' ▸ satPsiM_runs a b (mem_words.1 hz) (mem_words.1 hz')

end Eight.ViaGrouping
