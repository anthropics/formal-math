/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.Close
public import Printed.CodingDefs
public import Printed.Achievable
public import Printed.GroupingProcs
public import Eight.ViaGrouping.LevelEnd
import Mathlib.Tactic

/-! # Proof of Proposition 3: «Both networks satisfy Definition 2», with a table query at the cost of one operation

Proof of Proposition 3, paragraph «Two networks for each ι»: «Both networks satisfy Definition 2
with P = g³λ (so gP = N), with B₁ = gB + g²λ + 1 in the role of B, and with τ = poly(B + λ)».
This development has this sentence for procedures that are step machines
(`Eight.ViaGrouping.levelNetP_isNetworkP`, proof/networks/Eight/ViaGrouping/LevelEnd.lean), for any
procedure R that answers the queries to the tables of the clique within t steps. Here R is «ask the
tables» with the tables built in, and t = 1
(`StAskServes`, a hypothesis of this file); `gridProcs_close` says that the procedures of
proof/threesat/Printed/, with the tables built in, are those of proof/networks/Eight/, and that they
give the printed B₁. So the two networks are networks in the sense of `SecNetworks.IsNetwork`, B₁
given (`grid_isNetwork_of`).
`stBothNetworks_of` reads this for machines with query access (the four procedures as one machine
answer the queries of Definition 2(iii): `answerOf_runs`,
proof/threesat/Printed/GroupingProcs.lean): steps of the machine with the tables built in are own
steps plus queries (`QueryMachines.stClose`). -/

public section

namespace Printed

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine

/-! ## Small facts -/

/-- A polynomial in X ≤ 5Y is at most A'·Y^{A'}. -/
theorem poly_absorb (A L : ℕ) : ∃ A' : ℕ, ∀ X Y : ℕ, 1 ≤ Y → X ≤ 5 * Y → A * X ^ A + L * X ≤ A' * Y ^ A' := by
  obtain ⟨A', hA'⟩ : ∃ A', A' = A * 5 ^ A + 5 * L + A + 1 := ⟨_, rfl⟩
  refine ⟨A', fun X Y hY hX => ?_⟩
  have h1 : X ^ A ≤ 5 ^ A * Y ^ A' := by
    calc X ^ A ≤ (5 * Y) ^ A := Nat.pow_le_pow_left hX A
      _ = 5 ^ A * Y ^ A := Nat.mul_pow 5 Y A
      _ ≤ 5 ^ A * Y ^ A' := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY (by omega))
  have h2 : X ≤ 5 * Y ^ A' := hX.trans (Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) Y))
  calc A * X ^ A + L * X ≤ A * (5 ^ A * Y ^ A') + L * (5 * Y ^ A') := Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
    _ = (A * 5 ^ A + 5 * L) * Y ^ A' := by ring
    _ ≤ A' * Y ^ A' := Nat.mul_le_mul_right _ (by omega)

/-! ## The sentence -/

/-- **«Both networks satisfy Definition 2 with P = g³λ (so gP = N), with B₁ = gB + g²λ + 1 in the
role of B, and with τ = poly(B + λ)»** (proof of Proposition 3, «Two networks for each ι»), in the
form that the proof of Proposition 3 in this folder uses: Definition 2 is `SecNetworks.IsNetwork`
((iii) as four step machines; B₁ is GIVEN by them), for the procedures `gridProcs` with the tables
of the clique on g² nodes built in: they give the network `levelNetP g tr λ y`, the printed B₁
included, within a·(B + λ)^a steps.
The context is (c, y), where c holds λ and B in unary. The hypothesis: «ask the tables», with the
tables built in, answers in one step. -/
theorem grid_isNetwork_of (hA : StAskServes) (g : ℕ) (hg : 1 ≤ g) : ∃ a : ℕ, ∀ (tr : Bool) (c : List Unit × List Unit) (lam B : ℕ) (W : ℕ → List Bool → ℤ) (y : ℕ), c.1.length = lam → c.2.length = B → 1 ≤ lam →
    (∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) → y < (tOf lam + 1) ^ nRect g →
    SecNetworks.IsNetwork ((gridProcs g tr).close (tables (g * g) lam W)) (c, y) (levelNetP g tr lam y (listTables (g * g) W)) (g ^ 3 * lam) (g * B + g ^ 2 * lam + 1) (a * (B + lam) ^ a)
      (size c + size (g * g) + g * g * (2 * lam + 2) + B + 3 + a * (size c + B + lam) ^ a + 2) := by
  obtain ⟨a, ha⟩ := levelNetP_isNetworkP g hg
  refine ⟨a, fun tr c lam B W y hcl hcB hl hW hy => ?_⟩
  subst hcl hcB
  have h := ha tr (List Unit × List Unit) (fun c => c.1.length) (askTable.close (tables (g * g) c.1.length W)) c c.2.length 1 _ (listTables (g * g) W) y hl le_rfl hy
    (hA (List Unit × List Unit) (g * g) c.1.length c.2.length W c hW)
  rw [Nat.mul_one] at h
  rw [gridProcs_close]
  exact ⟨h.is, h.τ_pos, { P_eq := h.given.P_eq, B_eq := rfl, len_eq := h.given.len_eq, cap_eq := h.given.cap_eq, mem_runs := h.given.mem_runs, W_runs := h.given.W_runs, Ψ_runs := h.given.Ψ_runs, f_runs := h.given.f_runs }⟩

/-- **«Both networks satisfy Definition 2 with P = g³λ (so gP = N), with B₁ = gB + g²λ + 1 in the
role of B, and with τ = poly(B + λ)»**, a query to the tables counted as one operation. -/
theorem stBothNetworks_of (hA : StAskServes) : StBothNetworks := by
  intro g hg
  obtain ⟨a, ha⟩ := grid_isNetwork_of hA g hg
  obtain ⟨a', ha'⟩ := poly_absorb a (size (g * g) + 4 * (g * g) + 9)
  refine ⟨a', fun tr lam B W y hl hB hW hy => ?_⟩
  have h := ha tr (unary lam, unary B) lam B W y (length_unary lam) (length_unary B) hl hW hy
  refine ⟨h.is, ?_, fun x v hx => ?_⟩
  · rw [show (gridProcs g tr).P ((unary lam, unary B), y) = g ^ 3 * lam from h.given.P_eq, show (gridProcs g tr).B ((unary lam, unary B), y) = g * B + g ^ 2 * lam + 1 from h.given.B_eq]
    cases tr
    · exact inputOf_eq (g := g) (levelNetP g false lam y (listTables (g * g) W)) _ _ _ _ h.given.len_eq h.given.cap_eq
    · exact inputOf_eq (g := g) (levelNetP g true lam y (listTables (g * g) W)) _ _ _ _ h.given.len_eq h.given.cap_eq
  · have hr := answerOf_runs h.given hx
    rw [← answer_close] at hr
    refine ((stClose _ _ _ _ _ _ _ _ _ _).1 hr).mono ?_ ?_
    · exact le_trans (Nat.le_add_right _ _) (ha' (B + lam) (B + lam) (by omega) (by omega))
    · obtain ⟨X, hX⟩ : ∃ X, X = size (unary lam, unary B) + B + lam := ⟨_, rfl⟩
      have hs : size (unary lam, unary B) = 2 * lam + 1 + (2 * B + 1) := by rw [size_prod, size_unary, size_unary]
      have h0 := ha' X (B + lam) (by omega) (by omega)
      have h1 : size (g * g) ≤ size (g * g) * X := Nat.le_mul_of_pos_right _ (by omega)
      have h2 : g * g * (2 * lam + 2) ≤ g * g * (4 * X) := Nat.mul_le_mul_left _ (by omega)
      have e : (size (g * g) + 4 * (g * g) + 9) * X = size (g * g) * X + g * g * (4 * X) + 9 * X := by ring
      rw [← hX]
      omega

end Printed
