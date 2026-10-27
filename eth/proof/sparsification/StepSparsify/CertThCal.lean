/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepSparsify.Defs
public import SparsificationLemma.Cal.Beta
public import ClauseBound.ParityChecks.CertLib
import Mathlib.Data.Nat.Choose.Central

/-! # Calabro's thresholds are polynomial-time

Calabro's thresholds θ i are polynomial-time: `thetaC_polyT` shows that `Cal.thetaC a i` is
polynomial-time whenever Calabro's α (here `a`) is polynomial-time and i is given in unary.
The thresholds are defined by a recursion on sums of products. Here they are computed from closed
forms. By `SparsificationLemma.Cal.stBetaCat`, θ 0 = 2 and θ i = α·2·(8α)^(i−1)·Cat_(i−1) for i ≥ 1
(`thetaC_eq`),
and Cat_c = C(2c, c)/(c + 1).
The certificates for binomial coefficients and for ⌈log₂⌉ are those of
proof/rates/ClauseBound/ParityChecks/CertLib.lean; the one for powers with the exponent in unary is
`PolyT.pow_unary`. -/

public section

namespace StepSparsify.CertThCal

open Groundwork SparsificationLemma ClauseBound.ParityChecks.CertLib

variable {α : Type} [Enc α]

/-- Calabro's thresholds in closed form: θ 0 = 2, and θ i = α·(2·(8α)^(i−1)·Cat_(i−1)) for i ≥ 1. -/
theorem thetaC_eq (a i : ℕ) : Cal.thetaC a i = if i = 0 then 2 else a * (2 * (8 * a) ^ (i - 1) * catalan (i - 1)) := by
  cases i with
  | zero => rfl
  | succ i => rw [if_neg (Nat.succ_ne_zero i), Nat.add_sub_cancel, ← Cal.stBetaCat a i]; rfl

/-- The Catalan number Cat_c is polynomial-time, for c in unary. -/
theorem catalan_polyT {c : α → ℕ} (hc : Unary c) : PolyT fun x => catalan (c x) :=
  (PolyT.div (choose_polyT (PolyT.mul (PolyT.const 2) hc.poly) hc) (PolyT.add hc.poly (PolyT.const 1))).congr fun x => by
    rw [catalan_eq_centralBinom_div, Nat.centralBinom_eq_two_mul_choose]

/-- The threshold θ i is polynomial-time whenever Calabro's α (here `a`) is polynomial-time and i is
given in unary. -/
theorem thetaC_polyT {a i : α → ℕ} (ha : PolyT a) (hi : Unary i) : PolyT fun x => Cal.thetaC (a x) (i x) := by
  have h0 := hi.poly
  have h1 : Unary fun x => i x - 1 := hi.of_le (by fun_prop) fun x => Nat.sub_le _ _
  have hp : PolyT fun x => (8 * a x) ^ (i x - 1) := PolyT.pow_unary (by fun_prop) h1
  have hc := catalan_polyT h1
  simp only [thetaC_eq]; fun_prop

/-- Calabro's α for the width max(k, 3) and ε = 2^(−s) is polynomial-time jointly in k and s, if s
is given in unary. -/
theorem alphaS_polyT (hA : StAlphaS) {k s : α → ℕ} (hk : PolyT k) (hs : Unary s) : PolyT fun x => alphaS (k x) (s x) := by
  have h2 : PolyT fun x => 2 ^ s x := PolyT.pow_unary (PolyT.const 2) hs
  have hK : PolyT fun x => (max (k x) 3 - 1) * (max (k x) 3 - 1) := by fun_prop
  have hl : PolyT fun x => Nat.clog 2 (32 * ((max (k x) 3 - 1) * (max (k x) 3 - 1)) * 2 ^ s x) := clog_polyT (by fun_prop)
  have h : PolyT fun x => 2 * ((max (k x) 3 - 1) * (max (k x) 3 - 1)) * 2 ^ s x * Nat.clog 2 (32 * ((max (k x) 3 - 1) * (max (k x) 3 - 1)) * 2 ^ s x) :=
    PolyT.mul (PolyT.mul (PolyT.mul (PolyT.const 2) hK) h2) hl
  exact h.congr fun x => by rw [hA (k x) (s x), sq]

/-- Calabro's thresholds are polynomial-time, jointly in k, s and the index, all given in unary. -/
theorem stCertThCal (hA : StAlphaS) : StCertThCal := fun _ _ _ _ _ hk hs hi => thetaC_polyT (alphaS_polyT hA hk.poly hs) hi

end StepSparsify.CertThCal
