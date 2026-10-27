/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.Half
public import ClauseBound.Inst.CertHalfPart

/-! # The pieces with ρ = 1/√2 as programs: the certificates of the five numbers

For all values of the two parameters c₀ and c of `halfF`: the number of pieces, the number of bits
of a factorization, the exponent of the pad and the bound for the bits of the values are given in
unary (`cnt`, `cap`, `need`, `bits`), and the factor d = h! is polynomial-time (`d`), all as
functions of λ in unary. These are five of the seven fields of `(halfF c₀ c).Keeps`. -/

public section

namespace ClauseBound.Inst.Half.CertSmall

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half

variable {α : Type} [Enc α]

/-- s = i − 2h, with i cut off at 4h, is polynomial-time in h and i. -/
theorem sOf_polyT {h i : α → ℕ} (hh : PolyT h) (hi : PolyT i) : PolyT fun x => sOf (h x) (i x) := by
  unfold sOf
  exact PolyT.subZ (PolyT.natCast (PolyT.min' hi (PolyT.mul (PolyT.const 4) hh))) (PolyT.mulZ (PolyT.const 2) (PolyT.natCast hh))

/-- The least k with n ≤ 2^k is polynomial-time in n. -/
theorem clog_polyT {n : α → ℕ} (hn : PolyT n) : PolyT fun x => Nat.clog 2 (n x) := by
  simp only [clog_two_eq]
  exact PolyT.size' (PolyT.sub hn (PolyT.const 1))

/-- The number 4h + 1 of pieces is given in unary. -/
theorem cnt (c₀ c : ℕ) : Unary fun p : U × U => (halfF c₀ c).cnt p.1.length p.2.length :=
  ((Unary.const 4).mul (hF_unary c₀ (Unary.of_length PolyT.id'.snd))).add (Unary.const 1)

/-- The factor h! is polynomial-time. -/
theorem d (c₀ c : ℕ) : PolyT fun p : U × U => (halfF c₀ c).d p.1.length p.2.length :=
  factN_polyT (hF_unary c₀ (Unary.of_length PolyT.id'.snd))

/-- The number of bits of a factorization is given in unary; the number i of the piece is in binary. -/
theorem cap (c₀ c : ℕ) : Unary fun p : Bool × U × U × ℕ => (halfF c₀ c).cap p.1 p.2.1.length p.2.2.1.length p.2.2.2 := by
  have hl : Unary fun p : Bool × U × U × ℕ => p.2.2.1.length := Unary.of_length PolyT.id'.snd.snd.fst
  have hh : Unary fun p : Bool × U × U × ℕ => hF c₀ p.2.2.1.length := hF_unary c₀ hl
  have hs : PolyT fun p : Bool × U × U × ℕ => sOf (hF c₀ p.2.2.1.length) p.2.2.2 := sOf_polyT hh.poly PolyT.id'.snd.snd.snd
  have hb : Unary fun p : Bool × U × U × ℕ => 2 * c * p.2.2.1.length := (Unary.const (2 * c)).mul hl
  have hR : PolyT fun p : Bool × U × U × ℕ => bif p.1 then RcolF (hF c₀ p.2.2.1.length) (sOf (hF c₀ p.2.2.1.length) p.2.2.2)
      else RrowF (hF c₀ p.2.2.1.length) (sOf (hF c₀ p.2.2.1.length) p.2.2.2) :=
    PolyT.cond' PolyT.id'.fst (RcolF_polyT hh hs) (RrowF_polyT hh hs)
  exact hb.of_le (PolyT.min' hb.poly (clog_polyT hR)) fun p => min_le_left _ _

/-- The exponent c·λ of the pad is given in unary. -/
theorem need (c₀ c : ℕ) : Unary fun p : U × U => (halfF c₀ c).need p.1.length p.2.length :=
  (Unary.const c).mul (Unary.of_length PolyT.id'.snd)

/-- The bound (2λ)^c for the number of bits of the values is given in unary. -/
theorem bits (c₀ c : ℕ) : Unary fun p : U × U => (halfF c₀ c).bits p.1.length p.2.length :=
  unary_pow_const ((Unary.const 2).mul (Unary.of_length PolyT.id'.snd)) c

end ClauseBound.Inst.Half.CertSmall
