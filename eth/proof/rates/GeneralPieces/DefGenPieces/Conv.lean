/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppRunningTimeStatement
public import GeneralPieces.Trim.Cert
import PaddedDescent.F.FuelCert

/-! # The definition of pieces with parameters (ρ, c), and the form in which the recursion uses it

`AppRunningTime.IsPieces` is the definition in Appendix A, clause by clause. The programs of the
recursion are analysed under `ClauseBound.Gen.Par P ρ c` and `P.Keeps`, which speak of every value
of the parameter h
and have three more fields: the exponent of the pad, a bound for the number of bits of the values,
and a constant m with all numbers of bits at most 2·m·λ. This file goes both ways.

* `of_par_realizes`: from `Par P ρ c` and `P.Keeps` to the definition, with max(c + 1, 2m) in place
  of c. The c + 1 turns «at most» into «below»; the 2m is the loop of `valF`, which adds up the
  value
  of a piece.
* `atZero_par`, `atZero_keeps`: from the definition to `Par` and `Keeps` for the programs read at h =
  0, given a bound 2·m·λ on all numbers of bits; `Par` then holds with every constant c' ≥ c, m.
  If all numbers of bits are at most 2λ then m = 1 and the constant c is the same (`to_par_one`).

The definitions `valOf` and `atZero` are in `DefGenPieces/Progs.lean`. -/

@[expose] public section

namespace GeneralPieces

open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen AppRunningTime

/-! ### From the programs of the recursion to the definition -/

namespace DefGenPieces

/-- «At most 2^b» with b ≤ (2λ)^c is «below 2^{(2λ)^{c'}}» for c' > c. -/
theorem abs_lt {z : ℤ} {b lam c c' : ℕ} (hz : |z| ≤ 2 ^ b) (hb : b ≤ (2 * lam) ^ c) (hl : 1 ≤ lam) (hc : c < c') : |z| < 2 ^ (2 * lam) ^ c' :=
  hz.trans_lt (pow_lt_pow_right₀ (by norm_num) (hb.trans_lt (Nat.pow_lt_pow_right (by omega) hc)))

/-- log(2λ) ≥ 0. -/
theorem logb_nonneg {lam : ℕ} (hl : 1 ≤ lam) : 0 ≤ Real.logb 2 (2 * lam) :=
  Real.logb_nonneg (by norm_num) (by
    have : (1 : ℝ) ≤ lam := by exact_mod_cast hl
    linarith)

/-- log(2λ) ≤ λ. -/
theorem logb_le {lam : ℕ} (hl : 1 ≤ lam) : Real.logb 2 (2 * lam) ≤ lam := by
  have h0 : 2 * lam ≤ 2 ^ lam := by
    obtain ⟨k, rfl⟩ : ∃ k, lam = k + 1 := ⟨lam - 1, by omega⟩
    have := Nat.lt_two_pow_self (n := k)
    rw [pow_succ]
    omega
  have h1 : (0 : ℝ) < 2 * lam := by
    have : (1 : ℝ) ≤ lam := by exact_mod_cast hl
    linarith
  have h2 : Real.logb 2 (2 * lam) ≤ Real.logb 2 ((2 : ℝ) ^ lam) := Real.logb_le_logb_of_le (by norm_num) h1 (by exact_mod_cast h0)
  rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h2

end DefGenPieces

open DefGenPieces Trim

/-- Programs with `Par P ρ c` and `P.Keeps` are pieces with parameters (ρ, max(c + 1, 2m)) in the
sense of the definition, with any functions A_i that they realize at h = 0. -/
theorem of_par_realizes {P : PiecesF} {ρ : ℝ} {c : ℕ} (hP : Par P ρ c) (hK : P.Keeps) (h1 : 1 / 2 ≤ ρ) (h2 : ρ < 1) {A : (lam : ℕ) → ℕ → Pieces.Four lam}
    (hR : ∀ lam, 1 ≤ lam → Realizes P 0 lam (A lam)) : IsPieces ρ (max (c + 1) (2 * P.m)) P A (valOf P) := by
  have hc : c < max (c + 1) (2 * P.m) := lt_of_lt_of_le (Nat.lt_succ_self c) (le_max_left _ _)
  have hn : ∀ lam, 1 ≤ lam → ∀ pad : U, 2 ^ (max (c + 1) (2 * P.m) * lam) ≤ pad.length → 2 ^ P.need 0 lam ≤ pad.length := fun lam hl pad hp =>
    le_trans (Nat.pow_le_pow_right (by norm_num) ((hP.need 0 lam hl).trans (Nat.mul_le_mul_right _ hc.le))) hp
  have hcap : ∀ lam, 1 ≤ lam → ∀ pad : U, 2 ^ (max (c + 1) (2 * P.m) * lam) ≤ pad.length → ∀ i < P.cnt 0 lam, ∀ tr,
      2 ^ P.cap tr 0 lam i ≤ pad.length := fun lam hl pad hp i hi tr =>
    le_trans (Nat.pow_le_pow_right (by norm_num) (((hP.spec 0 lam hl).cap_le tr i hi).trans (Nat.mul_le_mul_right _ (le_max_right _ _)))) hp
  exact {
    rho_ge := h1
    rho_lt := h2
    c_pos := by omega
    d_pos := fun lam hl => (hP.spec 0 lam hl).d_pos
    sum := fun lam hl => (hR lam hl).1
    row := fun lam hl pad hp i hi => ((hR lam hl).2.2 pad (hn lam hl pad hp) i hi).1
    col := fun lam hl pad hp i hi => ((hR lam hl).2.2 pad (hn lam hl pad hp) i hi).2.1
    caps := fun lam hl i hi => by
      have h3 : P.cap false 0 lam i + P.cap true 0 lam i ≤ capSum P 0 lam :=
        Finset.le_sup (f := fun i => P.cap false 0 lam i + P.cap true 0 lam i) (Finset.mem_range.2 hi)
      have h4 : ((P.cap false 0 lam i + P.cap true 0 lam i : ℕ) : ℝ) ≤ capSum P 0 lam := by exact_mod_cast h3
      have h5 : (c : ℝ) ≤ (max (c + 1) (2 * P.m) : ℕ) := by exact_mod_cast hc.le
      have h6 := mul_le_mul_of_nonneg_right h5 (logb_nonneg hl)
      have h7 := hP.caps 0 lam hl
      linarith
    card := fun lam hl => (hP.cnt 0 lam hl).trans (Nat.pow_le_pow_right (by omega) hc.le)
    size_d := fun lam hl => (hP.d 0 lam hl).trans_le (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by omega) hc.le))
    size_A := fun lam hl i hi x y u v => abs_lt ((hR lam hl).2.1 i hi x y u v) (hP.bits 0 lam hl) hl hc
    size_f := fun lam hl pad hp i hi tr x y θ =>
      ⟨abs_lt (((hR lam hl).2.2 pad (hn lam hl pad hp) i hi).2.2 tr x y θ).1 (hP.bits 0 lam hl) hl hc,
        abs_lt (((hR lam hl).2.2 pad (hn lam hl pad hp) i hi).2.2 tr x y θ).2 (hP.bits 0 lam hl) hl hc⟩
    time_cnt := hK.cnt.comp (h := fun lam : U => (([] : U), lam)) (by fun_prop)
    time_d := hK.d.comp (g := fun lam : U => (([] : U), lam)) (by fun_prop)
    time_cap := hK.cap.comp (h := fun p : Bool × U × ℕ => (p.1, ([] : U), p.2.1, p.2.2)) (by fun_prop)
    time_top := hK.top
    time_bot := hK.bot
    time_val := (valF_polyT hK).comp (g := fun q : ValQ => ((q.1, false), (([] : U), q.2.1.2), q.2.2)) (by fun_prop)
    val_eq := fun lam hl pad hp i hi x y u v => (valF_eq (hR lam hl) (hn lam hl pad hp) hi (hcap lam hl pad hp i hi) x y u v).1 }

/-! ### From the definition to the programs of the recursion -/

section

variable {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : ValQ → ℤ}

/-- The index set is not empty, because the pieces add up to d ≥ 1 at x = v, y = u. -/
theorem cnt_pos_of_isPieces (h : IsPieces ρ c P A val) {lam : ℕ} (hl : 1 ≤ lam) : 1 ≤ P.cnt 0 lam := by
  by_contra h0
  have h1 : P.cnt 0 lam = 0 := by omega
  have h2 := h.sum lam hl (fun _ => false) (fun _ => false) (fun _ => false) (fun _ => false)
  have h3 := h.d_pos lam hl
  rw [h1] at h2
  simp [Pieces.cross] at h2
  omega

/-- The programs read at h = 0 are pieces in the sense of the recursion, at every h. -/
theorem atZero_spec (h : IsPieces ρ c P A val) {m : ℕ} (hm : 1 ≤ m) (hcap : ∀ tr lam i, 1 ≤ lam → i < P.cnt 0 lam → P.cap tr 0 lam i ≤ 2 * m * lam)
    (hh : ℕ) {lam : ℕ} (hl : 1 ≤ lam) : (atZero P c m).Spec hh lam where
  cnt_pos := cnt_pos_of_isPieces h hl
  d_pos := h.d_pos lam hl
  m_pos := hm
  cap_le tr i hi := hcap tr lam i hl hi
  ex := ⟨A lam, h.sum lam hl, fun i hi x y u v => (h.size_A lam hl i hi x y u v).le, fun pad hp i hi =>
    ⟨h.row lam hl pad hp i hi, h.col lam hl pad hp i hi, fun tr x y θ => ⟨(h.size_f lam hl pad hp i hi tr x y θ).1.le, (h.size_f lam hl pad hp i hi tr x y θ).2.le⟩⟩⟩

/-- Pieces with parameters (ρ, c) all of whose numbers of bits are at most 2·m·λ give `Par` with
every constant c' ≥ c, m. -/
theorem atZero_par (h : IsPieces ρ c P A val) {m c' : ℕ} (hm : 1 ≤ m) (hcap : ∀ tr lam i, 1 ≤ lam → i < P.cnt 0 lam → P.cap tr 0 lam i ≤ 2 * m * lam)
    (hc : c ≤ c') (hmc : m ≤ c') : Par (atZero P c m) ρ c' where
  spec hh lam hl := atZero_spec h hm hcap hh hl
  caps hh lam hl := by
    have h0 : (0 : ℝ) ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam) := by
      have := h.rho_ge
      have h4 : (0 : ℝ) ≤ lam := Nat.cast_nonneg _
      have h5 := mul_nonneg (Nat.cast_nonneg (α := ℝ) c) (logb_nonneg hl)
      nlinarith
    have h1 : capSum (atZero P c m) hh lam ≤ ⌊4 * ρ * lam + c * Real.logb 2 (2 * lam)⌋₊ :=
      Finset.sup_le fun i hi => Nat.le_floor (h.caps lam hl i (Finset.mem_range.1 hi))
    have h2 : (capSum (atZero P c m) hh lam : ℝ) ≤ 4 * ρ * lam + c * Real.logb 2 (2 * lam) := le_trans (by exact_mod_cast h1) (Nat.floor_le h0)
    have h3 : (c : ℝ) ≤ c' := by exact_mod_cast hc
    have h4 := mul_le_mul_of_nonneg_right h3 (logb_nonneg hl)
    linarith
  cnt hh lam hl := (h.card lam hl).trans (Nat.pow_le_pow_right (by omega) hc)
  bits hh lam hl := Nat.pow_le_pow_right (by omega) hc
  d hh lam hl := (h.size_d lam hl).trans_le (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by omega) hc))
  need hh lam hl := Nat.mul_le_mul_right _ hc
  m_le := hmc

/-- The programs read at h = 0 are polynomial-time (`PiecesF.Keeps`), by the time clauses of the
definition. -/
theorem atZero_keeps (h : IsPieces ρ c P A val) (m : ℕ) : (atZero P c m).Keeps where
  cnt := h.time_cnt.comp (h := fun p : U × U => p.2) (by fun_prop)
  d := h.time_d.comp (g := fun p : U × U => p.2) (by fun_prop)
  cap := h.time_cap.comp (h := fun p : Bool × U × U × ℕ => (p.1, p.2.2.1, p.2.2.2)) (by fun_prop)
  top := h.time_top.comp (g := fun q : PQ => (q.1, (0, q.2.1.2), q.2.2)) (by fun_prop)
  bot := h.time_bot.comp (g := fun q : PQ => (q.1, (0, q.2.1.2), q.2.2)) (by fun_prop)
  need := by change Unary fun p : U × U => c * p.2.length; fun_prop
  bits := by change Unary fun p : U × U => (2 * p.2.length) ^ c; fun_prop

/-- Pieces with parameters (ρ, c) and c^row, c^col ≤ 2λ: the recursion has them with m = 1 and with
the same constant c. -/
theorem to_par_one (h : IsPieces ρ c P A val) (hcap : ∀ tr lam i, 1 ≤ lam → i < P.cnt 0 lam → P.cap tr 0 lam i ≤ 2 * lam) :
    Par (atZero P c 1) ρ c ∧ (atZero P c 1).Keeps ∧ (atZero P c 1).m = 1 :=
  ⟨atZero_par h le_rfl (by simpa using hcap) le_rfl h.c_pos, atZero_keeps h 1, rfl⟩

end

end GeneralPieces
