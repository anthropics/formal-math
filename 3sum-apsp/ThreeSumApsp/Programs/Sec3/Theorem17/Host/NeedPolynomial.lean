/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Text

/-!
# The host of Theorem 17: the need stays polynomial

The need of a procedure says what it asks of the limits of a run: the largest number that it forms,
the cells that it uses, and the depth of its calls.  If the need of the solver is polynomially
bounded (`PolyNeedN`), then so is the need of the host (`hostNeed_poly`: `PolyNeed` of `hostNeed`).
The need of the host is an explicit expression in `n`, `U`, `D`, `g` and a few quantities derived
from them.  Each of these is at most a polynomial in `(n + 1)(U + 1)` (`PolyBounded`), and such
bounds are closed under sums, products and powers.

* The quantities: `⌊√D⌋ ≤ D`, the number of binary digits of `U` is at most `U`,
  `2^{len + 1} ≤ 4(U + 1)`, `2^⌈log₂ n⌉ ≤ 2(n + 1)`, `⌊n²/√D⌋ ≤ n²`, `⌈s/g⌉ ≤ s + g` with
  `s = ⌊√D⌋`.
* The numbers (`polyBounded_hostWord`), the cells (`polyBounded_chooseCells`,
  `polyBounded_hostLayout`), and each of the three parts of the need of the solver on the instances
  of the host (`polyBounded_sup`).  The depth adds `O(⌈log₂ n⌉)` calls (`polyBounded_clog`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

namespace HostPoly

/-! ## The quantities -/

/-- `⌊n²/√D⌋ ≤ n²`. -/
private theorem queryCapNat_le_sq (n D : ℕ) : queryCapNat n D ≤ n ^ 2 := by
  unfold queryCapNat
  calc Nat.sqrt (n ^ 4 / D) ≤ Nat.sqrt (n ^ 4) := Nat.sqrt_le_sqrt (Nat.div_le_self _ _)
    _ = Nat.sqrt (n ^ 2 * n ^ 2) := by rw [← pow_add]
    _ = n ^ 2 := Nat.sqrt_eq _

/-- `2^{len + 1} ≤ 4(U + 1)` for the number `len` of binary digits of `U`. -/
private theorem two_pow_bitLen_le (U : ℕ) : 2 ^ (bitLen U + 1) ≤ 4 * (U + 1) := by
  rcases Nat.eq_zero_or_pos U with rfl | hU
  · simp [bitLen]
  · have hlen : 0 < bitLen U := Nat.size_pos.2 hU
    obtain ⟨b, hb⟩ : ∃ b, bitLen U = b + 1 := ⟨bitLen U - 1, by omega⟩
    have hpow : 2 ^ b ≤ U := Nat.lt_size.1 (by unfold bitLen at hb; omega)
    rw [hb, pow_succ, pow_succ]
    omega

/-- `2^⌈log₂ n⌉ ≤ 2(n + 1)`. -/
private theorem two_pow_clog_le (n : ℕ) : 2 ^ Nat.clog 2 n ≤ 2 * (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have := Nat.pow_clog_le_mul Nat.one_lt_two hn
    omega

/-- The number of binary digits of `U` is at most `U`. -/
private theorem polyBounded_bitLen : PolyBounded fun _ U => bitLen U :=
  PolyBounded.snd.of_le fun _ _ => Nat.size_le.2 Nat.lt_two_pow_self

/-- `2^{len + 1} ≤ 4(U + 1)` is polynomially bounded. -/
private theorem polyBounded_two_pow_bitLen : PolyBounded fun _ U => 2 ^ (bitLen U + 1) := by
  growth_poly [Scale.SoftO.of_forall_le two_pow_bitLen_le]

/-- The size of the matrices of Strassen's recursion. -/
private theorem polyBounded_two_pow_clog : PolyBounded fun n _ => 2 ^ Nat.clog 2 n := by
  growth_poly [Scale.SoftO.of_forall_le two_pow_clog_le]

/-- The depth of Strassen's recursion. -/
private theorem polyBounded_clog : PolyBounded fun n _ => Nat.clog 2 n :=
  polyBounded_two_pow_clog.of_le fun _ _ => Nat.lt_two_pow_self.le

/-- `(2^c)^⌈log₂ n⌉ = (2^⌈log₂ n⌉)^c`. -/
private theorem polyBounded_pow_clog (c : ℕ) : PolyBounded fun n _ => (2 ^ c) ^ Nat.clog 2 n :=
  (by growth_poly [polyBounded_two_pow_clog] :
    PolyBounded fun n _ => (2 ^ Nat.clog 2 n) ^ c).of_le fun n _ => by
      rw [← pow_mul, ← pow_mul, mul_comm]

variable {D g : ℕ → ℕ}

/-- The number of query pairs of an instance. -/
private theorem polyBounded_queryCapNat : PolyBounded fun n _ => queryCapNat n (D n) := by
  growth_poly [Scale.SoftO.of_forall_le₂ queryCapNat_le_sq]

/-! ## The numbers, the cells, and the solver -/

section parts

variable (hD : PolyBounded fun n _ => D n)
include hD

/-- The numbers that the host forms. -/
private theorem polyBounded_hostWord {a b : ℕ → ℕ} (ha : PolyBounded fun n _ => a n)
    (hb : PolyBounded fun n _ => b n) (hg : PolyBounded fun n _ => g n) :
    PolyBounded fun n U => hostWord (a n) (b n) n U (D n) (g n) := by
  have hring : PolyBounded fun n _ => 16 ^ Nat.clog 2 n := polyBounded_pow_clog 4
  unfold hostWord pieceSizeNat
  growth_poly [ha, hb, hD, hg, polyBounded_two_pow_bitLen, hring, Scale.SoftO.ceilDiv]

/-- The cells of the arrays of the host. -/
private theorem polyBounded_hostLayout : PolyBounded fun n U => hostLayout n U (D n) := by
  unfold hostLayout
  growth_poly [hD, polyBounded_bitLen, polyBounded_queryCapNat]

/-- The cells for the choice of the prime.  The scratch space of Strassen's recursion is at most
the size `4^K s` of a matrix, with `K = ⌈log₂ n⌉` and `s = ⌊√D⌋`. -/
private theorem polyBounded_chooseCells : PolyBounded fun n U => chooseCells n U (D n) := by
  have hmatrix : PolyBounded fun n _ => 4 ^ Nat.clog 2 n := polyBounded_pow_clog 2
  unfold chooseCells countCells
  growth_poly [hD, polyBounded_bitLen, polyBounded_two_pow_clog, polyBounded_clog, hmatrix,
    Scale.SoftO.of_forall_le₂ strScr_le]

/-- A polynomially bounded function of the parameters `n`, `D`, `w` of an instance, at its largest
over the instances of the host, which have at most `⌊n²/√D⌋` query pairs. -/
private theorem polyBounded_sup {f : List ℕ → ℕ} {s k : ℕ} (hf : ∀ ps, f ps ≤ polyBound s k ps) :
    PolyBounded fun n _ => (Finset.range (queryCapNat n (D n) + 1)).sup fun w => f [n, D n, w] := by
  have hbound :
      PolyBounded fun n _ => 2 ^ s * ((n + 1) * ((D n + 1) * (queryCapNat n (D n) + 1))) ^ k := by
    growth_poly [hD, polyBounded_queryCapNat]
  refine hbound.of_le fun n _ => Finset.sup_le fun w hw => (hf _).trans ?_
  have hw' : w ≤ queryCapNat n (D n) := Nat.lt_succ_iff.1 (Finset.mem_range.1 hw)
  simp only [polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  gcongr

end parts

end HostPoly

open HostPoly in
/-- **The need of the host stays polynomial**, if the parameters, the numbers that the parameter
procedures form, and the need of the solver are polynomially bounded. -/
theorem hostNeed_poly {Dfun Gfun wD wG : ℕ → ℕ} {need : List ℕ → Need}
    (hD : PolyBounded fun n _ => Dfun n) (hG : PolyBounded fun n _ => Gfun (Dfun n))
    (hwD : PolyBounded fun n _ => wD n) (hwG : PolyBounded fun n _ => wG (Dfun n))
    (h : PolyNeedN need) :
    PolyNeed (hostNeed Dfun Gfun wD wG need) := by
  obtain ⟨s, k, hle⟩ := h
  unfold hostNeed hostNeedAt supNeed
  poly_need [polyBounded_hostWord hD hwD hwG hG, polyBounded_chooseCells hD,
    polyBounded_hostLayout hD, polyBounded_clog, polyBounded_sup hD fun ps => (hle ps).1,
    polyBounded_sup hD fun ps => (hle ps).2.1, polyBounded_sup hD fun ps => (hle ps).2.2]

end Light.Sec3
