/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Parameters
public import ThreeSumApsp.Spec.Sec3.Theorem17.Hashing
public import Mathlib.Algebra.Order.Floor.Div

/-!
# The parameters of Theorems 17 and 19 in integer arithmetic

The proof of Theorem 19 chooses `D` and `g` as rounded real powers of `n`: "Let D be the largest
power of four with D ≤ n^{1/18}, […] and let g := ⌈D^{1/36}⌉" on the route through Theorem 5, and
"Let D := ⌊n^{1/18}⌋ and g := ⌈D^{0.0315}⌉" on the route through Corollary 26.  The reduction of
Theorem 17 cuts each residue class into chunks of at most `n²/√D` query pairs and splits `C` into
pieces of at most `⌈s/g⌉` vertices, where `s = ⌊√D⌋`.  A program finds all these numbers by
operations on natural numbers.

* `rootFloor e t` is `⌊t^{1/e}⌋` and `rootCeil e t` is `⌈t^{1/e}⌉` (`floor_rpow_inv`,
  `ceil_rpow_inv`); they are characterised by `x ≤ rootFloor e t ↔ x^e ≤ t` (`le_rootFloor_iff`) and
  `rootCeil e t ≤ g ↔ t ≤ g^e` (`rootCeil_le_iff`).
* The four functions `paramD₅Nat`, `paramG₅Nat`, `paramD₂₆Nat`, `paramG₂₆Nat` are the parameters
  of the proof of Theorem 19 (`paramD₅Nat_eq`, `paramG₅Nat_eq`, `paramD₂₆Nat_eq`, `paramG₂₆Nat_eq`);
  they are at least 1 and at most `n` or `D` (`paramD₂₆Nat_le`, `paramG₅Nat_le`, `paramG₂₆Nat_le`).
* The sizes of the proof of Theorem 17: `⌊n²/√D⌋ = ⌊√(n⁴/D)⌋` (`queryCapNat_eq`), `s` is the integer
  square root (`sOf_eq_sqrt`), and the rounded quotients are `a ⌈/⌉ b` (`pieceSizeNat_eq`,
  `numPiecesNat_eq`, `numChunks_eq`).  The middle part `C_k × ℤ_p` of an instance has at most `D`
  vertices (`pieceSize_mul_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Roots, rounded down and up -/

/-- The greatest `x ≤ t` with `x^e ≤ t`: `⌊t^{1/e}⌋` for `e ≥ 1`. -/
def rootFloor (e t : ℕ) : ℕ := Nat.findGreatest (fun x => x ^ e ≤ t) t

/-- The least `g` with `g^e ≥ t`, for `t ≥ 1` and `e ≥ 1`: `⌈t^{1/e}⌉`. -/
def rootCeil (e t : ℕ) : ℕ := Nat.findGreatest (fun g => g ^ e < t) t + 1

/-- The power of `rootFloor e t` does not exceed `t`. -/
theorem rootFloor_pow_le {e : ℕ} (he : e ≠ 0) (t : ℕ) : rootFloor e t ^ e ≤ t :=
  Nat.findGreatest_spec (P := fun x => x ^ e ≤ t) (Nat.zero_le t) (by simp [he])

/-- `rootFloor e t` is the greatest `x` with `x^e ≤ t`. -/
theorem le_rootFloor {e : ℕ} (he : e ≠ 0) {t x : ℕ} (h : x ^ e ≤ t) : x ≤ rootFloor e t :=
  Nat.le_findGreatest ((Nat.le_self_pow he x).trans h) h

/-- The characterisation of `rootFloor` by which a program finds it. -/
theorem le_rootFloor_iff {e : ℕ} (he : e ≠ 0) {t x : ℕ} : x ≤ rootFloor e t ↔ x ^ e ≤ t :=
  ⟨fun h => (Nat.pow_le_pow_left h e).trans (rootFloor_pow_le he t), le_rootFloor he⟩

/-- `rootFloor e t` is `⌊t^{1/e}⌋`. -/
theorem floor_rpow_inv {e : ℕ} (he : e ≠ 0) (t : ℕ) :
    ⌊(t : ℝ) ^ ((e : ℝ)⁻¹)⌋₊ = rootFloor e t := by
  refine eq_of_forall_le_iff fun x => ?_
  rw [Nat.le_floor_iff (by positivity), Real.natCast_le_rpow_inv_iff he, le_rootFloor_iff he]

/-- The power of `rootCeil e t` reaches `t`. -/
theorem le_rootCeil_pow {e : ℕ} (he : e ≠ 0) (t : ℕ) : t ≤ rootCeil e t ^ e := by
  unfold rootCeil
  set G := Nat.findGreatest (fun g => g ^ e < t) t
  rcases Nat.lt_or_ge t (G + 1) with h | h
  · exact h.le.trans (Nat.le_self_pow he _)
  · exact not_lt.1 (Nat.findGreatest_is_greatest (P := fun g => g ^ e < t) (Nat.lt_succ_self G) h)

/-- `rootCeil e t` is the least `g` with `t ≤ g^e`, for `t ≥ 1`. -/
theorem rootCeil_le {e : ℕ} (he : e ≠ 0) {t g : ℕ} (ht : 1 ≤ t) (h : t ≤ g ^ e) :
    rootCeil e t ≤ g := by
  have hspec : Nat.findGreatest (fun g => g ^ e < t) t ^ e < t :=
    Nat.findGreatest_spec (P := fun g => g ^ e < t) (Nat.zero_le t)
      (show 0 ^ e < t by rw [zero_pow he]; exact ht)
  exact lt_of_pow_lt_pow_left₀ e (Nat.zero_le g) (hspec.trans_le h)

/-- The characterisation of `rootCeil` by which a program finds it. -/
theorem rootCeil_le_iff {e : ℕ} (he : e ≠ 0) {t g : ℕ} (ht : 1 ≤ t) :
    rootCeil e t ≤ g ↔ t ≤ g ^ e :=
  ⟨fun h => (le_rootCeil_pow he t).trans (Nat.pow_le_pow_left h e), rootCeil_le he ht⟩

/-- `rootCeil e t` is `⌈t^{1/e}⌉`, for `t ≥ 1`. -/
theorem ceil_rpow_inv {e : ℕ} (he : e ≠ 0) {t : ℕ} (ht : 1 ≤ t) :
    ⌈(t : ℝ) ^ ((e : ℝ)⁻¹)⌉₊ = rootCeil e t := by
  refine eq_of_forall_ge_iff fun g => ?_
  rw [Nat.ceil_le, Real.rpow_inv_le_natCast_iff he, rootCeil_le_iff he ht]

/-! ## The parameters of the proof of Theorem 19 -/

/-- "Let D be the largest power of four with D ≤ n^{1/18}". -/
def paramD₅Nat (n : ℕ) : ℕ := 4 ^ Nat.findGreatest (fun k => (4 ^ k) ^ 18 ≤ n) n

/-- "and let g := ⌈D^{1/36}⌉". -/
def paramG₅Nat (D : ℕ) : ℕ := rootCeil 36 D

/-- "Let D := ⌊n^{1/18}⌋". -/
def paramD₂₆Nat (n : ℕ) : ℕ := rootFloor 18 n

/-- "and g := ⌈D^{0.0315}⌉": the least `g` with `g^2000 ≥ D^63`. -/
def paramG₂₆Nat (D : ℕ) : ℕ := rootCeil 2000 (D ^ 63)

/-- `⌊n^{1/18}⌋`, with the exponent as the paper writes it. -/
private theorem floor_rpow_one_div (n : ℕ) : ⌊(n : ℝ) ^ (1 / 18 : ℝ)⌋₊ = rootFloor 18 n := by
  rw [← floor_rpow_inv (by norm_num)]
  norm_num

/-- "Let D := ⌊n^{1/18}⌋". -/
theorem paramD₂₆Nat_eq (n : ℕ) : paramD₂₆Nat n = paramD₂₆ n := (floor_rpow_one_div n).symm

/-- `⌊n^{1/18}⌋ ≤ n`. -/
theorem paramD₂₆Nat_le (n : ℕ) : paramD₂₆Nat n ≤ n := Nat.findGreatest_le n

/-- `⌊n^{1/18}⌋ ≥ 1` for `n ≥ 1`. -/
theorem one_le_paramD₂₆Nat {n : ℕ} (hn : 1 ≤ n) : 1 ≤ paramD₂₆Nat n :=
  le_rootFloor (by norm_num) (by simpa using hn)

/-- The greatest `k` with `(4^k)^18 ≤ n` is `⌊log₄ ⌊n^{1/18}⌋⌋`. -/
theorem findGreatest_four_pow (n : ℕ) :
    Nat.findGreatest (fun k => (4 ^ k) ^ 18 ≤ n) n = Nat.log 4 (rootFloor 18 n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [rootFloor]
  have hroot : rootFloor 18 n ≠ 0 := Nat.one_le_iff_ne_zero.1 (one_le_paramD₂₆Nat hn)
  have hiff : ∀ k, (4 ^ k) ^ 18 ≤ n ↔ k ≤ Nat.log 4 (rootFloor 18 n) := fun k => by
    rw [← le_rootFloor_iff (by norm_num), Nat.le_log_iff_pow_le (by norm_num) hroot]
  refine le_antisymm ?_ (Nat.le_findGreatest ?_ ((hiff _).2 le_rfl))
  · -- the greatest `k` satisfies the condition
    rw [← hiff]
    exact Nat.findGreatest_spec (P := fun k => (4 ^ k) ^ 18 ≤ n) (Nat.zero_le n)
      (show (4 ^ 0) ^ 18 ≤ n by rw [pow_zero, one_pow]; exact hn)
  · -- the logarithm lies within the range `≤ n` of the search
    calc Nat.log 4 (rootFloor 18 n) ≤ rootFloor 18 n := Nat.log_le_self _ _
      _ ≤ rootFloor 18 n ^ 18 := Nat.le_self_pow (by norm_num) _
      _ ≤ n := rootFloor_pow_le (by norm_num) n

/-- "Let D be the largest power of four with D ≤ n^{1/18}". -/
theorem paramD₅Nat_eq (n : ℕ) : paramD₅Nat n = paramD₅ n := by
  rw [paramD₅Nat, paramD₅, floor_rpow_one_div, findGreatest_four_pow]

/-- A power of four is at least 1. -/
theorem one_le_paramD₅Nat (n : ℕ) : 1 ≤ paramD₅Nat n := Nat.one_le_pow _ _ (by norm_num)

/-- The largest power of four below `n^{1/18}` is at most `⌊n^{1/18}⌋`. -/
theorem paramD₅Nat_le_paramD₂₆Nat {n : ℕ} (hn : 1 ≤ n) : paramD₅Nat n ≤ paramD₂₆Nat n := by
  rw [paramD₅Nat, findGreatest_four_pow]
  exact Nat.pow_log_le_self 4 (Nat.one_le_iff_ne_zero.1 (one_le_paramD₂₆Nat hn))

/-- "and let g := ⌈D^{1/36}⌉". -/
theorem paramG₅Nat_eq (n : ℕ) : paramG₅Nat (paramD₅ n) = paramG₅ n := by
  rw [paramG₅Nat, paramG₅, ← ceil_rpow_inv (by norm_num) (paramD₅Nat_eq n ▸ one_le_paramD₅Nat n)]
  norm_num

/-- "and g := ⌈D^{0.0315}⌉". -/
theorem paramG₂₆Nat_eq {n : ℕ} (hn : 1 ≤ n) : paramG₂₆Nat (paramD₂₆ n) = paramG₂₆ n := by
  have hD : 1 ≤ paramD₂₆ n := paramD₂₆Nat_eq n ▸ one_le_paramD₂₆Nat hn
  rw [paramG₂₆Nat, paramG₂₆, ← ceil_rpow_inv (by norm_num) (Nat.one_le_pow _ _ hD)]
  congr 1
  push_cast
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

/-- `⌈D^{1/36}⌉ ≤ D`. -/
theorem paramG₅Nat_le {D : ℕ} (hD : 1 ≤ D) : paramG₅Nat D ≤ D :=
  rootCeil_le (by norm_num) hD (Nat.le_self_pow (by norm_num) D)

/-- `⌈D^{0.0315}⌉ ≤ D`. -/
theorem paramG₂₆Nat_le {D : ℕ} (hD : 1 ≤ D) : paramG₂₆Nat D ≤ D :=
  rootCeil_le (by norm_num) (Nat.one_le_pow _ _ hD) (pow_le_pow_right₀ hD (by norm_num))

/-! ## The sizes of the instances of the proof of Theorem 17 -/

/-- `⌊n²/√D⌋`, the largest number of query pairs of an instance. -/
def queryCapNat (n D : ℕ) : ℕ := Nat.sqrt (n ^ 4 / D)

/-- The number of vertices `⌈s/g⌉` of a piece of `C`, with `s = ⌊√D⌋`. -/
def pieceSizeNat (D g : ℕ) : ℕ := Nat.sqrt D ⌈/⌉ g

/-- The number of pieces. -/
def numPiecesNat (n D g : ℕ) : ℕ := n ⌈/⌉ pieceSizeNat D g

/-- `queryCapNat n D` is `⌊n²/√D⌋`: both are the greatest `c` with `c² D ≤ n⁴`. -/
theorem queryCapNat_eq (n : ℕ) {D : ℕ} (hD : 1 ≤ D) : queryCapNat n D = queryCap n D := by
  refine (eq_of_forall_le_iff fun c => ?_).symm
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr (Nat.cast_pos.2 hD)
  rw [queryCap, Nat.le_floor_iff (by positivity), le_div_iff₀ hs, queryCapNat, Nat.le_sqrt',
    Nat.le_div_iff_mul_le hD, ← sq_le_sq₀ (by positivity) (by positivity), mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg D), ← pow_mul]
  exact_mod_cast Iff.rfl

/-- The test by which a program finds `queryCapNat n D`: `c + 1 ≤ ⌊n²/√D⌋` if and only if
`(c + 1)² D ≤ n⁴`. -/
theorem queryCapNat_succ_le_iff {n D : ℕ} (hD : 1 ≤ D) (c : ℕ) :
    c + 1 ≤ queryCapNat n D ↔ (c + 1) * (c + 1) * D ≤ n ^ 4 := by
  unfold queryCapNat
  rw [Nat.le_sqrt, Nat.le_div_iff_mul_le (by omega)]

/-- The largest number that this test forms. -/
theorem queryCapNat_succ_sq_mul_le {n D : ℕ} (hD : 1 ≤ D) :
    (queryCapNat n D + 1) * (queryCapNat n D + 1) * D ≤ 4 * n ^ 4 + D := by
  rcases Nat.eq_zero_or_pos (queryCapNat n D) with h | h
  · rw [h]
    omega
  · obtain ⟨c, hc⟩ : ∃ c, queryCapNat n D = c + 1 := ⟨queryCapNat n D - 1, by omega⟩
    have hle := (queryCapNat_succ_le_iff hD c).1 hc.ge
    rw [hc]
    calc (c + 1 + 1) * (c + 1 + 1) * D ≤ (2 * (c + 1)) * (2 * (c + 1)) * D :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) (by omega))
      _ = 4 * ((c + 1) * (c + 1) * D) := by ring
      _ ≤ 4 * n ^ 4 + D := by omega

/-- `s = ⌊√D⌋` is the integer square root. -/
theorem sOf_eq_sqrt (D : ℕ) : sOf D = Nat.sqrt D := Real.nat_floor_real_sqrt_eq_nat_sqrt

/-- `pieceSizeNat D g` is the number `⌈s/g⌉` of vertices of a piece, where `s = ⌊√D⌋`. -/
theorem pieceSizeNat_eq (D : ℕ) {g : ℕ} (hg : 1 ≤ g) : pieceSizeNat D g = pieceSize D g := by
  rw [pieceSize, Nat.ceil_div_eq_ceilDiv _ hg, sOf_eq_sqrt]
  rfl

/-- `numPiecesNat n D g` is the number of pieces. -/
theorem numPiecesNat_eq (n D : ℕ) {g : ℕ} (hg : 1 ≤ g) (h : 1 ≤ pieceSize D g) :
    numPiecesNat n D g = numPieces n D g := by
  rw [numPiecesNat, pieceSizeNat_eq D hg, numPieces, Nat.ceil_div_eq_ceilDiv _ h]

/-- The number of chunks of a set of pairs in integer arithmetic. -/
theorem numChunks_eq {n : ℕ} (S : Finset (Fin n × Fin n)) {cap : ℕ} (hcap : 1 ≤ cap) :
    numChunks S cap = S.card ⌈/⌉ cap := by
  rw [numChunks, Nat.ceil_div_eq_ceilDiv _ hcap]

/-- A piece has at least one vertex, and the middle part `C_k × ℤ_p` of an instance has at most `D`
vertices. -/
theorem pieceSize_mul_le {D g p : ℕ} (hD : 16 ≤ D) (hg : 1 ≤ g) (hp : p ∈ primesInRange D) :
    1 ≤ pieceSize D g ∧ pieceSize D g * p ≤ D := by
  rw [primesInRange_eq, List.mem_toFinset] at hp
  have hs : 4 ≤ Nat.sqrt D := Nat.le_sqrt'.2 (by omega)
  rw [← pieceSizeNat_eq D hg]
  refine ⟨(Nat.lt_ceilDiv_iff hg).2 (by omega), ?_⟩
  calc pieceSizeNat D g * p ≤ Nat.sqrt D * Nat.sqrt D :=
        Nat.mul_le_mul ((Nat.ceilDiv_le_iff hg).2 (Nat.le_mul_of_pos_right _ hg))
          (le_sqrt_of_mem_primesList hp)
    _ ≤ D := Nat.sqrt_le D

end ThreeSumApsp.Spec
