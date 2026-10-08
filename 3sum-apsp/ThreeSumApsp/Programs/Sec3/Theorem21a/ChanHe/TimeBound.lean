/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.LightModel
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Time
public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Sizes

/-!
# The arithmetic of the reduction from 3SUM to Convolution-3SUM

Theorem 21(a), after [CH20, Theorem 5.1]. Two statements about the time and
the need of the host (`chTime`, `chNeed`), which are explicit expressions in the number n of
integers and the bound on their absolute values.

* The need is polynomially bounded if the need of the solver of Convolution-3SUM is
  (`polyNeed_chNeed`).
* For inputs of absolute value at most n^κ, the host's own work is n^{3/2} times a polylogarithm, it
  calls the solver polylogarithmically often, and all calls are at the same length, which is n times
  a polylogarithm, and with the same bound on the numbers, which is polynomial in n. This gives the
  transfer of running times (`claim_CH20_Theorem_5_1_of_host`).

Both are proved by following the expressions, in the calculus `Scale.SoftO` of orders of growth:
`SoftOSqrtPow F i` says that F(n) is at most a polylogarithm times (⌊√n⌋ + 1)^i, and `PolyBounded F`
that F(n, U) is at most a polynomial in (n + 1)(U + 1).
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe Finset

/-! ## The host on inputs of absolute value at most `n^k` -/

/-- The bound `V = 2 n^k` with which the host works. -/
abbrev boundAt (k n : ℕ) : ℕ := 2 * n ^ k

/-- The host's own work. -/
def ownAt (k n : ℕ) : ℕ := 20 * k + 40 + coreOwn n (boundAt k n)

/-- The number of calls of the solver. -/
def callsAt (k n : ℕ) : ℕ := coreCalls n (boundAt k n)

/-- The bound on the numbers of the instances that the solver is asked. -/
def magAt (k n : ℕ) : ℕ := 60 * boundAt k n + 40

/-- The time of the host is its own work plus the calls of the solver, which are all at one length
and with one bound. -/
theorem chTime_eq {k n U : ℕ} (hU : U ≤ n ^ k) (Tn : ℕ → ℕ → ℕ) :
    chTime k Tn n U = ownAt k n + callsAt k n * Tn (lenOf k n) (magAt k n) := by
  simp only [chTime, coreTime, lenOf, ownAt, callsAt, magAt, boundAt, max_eq_right hU]
  omega

namespace ClaimF

/-! ## The time functions at the bound `V = 2 n^k`

In `SoftOSqrtPow F i` the index 0 stands for a polylogarithm, 1 for `Õ(√n)`, 2 for `Õ(n)` and 3 for
`Õ(n^{3/2})`.  The bound `m` on the primes has the index 1 (`softO_mPar`). -/

section own

variable (k : ℕ)

/-- The number of candidate primes, which is at most the bound `m` on the primes. -/
abbrev numPrimes (n : ℕ) : ℕ := #(Nat.primesLE (mPar n (boundAt k n)))

/-- The number of candidate primes is `Õ(√n)`. -/
theorem softO_numPrimes : SoftOSqrtPow (numPrimes k) 1 :=
  (softO_mPar k).of_le fun _ _ => Nat.card_primesLE_le _

/-- One remainder takes a step for each binary digit. -/
theorem softO_tEmod : SoftOSqrtPow (fun n => tEmod (boundAt k n)) 0 := by
  unfold tEmod
  growth_sqrt []

/-- The remainders of `n` numbers. -/
theorem softO_tResid : SoftOSqrtPow (fun n => tResid n (boundAt k n)) 2 := by
  unfold tResid
  growth_sqrt [softO_tEmod k]

/-- One pass over `n` remainders. -/
theorem softO_tTally : SoftOSqrtPow (fun n => tTally n) 2 := by
  unfold tTally
  growth_sqrt []

/-- The colliding pairs of a set of `n` numbers modulo one prime. -/
theorem softO_tColl : SoftOSqrtPow (fun n => tColl n (boundAt k n)) 2 := by
  unfold tColl
  growth_sqrt [softO_tResid k, softO_tTally]

/-- The heavy elements of a set of `n` numbers. -/
theorem softO_tHeavy : SoftOSqrtPow (fun n => tHeavy n (boundAt k n)) 2 := by
  unfold tHeavy
  growth_sqrt [softO_tResid k, softO_tTally]

/-- One search goes through the `Õ(√n)` candidate primes, at `Õ(n)` steps each. -/
theorem softO_tSearch : SoftOSqrtPow (fun n => tSearch (numPrimes k n) n n n (boundAt k n)) 3 := by
  unfold tSearch
  growth_sqrt [softO_numPrimes k, softO_tColl k]

/-- The modulus of a node: two searches. -/
theorem softO_tModulus :
    SoftOSqrtPow (fun n => tModulus (numPrimes k n) n n n (boundAt k n)) 3 := by
  unfold tModulus
  growth_sqrt [softO_tSearch k, softO_tColl k]

/-- The array of a node has `O(m²) = Õ(n)` cells. -/
theorem softO_tNodeArray :
    SoftOSqrtPow (fun n => tNodeArray (mPar n (boundAt k n)) n n n (boundAt k n)) 2 := by
  unfold tNodeArray
  growth_sqrt [softO_mPar k, softO_tResid k, softO_tTally]

/-- One call of the recursive procedure, without the call of the solver. -/
theorem softO_nodeOwn :
    SoftOSqrtPow (fun n => nodeOwn n (boundAt k n) (mPar n (boundAt k n)) (numPrimes k n)) 3 := by
  unfold nodeOwn
  growth_sqrt [softO_tModulus k, softO_tNodeArray k, softO_tHeavy k]

/-- The recursive procedure is called polylogarithmically often for one three-set input. -/
theorem softO_callsB : SoftOSqrtPow (fun n => callsB n) 0 := by
  unfold callsB
  growth_sqrt [Scale.SoftO.of_forall_le three_pow_fuel_le]

/-- The routines params and prep cost `Õ(n)`. -/
theorem softO_tSetup : SoftOSqrtPow (fun n => tSetup n (boundAt k n)) 2 := by
  unfold tSetup tParams tPrep tLog2 tPrimes tSort tDistinct tBits
  growth_sqrt [softO_wPar k, softO_mPar k, softO_Lam k]

/-- The host's own work is `Õ(n^{3/2})`. -/
theorem softO_ownAt : SoftOSqrtPow (ownAt k) 3 := by
  unfold ownAt coreOwn inputsB tPick tTwice tZeroThree
  growth_sqrt [softO_tSetup k, softO_nodeOwn k, softO_callsB, softO_Lam k]

/-- The host calls the solver polylogarithmically often. -/
theorem softO_callsAt : SoftOSqrtPow (callsAt k) 0 := by
  unfold callsAt coreCalls inputsB
  growth_sqrt [softO_callsB, softO_Lam k]

end own

end ClaimF

/-- **The need of the host is polynomially bounded** if the need of the solver is.  The number of
binary digits and the number of levels of the recursion are at most linear. -/
theorem polyNeed_chNeed (κ : ℕ) (r : ℕ → ℕ → Need) (hr : PolyNeed r) : PolyNeed (chNeed κ r) := by
  have hfuel : ∀ n, fuel n ≤ 3 * (n + 2) := fun n => by
    have h1 : height n ≤ Nat.log 2 n + 2 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    have h2 : Nat.log 2 n ≤ n := Nat.log_le_self _ _
    unfold fuel
    omega
  have hm : PolyBounded fun n U => mPar n (2 * max U (n ^ κ)) := by
    unfold mPar wPar Lam
    growth_poly []
  unfold chNeed coreNeed coreCells nodesNeed modulusNeed wordNeed Lam
  poly_need [hr.word, hr.cells, hr.depth, hm, Scale.SoftO.of_forall_le hfuel]

/-- [CH20, Theorem 5.1] for programs of the light language, from the host: 3SUM from
Convolution-3SUM.  For inputs of absolute value at most `n^κ` the host is taken with the parameter
`k = ⌈κ⌉`. -/
theorem claim_CH20_Theorem_5_1_of_host (h : ∀ κ : ℕ, IsHost c3Task s3Task (chTime κ) (chNeed κ)) :
    Claim.CH20_Theorem_5_1 lightModel := by
  intro κ _
  have hκ : κ ≤ ⌈κ⌉₊ := Nat.le_ceil κ
  generalize ⌈κ⌉₊ = k at hκ
  refine ⟨fun n => ownAt k n, fun n => callsAt k n, fun n => magAt k n, lenOf k, 160, k,
    (ClaimF.softO_ownAt k).isPowPolylog (by norm_num),
    (ClaimF.softO_callsAt k).isPowPolylog (by norm_num), isPowPolylog_lenOf k,
    fun n hn => ⟨one_le_lenOf k n, ?_, ?_⟩, ?_⟩
  · exact Nat.one_le_cast.2 (by unfold magAt boundAt; omega)
  · have hpow : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn
    have hmag : magAt k n ≤ 160 * n ^ k := by unfold magAt boundAt; omega
    rw [Real.rpow_natCast]
    change (magAt k n : ℝ) ≤ _
    exact_mod_cast hmag
  rintro T ⟨P, p, Tn, r, hr, hsol, hT⟩
  obtain ⟨R, p', hsol'⟩ := (h k).1 P p Tn r hsol
  refine ⟨timeUpTo (chTime k Tn), hsol'.solvedIn ((h k).2 r hr), fun n hn =>
    timeUpTo_le fun U hU => ?_⟩
  have hUk : U ≤ n ^ k := by
    have hle : (U : ℝ) ≤ (n : ℝ) ^ (k : ℝ) := (hU.trans_eq (max_eq_left (by positivity))).trans
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hκ)
    rw [Real.rpow_natCast] at hle
    exact_mod_cast hle
  rw [chTime_eq hUk]
  push_cast
  gcongr
  exact hT _ _ _ (one_le_lenOf k n) (by unfold magAt boundAt; omega) le_rfl

end Light.Sec3.ChanHe
