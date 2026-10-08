/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec5.Corollary39.GraphH.PairCount
public import ThreeSumApsp.RunningTimes.FromClaims.Bounds
public import ThreeSumApsp.RunningTimes.Sec5.Corollary39.ZeroWeightLayout
public import ThreeSumApsp.TimeClaims.Sec5.Corollary39

/-!
# Corollary 39, the zero-weight case, on the word RAM

Corollary 39 reduces weighted k-Clique to triangle problems on N = n^⌊k/3⌋ vertices per
part, one for each of the n^t choices of the fixed vertices.

* The host that builds the graph H and calls a solver of Exact Triangle takes at most n^t (T(N, ·) +
  C N²) steps (`exists_kcTime_le`; the arithmetic is `hostTime_le`).
* A host with such a time proves the transfer claim of the proof of Corollary 39
  for programs of the light language, that is, for the reading `lightModel5` of "is solved in time
  T" (`solvedIn_of_hostTime`, `claim_zeroCliqueFromExactTriangle`).
* With the bound of Theorem 19 for Exact Triangle, the arithmetic of the running times, which holds
  for any reading of "is solved in time T" (`zeroClique_of_theorem_19`), gives O(n^{k -
  ε_T ⌊k/3⌋}), and `realized_zeroKClique` and `FromClaims.solvedAt_of_realized` carry it to the word
  RAM (`corollary_39_zero_of_theorem_19`).
-/

public section

open ThreeSumApsp.Spec

namespace Light.Sec5

open ThreeSumApsp ThreeSumApsp.WordRam ThreeSumApsp.KClique

/-! ## The time of a host -/

/-- Writing the three weight matrices of H takes a constant times N² steps. -/
theorem exists_fillT_le (k : ℕ) :
    ∃ C, ∀ N, 1 ≤ N → fillT k N 0 + fillT k N 1 + fillT k N 2 ≤ C * (N * N) := by
  have hone : ∀ i : Fin 3, ∀ N, 1 ≤ N →
      fillT k N i ≤ (21 * (pairsH k i).length + 28 * width k + 49) * (N * N) := fun i N hN =>
    calc fillT k N i
        = (21 * (pairsH k i).length + 14 * width k + 22) * (N * N) + (14 * width k + 19) * N +
          8 * 1 := by unfold fillT matTime rowTime entryTime; ring
      _ ≤ (21 * (pairsH k i).length + 14 * width k + 22) * (N * N) +
          (14 * width k + 19) * (N * N) + 8 * (N * N) := by
        gcongr
        · exact Nat.le_mul_of_pos_left N hN
        · exact Nat.mul_pos hN hN
      _ = (21 * (pairsH k i).length + 28 * width k + 49) * (N * N) := by ring
  exact ⟨_, fun N hN => (Nat.add_le_add (Nat.add_le_add (hone 0 N hN) (hone 1 N hN))
    (hone 2 N hN)).trans_eq (by rw [← Nat.add_mul, ← Nat.add_mul])⟩

/-- The arithmetic of the time of a host: P rounds, each of F ≤ c X steps, a call of t₀ steps and a
further steps, and b ≤ b' X steps outside the rounds. -/
theorem hostTime_le {P X F t₀ a b c b' : ℕ} (hP : 1 ≤ P) (hX : 1 ≤ X) (hF : F ≤ c * X)
    (hb : b ≤ b' * X) : P * (F + t₀ + a) + b ≤ P * (t₀ + (c + a + b') * X) :=
  calc P * (F + t₀ + a) + b ≤ P * (c * X + t₀ + a * X) + P * (b' * X) := by
        gcongr
        · exact Nat.le_mul_of_pos_right a hX
        · exact hb.trans (Nat.le_mul_of_pos_left _ hP)
    _ = P * (t₀ + (c + a + b') * X) := by ring

/-- The time of the host: n^t calls of the solver, and a constant times N² steps for each of them
(proof of Corollary 39: t = numFixed k, N = n ^ width k). -/
theorem exists_kcTime_le (k : ℕ) : ∃ C : ℕ, ∀ (T : ℕ → ℕ → ℕ) (n U : ℕ), 1 ≤ n →
    kcTime k T n U ≤ n ^ numFixed k *
      (T (n ^ width k) (lenH k * U) + C * (n ^ width k * n ^ width k)) := by
  obtain ⟨c, hc⟩ := exists_fillT_le k
  refine ⟨c + (14 * numFixed k + 29) + (2 * width k + 2 * numFixed k + 5 * k + 38),
    fun T n U hn => ?_⟩
  have hN : 1 ≤ n ^ width k := Nat.one_le_pow _ _ hn
  have hX : 1 ≤ n ^ width k * n ^ width k := Nat.mul_pos hN hN
  refine le_of_eq_of_le ?_ (hostTime_le (Nat.one_le_pow _ _ hn) hX (hc _ hN)
    (Nat.le_mul_of_pos_right _ hX))
  unfold kcTime roundT
  ring

/-- `1 + log(max(u, 2))` is at least 1. -/
theorem one_le_one_add_logU (u : ℝ) : 1 ≤ 1 + logU u :=
  le_add_of_nonneg_right (Real.log_nonneg (le_trans (by norm_num) (le_max_right _ _)))

/-- A host that takes at most n^t (T(N, ℓU) + C N²) steps, where ℓ is the number of pairs of parts,
transfers running times as the proof of Corollary 39 says. -/
theorem solvedIn_of_hostTime {k : ℕ} (hk : 3 ≤ k) {lower upper : Task}
    {time : (ℕ → ℕ → ℕ) → ℕ → ℕ → ℕ} {need : (ℕ → ℕ → Need) → ℕ → ℕ → Need}
    (hhost : IsHost lower upper time need) {C : ℕ}
    (htime : ∀ (T : ℕ → ℕ → ℕ) (n U : ℕ), 1 ≤ n → time T n U ≤ n ^ numFixed k *
      (T (n ^ width k) (lenH k * U) + C * (n ^ width k * n ^ width k)))
    {T : ℕ → ℝ → ℝ} (hT : SolvedIn lower T) :
    SolvedIn upper fun n u => (n : ℝ) ^ numFixed k * (T (n ^ (k / 3)) ((k.choose 2 : ℝ) * u) +
      (C : ℝ) * (((n ^ (k / 3) : ℕ) : ℝ) ^ 2 * (1 + logU u))) := by
  refine hhost.solvedIn hT fun Tn hTn n U u hn hU hu => ?_
  have hweights : ((lenH k * U : ℕ) : ℝ) ≤ (k.choose 2 : ℝ) * u := by
    rw [lenH_eq_choose]
    push_cast
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  have hcall := hTn (n ^ width k) (lenH k * U) _ (Nat.one_le_pow _ _ hn)
    (Nat.mul_pos (lenH_pos hk) hU) hweights
  have hlog := one_le_one_add_logU u
  calc (time Tn n U : ℝ)
      ≤ ((n ^ numFixed k * (Tn (n ^ width k) (lenH k * U) +
          C * (n ^ width k * n ^ width k)) : ℕ) : ℝ) := by exact_mod_cast htime Tn n U hn
    _ = (n : ℝ) ^ numFixed k * ((Tn (n ^ width k) (lenH k * U) : ℝ) +
          (C : ℝ) * (((n ^ width k : ℕ) : ℝ) ^ 2 * 1)) := by push_cast; ring
    _ ≤ (n : ℝ) ^ numFixed k * (T (n ^ width k) ((k.choose 2 : ℝ) * u) +
          (C : ℝ) * (((n ^ width k : ℕ) : ℝ) ^ 2 * (1 + logU u))) := by gcongr

/-! ## Corollary 39, the zero-weight case -/

/-- **The transfer claim of the proof of Corollary 39** holds for programs of the light
language. -/
theorem claim_zeroCliqueFromExactTriangle {k : ℕ} (hk : 3 ≤ k) :
    Claim.ZeroCliqueFromExactTriangle lightModel5 k :=
  let ⟨C, hC⟩ := exists_kcTime_le k
  ⟨C, fun _ hT => solvedIn_of_hostTime hk (isHost_kc hk) hC hT⟩

/-- **Corollary 39, the zero-weight case, on the word RAM**, from the bound of Theorem 19 for Exact
Triangle for programs of the light language. -/
theorem corollary_39_zero_of_theorem_19 (h19 : Claim.Theorem_19_explicit lightModel 0.00175 1) :
    Items.Corollary_39_zero := by
  intro k hk
  have hclaim := zeroClique_of_theorem_19 lightModel5 k hk h19
    (claim_zeroCliqueFromExactTriangle hk)
  refine FromClaims.solvedInTime_of_one_le (Q := EndStatement.ZeroWeightKClique k) kList_zero
    fun κ hκ => ?_
  obtain ⟨T, hT, C, hb⟩ := hclaim κ (by exact_mod_cast hκ)
  exact FromClaims.solvedAt_of_realized T κ (realized_zeroKClique k (by omega) T hT) (C := C)
    (by simpa only [pow_zero, mul_one] using hb)

end Light.Sec5
