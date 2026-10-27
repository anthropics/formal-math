/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.TopDefs
import CountKSatRate.Leaf
import PaddedDescent.Choice
import all CountKSat.Top.Count

/-! # Correctness of the function `AO`

`stCorrectO : StCorrectO`. For the constant c, the number n₀ is the larger of 2^20 and the n₀ of
`exists_n0 c`. If the plan is `none`, the exponent is n and the function counts exhaustively
(`StBruteC`). Otherwise the plan says that s ≥ s0K k, that Δ = 2^(betaN k s) ≤ n + 1, that n ≥ n₀,
that Δ ≤ (⌊log₂ n⌋ + 1)^c, that 2·⌈log₂(2Δ)⌉ ≤ n, and that the exponent is `needO`. Then the
parameters
satisfy what the choice of the checks needs (`exists_n0`), the pad suffices for the count of a leaf
(`StBudgetO`, `FitsOL`), so that this count is right (`StCountOL`), and for the walk
(`StWalkCount`). -/

namespace ClauseBound.ParityChecks.TopOL

open Groundwork Groundwork.Prog CountKSat PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks
open WidthK (theta bsum leafC)
open PaddedDescent.F.Mark (WfL occ nSat)

/-- What a plan says. -/
theorem planAtO_some {Idx : Type} [Enc Idx] {S : Solver Idx} (hS : S.Poly) {c n₀ k n s v : ℕ} {i : Idx} (h : planAtO S c n₀ k n i s = some v) :
    (s0K k ≤ s ∧ 2 ^ betaN k s ≤ n + 1 ∧ n₀ ≤ n ∧ 2 ^ betaN k s ≤ (Nat.log 2 n + 1) ^ c ∧ 2 * LD (2 ^ betaN k s) ≤ n) ∧ v = needO S k i n s := by
  unfold planAtO at h
  split_ifs at h with hc
  obtain ⟨v', h1, h2⟩ := Option.bind_eq_some_iff.1 h
  split_ifs at h2 with hc2
  obtain ⟨u, h3, h4⟩ := Option.map_eq_some_iff.1 h1
  have hu := hS.needC_eq _ _ _ h3
  refine ⟨hc, ?_⟩
  rw [← Option.some.inj h2, ← h4, hu]
  rfl

/-- The threshold is at least k² for every k ≤ s. -/
theorem sq_le_tauOf {k s : ℕ} (h : k ≤ s) : k ^ 2 ≤ tauOf s := by
  calc k ^ 2 ≤ (2 ^ s) ^ 2 := Nat.pow_le_pow_left (h.trans Nat.lt_two_pow_self.le) 2
    _ = 2 ^ (s * 2) := (pow_mul 2 s 2).symm
    _ ≤ 2 ^ (4 * s + 17) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- ⌈log₂(2Δ)⌉ ≥ 1 for Δ ≥ 1. -/
theorem LD_pos {Δ : ℕ} (h : 1 ≤ Δ) : 0 < LD Δ := Nat.clog_pos (by norm_num) (by omega)

/-- nb ≥ 2 if 2·⌈log₂(2Δ)⌉ ≤ n. -/
theorem two_le_nbOf {n Δ : ℕ} (hΔ : 1 ≤ Δ) (h : 2 * LD Δ ≤ n) : 2 ≤ nbOf n Δ := (Nat.le_div_iff_mul_le (LD_pos hΔ)).2 h

/-- n < 2·nb·⌈log₂(2Δ)⌉ if nb ≥ 1. -/
theorem lt_two_mul_nbOf {n Δ : ℕ} (hΔ : 1 ≤ Δ) (h : 1 ≤ nbOf n Δ) : n < 2 * (nbOf n Δ * LD Δ) := by
  have h1 := Nat.lt_mul_div_succ n (LD_pos hΔ)
  have h2 : LD Δ * (n / LD Δ + 1) = nbOf n Δ * LD Δ + LD Δ := by rw [nbOf]; ring
  have h3 : LD Δ ≤ nbOf n Δ * LD Δ := Nat.le_mul_of_pos_left _ h
  omega

/-- i₀ is at most the cap, for n ≥ 2^20. -/
theorem i0_le_capM {n : ℕ} (hn : 2 ^ 20 ≤ n) (Δ m : ℕ) : (parOf n Δ m).i₀ ≤ capM (parOf n Δ m) := by
  have hL : 20 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) hn
  have h1 : i0Of n ≤ n := by
    unfold i0Of
    rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
    have : 20 * n ≤ Nat.log 2 n * n := Nat.mul_le_mul_right n hL
    omega
  simp only [capM, parOf]
  omega

/-- The end of the correctness side. -/
public theorem stCorrectO (hC : StCountOL) (hB : StBudgetO) (hPar : StParN) (hWC : StWalkCount) (hBr : StBruteC) (hD : StDecU) : StCorrectO := by
  intro c
  obtain ⟨n₁, hn₁⟩ := exists_n0 c
  refine ⟨max (2 ^ 20) n₁, ?_⟩
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = max (2 ^ 20) n₁ := ⟨_, rfl⟩
  rw [← hn₀]
  intro Idx _ S e C₀ Q hS slU k n φ hk h3 pad hpad
  have hdec : decU k (SatK.enc k φ) = (List.replicate n (), Decode.toN φ) := hD k n φ hk h3.1
  have hn : nK k (SatK.enc k φ) = n := by rw [nK, hdec, List.length_replicate]
  obtain ⟨i, hi⟩ : ∃ i, i = idxN k Q.pick (SatK.enc k φ) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = precN k Q.pick slU (SatK.enc k φ) := ⟨_, rfl⟩
  have hplan : planO S c n₀ k Q.pick slU (SatK.enc k φ) = planAtO S c n₀ k n i s := by rw [planO, hn, hi, hs]
  have hnum : (bif (planO S c n₀ k Q.pick slU (SatK.enc k φ)).isNone then bruteN k (SatK.enc k φ, pad)
      else numOL S k (idxN k Q.pick (SatK.enc k φ)) (precN k Q.pick slU (SatK.enc k φ)) (SatK.enc k φ, pad)) = SatK.numSat φ := by
    rw [eO, hplan, hn] at hpad
    rw [hplan, ← hi, ← hs]
    cases hpl : planAtO S c n₀ k n i s with
    | none =>
      rw [hpl, Option.getD_none] at hpad
      simpa using hBr k n φ hk h3 pad hpad
    | some v =>
      rw [hpl, Option.getD_some] at hpad
      obtain ⟨⟨c1, c2, c3, c4, c5⟩, c6⟩ := planAtO_some hS hpl
      have hblock : blockN k n s = 2 ^ betaN k s := min_eq_left c2
      obtain ⟨Δ, hΔ⟩ : ∃ Δ, Δ = blockN k n s := ⟨_, rfl⟩
      rw [← hblock, ← hΔ] at c4 c5
      rw [c6, needO, pow_add, ← hΔ] at hpad
      have hp1 : 2 ^ needNet S i (UbOL k (S.K i) n Δ) (PbOL (S.K i) n Δ) 0 ≤ pad.length :=
        le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) hpad
      have hp2 : 2 ^ restO k (S.K i) n s ≤ pad.length := le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) hpad
      obtain ⟨b1, b2, b3, b4⟩ := hB k (S.K i) n s pad.length hk c1 hp2
      rw [← hΔ] at b1 b2
      have q1 : leafC (tauOf s) k + 2 ≤ Δ := by rw [hΔ, hblock]; exact (hPar k n s).1
      have hks : k ≤ s := le_of_s0K_le c1
      have hΔ2 : 2 ≤ Δ := by omega
      have hn20 : 2 ^ 20 ≤ n := le_trans (by rw [hn₀]; exact le_max_left _ _) c3
      have hnn₁ : n₁ ≤ n := le_trans (by rw [hn₀]; exact le_max_right _ _) c3
      have hnb : 2 ≤ nbOf n Δ := two_le_nbOf (by omega) c5
      have hoki : ∃ l, i = Q.idx l := ⟨_, hi.trans (Q.pick_idx _)⟩
      have hK2 : 2 ≤ S.K i := by obtain ⟨l, rfl⟩ := hoki; exact Q.K_two l
      simp only [Option.isNone_some, cond_false, numOL, hn]
      refine hWC k (tauOf s) n φ pad _ hk h3 (sq_le_tauOf hks) b3 b4 fun x hxl hx1 ho hs' => ?_
      obtain ⟨m1, m2, m3, m4⟩ := Leaf.spec hk hx1 ho hs'
      have hlen : (leafM x).length ≤ Δ * n := (m1.trans hxl).trans (Nat.mul_le_mul_right _ q1)
      unfold valO
      rw [← hΔ, hC Idx S (fun i => ∃ l, i = Q.idx l) Q.correct k pad i n Δ (leafM x) (2 / 2 ^ (10 * n)) hoki hK2 m2 (fun v => (m3 v).trans q1) hlen hnb
        (lt_two_mul_nbOf (by omega) (by omega))
        (fun hlt => by
          obtain ⟨e1, e2, e3, -⟩ := hn₁ n hnn₁ Δ (leafM x).length hΔ2 c4 hlt hlen
          exact ⟨e1, e2, e3, i0_le_capM hn20 _ _⟩)
        ⟨hp1, b1, b2⟩, m4]
  unfold AO
  simp only [hnum, hdec]
  exact CountTop.outW_eq _ _ _

end ClauseBound.ParityChecks.TopOL
