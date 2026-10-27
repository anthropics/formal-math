/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppRunningTimeStatement
public import GeneralPieces.Group.Lemma
public import GeneralPieces.Rec.PartB
public import GeneralPieces.Rec.Seq
public import GeneralPieces.Num.PartA
public import GeneralPieces.Num.PartAUse
public import GeneralPieces.Num.PartD
public import GeneralPieces.Num.TopDisplay
public import GeneralPieces.DefGenPieces.MayAssume
public import ClauseBound.Gen.End
public import ClauseBound.ParityChecks.MasterOL
public import GeneralPieces.Top.CaseI
public import GeneralPieces.Top.EndM
import all ClauseBound.ParityChecks.MasterOL
import all ClauseBound.TopN.Arith
import all ClauseBound.TopN.Gen
import ClauseBound.Alg.NeedC
import ClauseBound.Alg.Decode
import ClauseBound.Alg.TopVal
import ClauseBound.Alg.CertTop
import ClauseBound.Alg.End
import ClauseBound.ParityChecks.EndOL
import ClauseBound.ParityChecks.TopOL
import ClauseBound.ParityChecks.CertTopOL
import ClauseBound.ParityChecks.CertOL
import ClauseBound.ParityChecks.BudgetOL
import ClauseBound.ParityChecks.ArithOL
import ClauseBound.ParityChecks.Ev
import ClauseBound.ParityChecks.Count
import ClauseBound.ParityChecks.Shape
import ClauseBound.ParityChecks.Bridge
import ClauseBound.ParityChecks.ChoiceByPotential
import ClauseBound.TopN.Budget
import ClauseBound.TopN.Walk
import ClauseBound.Alg.CertTopNet
import PaddedDescent.F.MarkCode
import PaddedDescent.F.MarkVal
import PaddedDescent.F.MarkProf
import PaddedDescent.F.MarkSize
import PaddedDescent.F.CertMark
import CountKSatRate.Tree
import CountKSatRate.Walk
import CountKSatRate.Pad
import CountKSatRate.Brute
import CountKSatRate.Stack
import CountKSat.InOut

/-! # Theorem A (the running time as a function of m and n), assembled

Parts (a) to (d) as stated in `AppRunningTimeStatement.lean`. "Suppose that there are pieces with
parameters (ρ, c)": by "we may and do assume", the recursion has programs whose numbers of bits are
at most 2λ, with the
same c. Parts (b) and (c) run the recursion through case (ii) of Lemma 8 at every level, with an x₀
of the theorem; for part (c) it is the least one,
x₀ = max(18, ⌈log(c + 5)⌉). The top levels of part (c), which turn a k-CNF into networks on 3K⁸
nodes and rebalance each once, call case (i) of Lemma 8 (`GeneralPieces.Top`); the remaining
arguments,
for the bound in m and the bound in n, take as given the display in the paper's proof of part (c)
(`Num/TopDisplay.lean`) and part (a) (`Num/PartAUse.lean`). Part (d) follows from a stronger bound
on 3-SAT (`PartD.thmRunningTime_d`), which does not go through parts (a) to (c). -/

public section

namespace GeneralPieces

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen

/-- x₀Of c ≥ 18. -/
theorem x₀Of_ge (c : ℕ) : 18 ≤ x₀Of c := le_max_left _ _

/-- 2^{x₀Of c} ≥ c + 5. -/
theorem x₀Of_pow (c : ℕ) : c + 5 ≤ 2 ^ x₀Of c :=
  (Nat.le_pow_clog (by norm_num) _).trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))

/-- Parts (a) and (b) in the form that the top levels use, with every interface statement proved. -/
theorem seq2 : StSeq2 := stSeq2 Chain.stChain2 solveG2

/-- The solver that a family of pieces gives is polynomial-time, if the programs of the pieces are. -/
theorem solver_poly (P : PiecesF) (hKeeps : P.Keeps) : (solverOf P).Poly :=
  solverOf_poly (certSolveG P) (CertLevel.stCertNeedC P (CertGridG.stCertLam P)) (NeedC.stNeedC P) hKeeps

/-- The solver has K_ℓ nodes at the index of level ℓ. -/
theorem K_idx (P : PiecesF) (x₀ l : ℕ) : (solverOf P).K (idx P x₀ l) = K x₀ l := ClauseBound.Gen.Seq.topK_idx P x₀ l

/-- Part (c), first sentence, for the named programs: pieces whose numbers of bits are at most 2λ
and any x₀ of the theorem. The network of the formula is rebalanced by case (i) of Lemma 8
(`Top.stCountG2`); the exponent is bounded through the display in the paper's proof of part (c) and
"every term after 2ekm is O(k·m^{1−1/90})" (`TopDisplay.top_level`, `top_arith`); the level is "the
largest ℓ with K_ℓ ≤ m^{1/9}", and e_ℓ = O((log m)^{−α'}) there by
part (a) (`PartAUse.e_le_rPow`). -/
theorem partC_m_tied {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hP : Par P ρ c) (hm : P.m = 1) (hKeeps : P.Keeps) (hx : 18 ≤ x₀)
    (hc : c + 5 ≤ 2 ^ x₀) : Tied.PartCm P ρ x₀ := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := pick_spec P x₀
  obtain ⟨C₀, Q, hQ, hpick⟩ := seq_of_pick Chain.stChain2 stRate2 solveG2 Need.stNeedG P ρ c x₀ hρ hρ1 hP hm hx hc (Pick.pick P x₀) hp1 hp2 hp3 hp4
  unfold Tied.PartCm
  rw [← hpick]
  refine Top.topM_of_arith CountKSatRate.stPaddedW (TopVal.stCorrectM Decode.stDecM (Top.stCountG2 TopVal.stSatPresentsK))
    (CertTop.stCertM Decode.stCertDecM CertTop.stCertSatK PaddedDescent.F.certRebalG) (solverOf P) (e ρ x₀) C₀ Q
    ⟨_, fun k m hk hm => TopDisplay.top_arith P ρ x₀ C₀ hρ hx Q hQ k m hk (by rwa [hQ, K_idx] at hm)⟩ (solver_poly P hKeeps) _
    (91 * (3 * x₀ + 6)) (fun m _ => le_rPow (alpha_mem hρ hρ1).2 (by omega) m) fun m _ => ?_
  refine PartAUse.e_le_rPow hρ hρ1 hx ?_
  have h := Q.pick_max (root9 m)
  rwa [hQ, K_idx] at h

open PaddedDescent CountKSat CountKSatRate ClauseBound.ParityChecks ClauseBound.TopN in
/-- The top level in n, for a solver with a sequence of levels; every network of marks is rebalanced
by case (i) of Lemma 8. -/
theorem endO2 : StEndO :=
  EndOL.stEndO stPaddedW
    (TopOL.stCorrectO
      (Count.stCountOL (Ev.stEvW (Mark.Val.stMarkVal stEncLen stEncInj) Mark.Prof.stProfSum Mark.Val.stMarkPresents stMarkSized Top.stValS2)
        Shape.stShape Bridge.stBridgeB Bridge.stBridgeA Bridge.stBridgeF stepTwo)
      BudgetOL.stBudgetO stParN (stWalkCount stTreeK stWalkS stRoundS stRoundSEnd stStateLen stCntToN stDecU) stBruteC stDecU)
    (CertTopOL.stCertO (CertOL.stCertCountOL (CertTopNet.stCertValS certRebalG) certMark certAdm)) ArithOL.stArithO

open ClauseBound.ParityChecks ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.TopN.GenN in
/-- Part (c), second sentence, for programs whose numbers of bits are at most 2λ and any x₀ of the
theorem; what the choice of the level needs of K_ℓ and e_ℓ comes from part (a)
(`PartAUse.inv_two_pow_le_e`, `two_pow_le_div`, `e_mul_le`). -/
theorem partC_n {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ} (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hP : Par P ρ c) (hm : P.m = 1) (hKeeps : P.Keeps) (hx : 18 ≤ x₀)
    (hc : c + 5 ≤ 2 ^ x₀) (k : ℕ) (hk : 1 ≤ k) : SatK.CountInRateN k (SatK.rN 1 (Real.logb 2 (1 / ρ))) := by
  obtain ⟨C₀, Q, hQ⟩ := seq2 P ρ c x₀ hρ hρ1 hP hm hx hc
  have hA := PartA.thmRunningTime_a ρ x₀ hρ hρ1 hx
  obtain ⟨C, hC⟩ : ∃ C : ℕ, ρ ^ C ≤ 1 / 2 := by
    obtain ⟨C, hC⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 2) hρ1
    exact ⟨C, hC.le⟩
  refine endO2 _ (solverOf P) (e ρ x₀) C₀ Q (solver_poly P hKeeps) (fun u => () :: u) (C + 1) (by fun_prop)
    (fun l => ?_) (fun l => ?_) k _ (3 * (171 * (3 * x₀ + 6))) hk (fun n _ => MasterOL.le_rN (alpha_mem hρ hρ1).2 (by omega) n) fun n hn => ?_
  · simpa using PartAUse.inv_two_pow_le_e hA hρ l
  · simpa using PartAUse.two_pow_le_div hA hρ hρ1 hC l
  · obtain ⟨hr1, hr2⟩ := root17_spec n
    have hK0 : (solverOf P).K (Q.idx 0) ≤ (root17 n).length := by
      by_contra h
      have h' := Nat.pow_le_pow_left (Nat.succ_le_of_lt (not_le.1 h)) 17
      exact absurd (h'.trans hn) (not_le.2 hr2)
    have hle := Q.pick_le _ hK0
    have hmax := Q.pick_max (root17 n)
    rw [Q.pick_idx, hQ, K_idx] at hle
    rw [hQ, K_idx] at hmax
    have h := PartAUse.e_mul_le (l := (Q.pick (root17 n)).1.length) (n := n) hρ hρ1 hx ((Nat.pow_le_pow_left hle 17).trans hr1)
      (hr2.trans_le (Nat.pow_le_pow_left (Nat.succ_le_of_lt hmax) 17))
    simpa [SatK.rN] using h

/-- ½ ≤ ρ < 1 is part of the definition of pieces. -/
theorem rho_of_exist {ρ : ℝ} {c : ℕ} (h : AppRunningTime.Exist ρ c) : 1 / 2 ≤ ρ ∧ ρ < 1 :=
  let ⟨_, _, _, hP⟩ := h
  ⟨hP.rho_ge, hP.rho_lt⟩

/-- The programs that the recursion runs on, for pieces (P, val) with parameters (ρ, c): "we may and
do assume" (`trimV`), read in the form of the recursion (`atZero`); they have m = 1 and the same c. -/
theorem par_of_isPieces {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} (h : AppRunningTime.IsPieces ρ c P A val) :
    Par (atZero (trimV P val c) c 1) ρ c ∧ (atZero (trimV P val c) c 1).Keeps ∧ (atZero (trimV P val c) c 1).m = 1 :=
  to_par_one (trimV_isPieces h) fun tr lam i _ _ => trimV_cap_le P val c tr 0 lam i

/-- Part (b) for the named program, from pieces as in the definition of the appendix; C₀ depends
only on c. -/
theorem thmRunningTime_b_tied (c : ℕ) : ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), AppRunningTime.IsPieces ρ c P A val →
    18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → Tied.PartB (atZero (trimV P val c) c 1) ρ x₀ C₀ := by
  obtain ⟨C₀, hC⟩ := partB_tied c
  refine ⟨C₀, fun ρ x₀ P A val h hx hc => ?_⟩
  obtain ⟨hP, hKeeps, hm⟩ := par_of_isPieces h
  exact hC _ ρ x₀ h.rho_ge h.rho_lt hP hm hKeeps hx hc

/-- Part (c), first sentence, for the named programs, from pieces as in the definition of the
appendix, with any x₀ of the theorem. -/
theorem thmRunningTime_c_m_tied_at {ρ : ℝ} {c x₀ : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} (h : AppRunningTime.IsPieces ρ c P A val)
    (hx : 18 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) : Tied.PartCm (atZero (trimV P val c) c 1) ρ x₀ := by
  obtain ⟨hP, hKeeps, hm⟩ := par_of_isPieces h
  exact partC_m_tied h.rho_ge h.rho_lt hP hm hKeeps hx hc

/-- The same with the least x₀ of the theorem. -/
theorem thmRunningTime_c_m_tied {ρ : ℝ} {c : ℕ} {P : PiecesF} {A : (lam : ℕ) → ℕ → Pieces.Four lam} {val : AppRunningTime.ValQ → ℤ} (h : AppRunningTime.IsPieces ρ c P A val) :
    Tied.PartCm (atZero (trimV P val c) c 1) ρ (x₀Of c) :=
  thmRunningTime_c_m_tied_at h (x₀Of_ge c) (x₀Of_pow c)

/-- Part (a). -/
theorem thmRunningTime_a (ρ : ℝ) (x₀ : ℕ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) : AppRunningTime.PartA ρ x₀ :=
  let h := PartA.thmRunningTime_a ρ x₀ hρ hρ1 hx
  ⟨h.logK, h.K_lt_le, h.e_bounds, h.rho_pow⟩

/-- Part (b); C₀ depends only on c. This form says "there is a program" and does not name the
recursion; `thmRunningTime_b_tied` does. The pieces are first brought to numbers of bits at most 2λ
by "we may and do assume" as printed (`exist_par_one`). -/
theorem thmRunningTime_b (c : ℕ) : ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ), AppRunningTime.Exist ρ c → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → AppRunningTime.PartB ρ x₀ C₀ := by
  obtain ⟨C₀, hC⟩ := partB_tied c
  refine ⟨C₀, fun ρ x₀ hE hx hc => ?_⟩
  obtain ⟨P, hP, hKeeps, hm⟩ := exist_par_one hE
  exact partB_of_tied (hC P ρ x₀ (rho_of_exist hE).1 (rho_of_exist hE).2 hP hm hKeeps hx hc)

/-- Part (c), first sentence. This form says "there is a machine" and does not name the programs;
`thmRunningTime_c_m_tied` does (the proof below does not use it). The proof goes as the appendix
does: take pieces, "we may and do assume" that their numbers of bits are at most 2λ
-/
theorem thmRunningTime_c_m (ρ : ℝ) (c : ℕ) (hE : AppRunningTime.Exist ρ c) : SatM.CountInRate (SatM.rPow (AppRunningTime.alpha' ρ)) := by
  obtain ⟨P, A', val, h⟩ := hE
  obtain ⟨P', h', -, hcap⟩ := mayAssume ρ c P A' val h
  obtain ⟨hP, hKeeps, hm⟩ := to_par_one h' fun tr lam i _ _ => hcap tr lam i
  exact Top.countInRate_of_topM (partC_m_tied h.rho_ge h.rho_lt hP hm hKeeps (x₀Of_ge c) (x₀Of_pow c))

/-- Part (c), second sentence. Only this form, which says "there is a machine", is stated; no form
names the programs. The appendix's proviso (a number between 0.85ρ^ℓ and ρ^ℓ computable from ℓ in
time polynomial in
K_ℓ) is not needed. -/
theorem thmRunningTime_c_n (ρ : ℝ) (c : ℕ) (hE : AppRunningTime.Exist ρ c) (k : ℕ) (hk : 1 ≤ k) : SatK.CountInRateN k (SatK.rN 1 (AppRunningTime.alpha' ρ)) := by
  obtain ⟨P, hP, hKeeps, hm⟩ := exist_par_one hE
  exact partC_n (rho_of_exist hE).1 (rho_of_exist hE).2 hP hm hKeeps (x₀Of_ge c) (x₀Of_pow c) k hk

/-- Part (d). It is derived in `PartD.thmRunningTime_d` from a bound on 3-SAT with the exponent
3/19, which the paper does not state and which is proved with a lemma on groupings other than Lemma
8; parts (a) to (c) do not use that bound. -/
theorem thmRunningTime_d (ρ : ℝ) (c : ℕ) (hE : AppRunningTime.Exist ρ c) : Sat3.InRateTM (AppRunningTime.alpha' ρ / 10) :=
  PartD.thmRunningTime_d ρ (rho_of_exist hE).1 (rho_of_exist hE).2

/-- Theorem A, all four parts. -/
theorem thmRunningTime : AppRunningTime.ThmRunningTime := ⟨thmRunningTime_a, thmRunningTime_b, thmRunningTime_c_m, thmRunningTime_c_n, thmRunningTime_d⟩

end GeneralPieces
