/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Tied.Defs
public import GeneralPieces.Rec.Seq
public import GeneralPieces.Rec.Chain
public import GeneralPieces.Rec.Descend
public import GeneralPieces.Rec.Level
public import ClauseBound.Gen.Pick
public import ClauseBound.Gen.Seq
public import ClauseBound.Alg.Need
public import ClauseBound.Alg.Enum
public import ClauseBound.Alg.Grid
public import ClauseBound.Alg.CertEnum
public import ClauseBound.Alg.CertGridG
public import ClauseBound.Alg.CertLevel
public import PaddedDescent.Col.CertG

/-! # Part (b) of Theorem A, as one statement

"One deterministic algorithm, given ℓ ≥ 0, λ, B ≥ 1 and query access to tables with |W_w| < 2^B,
outputs the value of the (K_ℓ, λ)-clique within 2^{e_ℓK_ℓ²λ}(K_ℓ(λ + B))^{C₀K_ℓ²} operations."

The algorithm is `solveG` on the schedule (40). For ℓ ≥ 1 the schedule of level ℓ has at least
g_{ℓ−1} = √K_ℓ symbols, far more than ℓ, so a program that is polynomial-time on all inputs cannot
write it down from ℓ alone.
It reads K_ℓ off the instance, whose tables are written out (the number of rows is K_ℓ), and builds
the schedule of the largest level whose number of nodes is at most that; on a (K_ℓ, λ)-clique this
is level ℓ.
So the ℓ in the input is not read. The statement is `GeneralPieces.Tied.PartB`, which names the
program (`Tied.runB`), the schedule and the hypotheses of case (ii); `AppRunningTime.PartB` follows
from it (`partB_of_tied`). The clauses: polynomial time (the certificates of the programs), the
value (all levels under the hypotheses of case (ii) of Lemma 8,
at every step of the schedule), and the bound on the exponent of the pad, a string of ones whose
length bounds the number of operations (`stRate2`). -/

public section

namespace GeneralPieces

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen

/-- K_ℓ is strictly increasing in ℓ. -/
theorem K_strictMono (x₀ : ℕ) (hx : 18 ≤ x₀) : StrictMono (K x₀) := strictMono_nat_of_lt_succ fun l => (PartA.K_lt_le x₀ l (by omega)).1

/-- On a (K_ℓ, λ)-clique the program picks level ℓ. -/
theorem pick_rows (P : PiecesF) (x₀ : ℕ) (hx : 18 ≤ x₀) (l lam B : ℕ) (I : PInst) (hI : WFe (K x₀ l) lam B I) :
    (Pick.pick P x₀ (List.replicate I.2.length ())).2 = idx P x₀ l := by
  obtain ⟨-, hp2, hp3, hp4⟩ := pick_spec P x₀
  have hmono := K_strictMono x₀ hx
  obtain ⟨b, hb⟩ : ∃ b : U, b = List.replicate I.2.length () := ⟨_, rfl⟩
  have hbl : b.length = K x₀ l := by rw [hb, List.length_replicate, hI.1.rows]
  have h3 := hp3 b (by rw [hbl]; exact hmono.monotone (Nat.zero_le l))
  have h4 := hp4 b
  rw [hbl] at h3 h4
  have hl : (Pick.pick P x₀ b).1.length = l := by
    have a1 := hmono.le_iff_le.1 h3
    have a2 := hmono.lt_iff_lt.1 h4
    omega
  rw [← hb, hp2, hl]

/-- The named program is polynomial-time in (pad, ℓ, instance), if the descent through all levels
is. -/
theorem runB_polyT (P : PiecesF) (x₀ : ℕ) (hCS : StCertSolveG P) (hKeeps : P.Keeps) : PolyT (Tied.runB P x₀) := by
  have hp1 := (pick_spec P x₀).1
  have h1 : PolyT fun p : U × U × PInst =>
      (p.1, (Pick.pick P x₀ (List.replicate p.2.2.2.length ())).2.2, (Pick.pick P x₀ (List.replicate p.2.2.2.length ())).2.1, p.2.2) := by fun_prop
  have h2 : PolyT fun p : U × U × PInst =>
      solveG P p.1 (Pick.pick P x₀ (List.replicate p.2.2.2.length ())).2.2.length (Pick.pick P x₀ (List.replicate p.2.2.2.length ())).2.1 p.2.2 :=
    PolyT.comp (f := fun p : U × U × List Step × PInst => solveG P p.1 p.2.1.length p.2.2.1 p.2.2.2)
      (g := fun p : U × U × PInst =>
        (p.1, (Pick.pick P x₀ (List.replicate p.2.2.2.length ())).2.2, (Pick.pick P x₀ (List.replicate p.2.2.2.length ())).2.1, p.2.2))
      (hCS hKeeps) h1
  exact h2

/-- Part (b) for the named program, from the interface statements; C₀ depends on c only. -/
theorem partB_tied_of (hR : StRate2) (hCh : StChain2) (hSolve : ∀ P, StSolveG2 P) (hNeed : ∀ P, StNeedG P) (hCS : ∀ P, StCertSolveG P) (c : ℕ) :
    ∃ C₀ : ℕ, ∀ (P : PiecesF) (ρ : ℝ) (x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → Par P ρ c → P.m = 1 → P.Keeps → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → Tied.PartB P ρ x₀ C₀ := by
  obtain ⟨C₀, hC⟩ := hR c
  refine ⟨C₀, fun P ρ x₀ hρ hρ1 hP hm hKeeps hx hc => ?_⟩
  have hs : ∀ (pad lu : U) (l lam B : ℕ) (I : PInst), WFe (K x₀ l) lam B I →
      Tied.runB P x₀ (pad, lu, I) = solveG P pad (K x₀ 0) (sched P x₀ l) I := fun pad lu l lam B I hI => by
    change solveG P pad (Pick.pick P x₀ (List.replicate I.2.length ())).2.2.length (Pick.pick P x₀ (List.replicate I.2.length ())).2.1 I = _
    rw [pick_rows P x₀ hx l lam B I hI]
    simp [idx, rep]
  refine ⟨runB_polyT P x₀ (hCS P) hKeeps, hs, fun l => ⟨Rate.step_K P x₀ l, Rate.step_p P x₀ l, Rate.step_d P x₀ l, Chain.zetaOf_step hm x₀ l⟩,
    fun l lam hlam => Chain.levelOK2 hP hm x₀ hx l lam hlam, fun pad l lam B I hlam _ hI hpad => ?_, fun l lam B hlam hB => hC P ρ x₀ hρ hρ1 hP hm hx hc l lam B hlam hB⟩
  rw [hs pad _ l lam B I hI]
  exact hSolve P pad (K x₀ 0) (sched P x₀ l) (K x₀ l) lam B I (hCh P ρ c x₀ hP hm hx hc l lam hlam)
    (hNeed P pad.length (K x₀ l) lam B 1 1 (sched P x₀ l) hpad) hI

/-- The form with "there is a program" follows; it does not name the recursion. -/
theorem partB_of_tied {P : PiecesF} {ρ : ℝ} {x₀ C₀ : ℕ} (h : Tied.PartB P ρ x₀ C₀) : AppRunningTime.PartB ρ x₀ C₀ :=
  ⟨Tied.runB P x₀, Tied.needB P x₀, h.poly, h.value, h.rate⟩

/-- All levels give the value of the clique, under the hypotheses of case (ii) at every step. -/
theorem solveG2 (P : PiecesF) : StSolveG2 P := Descend.stSolveG2 P (Level.stExpandG2 P (Grid.stGrid P) Enum.stEnum)

/-- The descent through all levels is polynomial-time in (pad, K₀, schedule, instance), if the
programs of the pieces are. -/
theorem certSolveG (P : PiecesF) : StCertSolveG P :=
  CertLevel.stCertSolveG P (CertGridG.stCertLam P)
    (CertLevel.stCertExpandG P (CertGridG.stCertGrid P) (CertGridG.stCertLam P) CertEnum.stCertEnum PaddedDescent.F.certRebalG) CertEnum.stCertBruteK

/-- Part (b) of Theorem A for the named program, for pieces given as polynomial-time programs whose
numbers of bits are at most 2λ; C₀ depends on c only. -/
theorem partB_tied (c : ℕ) : ∃ C₀ : ℕ, ∀ (P : PiecesF) (ρ : ℝ) (x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → Par P ρ c → P.m = 1 → P.Keeps → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ →
    Tied.PartB P ρ x₀ C₀ :=
  partB_tied_of stRate2 Chain.stChain2 solveG2 Need.stNeedG certSolveG c

end GeneralPieces
