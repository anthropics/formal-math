/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Prog
public import PaddedDescent.F.Interfaces
public import ClauseBoundStatement

/-! # The interface lemmas, as PROPOSITIONS

As in proof/rates/PaddedDescent/F/Interfaces.lean: definitions `St… : Prop`; nothing is proved and
nothing is assumed here. One file proves `theorem … : St…`; a file that needs such a lemma imports
that
file or takes `(h : St…)` as a hypothesis, and the final assembly feeds the proofs in. -/

@[expose] public section

namespace ClauseBound.Alg

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F

/-- I is an instance on K nodes with labels of exactly lam ≥ 1 bits and entries of absolute value at
most 2^B. -/
def WFe (K lam B : ℕ) (I : PInst) : Prop := WF K lam B I ∧ I.1.length = lam

/-! ### Enum.lean -/

def StEnum : Prop := ∀ (C : Type) (pad : U) (g : ℕ) (F : FNet C) (c : C) (N : Network (Fin g) (List Bool) (List Bool)),
  F.toP.Presents c N 0 0 → 2 ^ enumBits g F c ≤ pad.length → (∀ a < g, 2 ^ F.n c a ≤ pad.length) →
  enumF pad g F c = N.value ∧ 2 * enumBits g F c = N.U

/-! ### Grid*.lean: the networks of the terms of one level on a p × d grid, for any pieces -/

def StGrid (P : PiecesF) : Prop := ∀ (pad pu du hu ℓu : U) (T : Tab) (B : ℕ), 1 ≤ ℓu.length → P.Spec hu.length ℓu.length →
  2 ^ P.need hu.length ℓu.length ≤ pad.length → BoundedInst ℓu.length B (instOf (K := pu.length * du.length) T) →
  ∃ Zt : ℕ → ℤ,
    (P.d hu.length ℓu.length : ℤ) ^ nRectG pu.length du.length * Inst.ZW ℓu.length [] (instOf (K := pu.length * du.length) T) =
      ∑ y ∈ Finset.range (P.cnt hu.length ℓu.length ^ nRectG pu.length du.length), Zt y ∧
    ∀ y < P.cnt hu.length ℓu.length ^ nRectG pu.length du.length, ∀ tr : Bool,
      ∃ N : Network (Fin (nParts pu.length du.length tr)) (List Bool) (List Bool),
        (gridF P).toP.Presents ((pad, (pu, du), tr, hu), (ℓu, y, T)) N 0 0 ∧ N.value = Zt y ∧
        N.Sized (P.m * (nParts pu.length du.length tr * nMemb pu.length du.length tr ^ 2 * ℓu.length))
          (nMemb pu.length du.length tr * B + nMemb pu.length du.length tr ^ 2 * P.bits hu.length ℓu.length) ∧
        N.U = totalG P pu.length du.length tr hu.length ℓu.length y ∧
        ∀ a b, a ≠ b → N.c a b ≤ nMemb pu.length du.length tr ^ 2 * (P.m * ℓu.length)

/-! ### The pad for a schedule of levels -/

/-- The pad of length F suffices for a state with at most cnt instances on Kup nodes (labels lam,
entries ≤ 2^B), a sum and a factor of at most z bits, and for all steps below. -/
def FitsG (P : PiecesF) (F : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → List Step → Prop
  | Kup, lam, B, cnt, z, [] => cnt * instLen Kup lam B + 8 * z + 4 * lam + 40 ≤ F ∧ 2 ^ (Kup * (Kup - 1) / 2 * lam) ≤ F
  | Kup, lam, B, cnt, z, s :: r =>
      cnt * instLen Kup lam B + 8 * z + 4 * lam + 40 ≤ F ∧ BudG P F s lam ∧
        FitsG P F s.K (lamNextG P s lam) (bNextG P s lam B) (cnt * nPat P s lam)
          (z + nRectG s.p s.d * Nat.size (P.d s.h lam) + Nat.size (cnt * nPat P s lam) + Nof s lam +
            s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h lam + 1) + 2) r

/-- The exponent of a pad that suffices: the largest of the exponents of all the budgets of `FitsG`,
computed from the schedule. -/
def needG (P : PiecesF) : ℕ → ℕ → ℕ → ℕ → ℕ → List Step → ℕ
  | Kup, lam, B, cnt, z, [] => max (max (Nat.size (cnt * instLen Kup lam B + 8 * z + 4 * lam + 40)) (max lam (max (Nat.size B) (Nat.size Kup)))) (Kup * (Kup - 1) / 2 * lam)
  | Kup, lam, B, cnt, z, s :: r =>
      max (max (Nat.size (cnt * instLen Kup lam B + 8 * z + 4 * lam + 40)) (max lam (max (Nat.size B) (Nat.size Kup))))
        (max (max (max (P.need s.h lam) (Nat.size (nPat P s lam))) (max (s.p * Nat.size s.K) (PnG P s lam * (2 * s.p / s.K + 1))))
          (max (max ((s.K - 1) * lamNextG P s lam) (if s.thin = true then max (ebarG s lam) (s.p ^ 2 * s.d * lam) else 0))
            (needG P s.K (lamNextG P s lam) (bNextG P s lam B) (cnt * nPat P s lam)
              (z + nRectG s.p s.d * Nat.size (P.d s.h lam) + Nat.size (cnt * nPat P s lam) + Nof s lam +
                s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h lam + 1) + 2) r)))

def StNeedG (P : PiecesF) : Prop := ∀ (F Kup lam B cnt z : ℕ) (sched : List Step), 2 ^ needG P Kup lam B cnt z sched ≤ F → FitsG P F Kup lam B cnt z sched

/-! The exponent `needG` can be huge for a senseless schedule, so the machine computes it under a
bound b: the state of the computation is cut off when its word gets longer than 100·(b+2). -/

/-- ((label length in unary, B), (cnt, z), (number of nodes, largest exponent so far)). -/
abbrev NState : Type := (U × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)

/-- One step of the computation of `needG`. -/
def needStep (P : PiecesF) (st : NState) (s : Step) : NState :=
  ((List.replicate (lamNextG P s st.1.1.length) (), bNextG P s st.1.1.length st.1.2),
   (st.2.1.1 * nPat P s st.1.1.length,
    st.2.1.2 + nRectG s.p s.d * Nat.size (P.d s.h st.1.1.length) + Nat.size (st.2.1.1 * nPat P s st.1.1.length) + Nof s st.1.1.length +
      s.d ^ 2 * (s.p * st.1.2 + s.p ^ 2 * P.bits s.h st.1.1.length + 1) + 2),
   (s.K,
    max st.2.2.2 (max (max (Nat.size (st.2.1.1 * instLen st.2.2.1 st.1.1.length st.1.2 + 8 * st.2.1.2 + 4 * st.1.1.length + 40)) (max st.1.1.length (max (Nat.size st.1.2) (Nat.size st.2.2.1))))
      (max (max (max (P.need s.h st.1.1.length) (Nat.size (nPat P s st.1.1.length))) (max (s.p * Nat.size s.K) (PnG P s st.1.1.length * (2 * s.p / s.K + 1))))
        (max ((s.K - 1) * lamNextG P s st.1.1.length) (if s.thin = true then max (ebarG s st.1.1.length) (s.p ^ 2 * s.d * st.1.1.length) else 0))))))

/-- The end of that computation. -/
def needFin (st : NState) : ℕ :=
  max st.2.2.2 (max (max (Nat.size (st.2.1.1 * instLen st.2.2.1 st.1.1.length st.1.2 + 8 * st.2.1.2 + 4 * st.1.1.length + 40)) (max st.1.1.length (max (Nat.size st.1.2) (Nat.size st.2.2.1))))
    (st.2.2.1 * (st.2.2.1 - 1) / 2 * st.1.1.length))

/-- `needG P Kup lam B 1 1 sched` if it is at most the length of b, computed with cut-offs; `none`
otherwise. -/
def needC (P : PiecesF) (b : U) (Kup lam B : ℕ) (sched : List Step) : Option ℕ :=
  (sched.foldl (fun o s => cap (List.replicate (100 * (b.length + 2)) ()) none (o.map fun st => needStep P st s))
    (cap (List.replicate (100 * (b.length + 2)) ()) none (some ((List.replicate lam (), B), (1, 1), (Kup, 0))))).bind fun st =>
      if needFin st ≤ b.length then some (needFin st) else none

def StNeedC (P : PiecesF) : Prop := ∀ (b : U) (Kup lam B : ℕ) (sched : List Step),
  (∀ v, needC P b Kup lam B sched = some v → v = needG P Kup lam B 1 1 sched) ∧
  (needG P Kup lam B 1 1 sched ≤ b.length → needC P b Kup lam B sched = some (needG P Kup lam B 1 1 sched))

/-! ### The polynomial-time certificates -/

def StCertEnum : Prop := ∀ (C : Type) [Enc C] (F : FNet C), FKeeps F → ∀ (α : Type) [Enc α] (pad : α → U) (g : α → ℕ) (c : α → C),
  PolyT pad → Unary g → PolyT c → PolyT fun t => enumF (pad t) (g t) F (c t)

def StCertGrid (P : PiecesF) : Prop := P.Keeps → FKeeps (gridF P)
def StCertLam (P : PiecesF) : Prop := P.Keeps → Unary fun p : Step × U => lamNextG P p.1 p.2.length
def StCertExpandG (P : PiecesF) : Prop := P.Keeps → PolyT fun p : U × Step × PInst => expandG P p.1 p.2.1 p.2.2
def StCertBruteK : Prop := PolyT fun p : U × U × PInst => bruteF p.1 p.2.1.length p.2.2
def StCertSolveG (P : PiecesF) : Prop := P.Keeps → PolyT fun p : U × U × List Step × PInst => solveG P p.1 p.2.1.length p.2.2.1 p.2.2.2
def StCertNeedC (P : PiecesF) : Prop := P.Keeps →
  PolyT fun p : U × (U × U × U) × List Step => needC P p.1 p.2.1.1.length p.2.1.2.1.length p.2.1.2.2.length p.2.2

/-! ### The clique solver: the form in which part (b) of Theorem A, and the hypothesis of Theorem D(a), are used -/

/-- One algorithm for the cliques on K i nodes, i in an index type that is data. `need` is the
exponent of a pad that suffices, as a function of (i, λ, B). -/
structure Solver (Idx : Type) [Enc Idx] where
  K : Idx → ℕ
  run : U × Idx × PInst → ℤ
  need : Idx × U × U → ℕ
  /-- `need`, computed under a bound in unary: `none` if it is larger than the bound -/
  needC : U × Idx × U × U → Option ℕ

namespace Solver
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-- The algorithm is right when the pad is long enough. -/
def Correct (ok : Idx → Prop) : Prop := ∀ (pad : U) (i : Idx) (lam B : ℕ) (I : PInst), ok i → 1 ≤ lam → WFe (S.K i) lam B I →
  2 ^ S.need (i, List.replicate lam (), List.replicate B ()) ≤ pad.length → S.run (pad, i, I) = zval (S.K i) I

/-- It is polynomial-time in (pad, index, instance); K is computed in unary, the exponent under a
bound. -/
structure Poly : Prop where
  run : PolyT S.run
  K : Unary S.K
  needC : PolyT S.needC
  needC_eq : ∀ b x v, S.needC (b, x) = some v → v = S.need x
  needC_some : ∀ (b : U) x, S.need x ≤ b.length → S.needC (b, x) = some (S.need x)

end Solver

/-- The number of nodes at the top of a schedule. -/
def topK (i : List Step × U) : ℕ := match i.1 with
  | [] => i.2.length
  | s :: _ => s.p * s.d

/-- The solver that a family of pieces gives: the index is (schedule, K₀ in unary). -/
def solverOf (P : PiecesF) : Solver (List Step × U) where
  K := topK
  run x := solveG P x.1 x.2.1.2.length x.2.1.1 x.2.2
  need x := needG P (topK x.1) x.2.1.length x.2.2.length 1 1 x.1.1
  needC x := needC P x.1 (topK x.2.1) x.2.2.1.length x.2.2.2.length x.2.1.1

/-- A sequence of indices of a solver with the hypotheses of Theorem D(a), and a way to pick the
right index. -/
structure Solver.Seq {Idx : Type} [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) where
  idx : ℕ → Idx
  K_two : ∀ l, 2 ≤ S.K (idx l)
  K_lt : ∀ l, S.K (idx l) < S.K (idx (l + 1))
  K_le : ∀ l, S.K (idx (l + 1)) ≤ S.K (idx l) ^ C₀
  e_le : ∀ l, e l ≤ 1
  e_ge : ∀ l, 1 / Real.logb 2 (S.K (idx l)) ^ C₀ ≤ e l
  correct : S.Correct fun i => ∃ l, i = idx l
  rate : ∀ (l lam B : ℕ), 1 ≤ lam → 1 ≤ B → (S.need (idx l, List.replicate lam (), List.replicate B ()) : ℝ) ≤
    e l * (S.K (idx l) : ℝ) ^ 2 * lam + C₀ * (S.K (idx l) : ℝ) ^ 2 * Real.logb 2 (S.K (idx l) * (lam + B))
  /-- from a bound in unary: the number l and the index of the largest l with K_l ≤ bound (l = 0 if
  there is none) -/
  pick : U → U × Idx
  pick_poly : PolyT pick
  pick_idx : ∀ b, (pick b).2 = idx (pick b).1.length
  pick_le : ∀ b, S.K (idx 0) ≤ b.length → S.K (pick b).2 ≤ b.length
  pick_max : ∀ b, b.length < S.K (idx ((pick b).1.length + 1))

/-! ### The top level in m -/

/-- The network of a k-CNF with g and k in the context: ((g, k) in unary, ψ). -/
def satFk : FNet ((U × U) × Fml) where
  n c _ := Count.mu c.1.1.length c.2 * c.1.2.length
  cap c a b := Count.capF c.1.1.length c.1.2.length c.2 a b
  W x := Count.wF x.1.1.1.length x.1.1.2.length (x.1.2, x.2)
  f x := Count.fF x.1.1.1.length x.1.1.2.length (x.1.2, x.2)

def StSatPresentsK : Prop := ∀ (gu ku : U) (ψ : Fml), 0 < gu.length → satFk.toP.Presents ((gu, ku), ψ) (Count.wordNet gu.length ku.length ψ) 0 0

end ClauseBound.Alg
