/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Prog
public import StepMachines.Math.SideNet
public import ThreeSatStatement

/-! # The interface lemmas, as PROPOSITIONS

The main lemmas that connect the files of this folder are written here as definitions `St… : Prop`.
Nothing is proved and nothing is assumed: this
file has no theorem. One file proves `theorem … : St…`. A file that needs such a lemma either
imports that file or takes `(h : St…)` as a hypothesis; in
the second case the final assembly (proof/rates/PaddedDescent/Main.lean) feeds the proof in. No file
contains a placeholder proof. -/

@[expose] public section

namespace PaddedDescent.F

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Prog.Count Groundwork.Grid Groundwork.Sparsify
open WidthK (theta bsum leafC)
open WidthK.Prog (stepK)
open PaddedDescent.F.Mark (Cl vio nvio Tpl Tsg trunc Good nSat occ layersE Asked enc MCtx markF markN adm nProf cls WfL vset layP sgnP Match)

/-- θ is a well-formed query at v: labels of ℓ bits, the empty word at v itself. -/
def WFQ {K : ℕ} (ℓ : ℕ) (v : Fin K) (θ : Fin K → List Bool) : Prop := (∀ u, u ≠ v → (θ u).length = ℓ) ∧ θ v = []

/-! ### Table.lean -/

def StT1 : Prop := ∀ (K ℓ : ℕ) (R R' : Inst (Fin K) (List Bool)),
  (∀ v θ, WFQ ℓ v θ → R v θ = R' v θ) → Inst.ZW ℓ [] R = Inst.ZW ℓ [] R'

def StT2 : Prop := ∀ (pad : U) (K ℓ : ℕ) (F : IQ → ℤ), 2 ^ ((K - 1) * ℓ) ≤ pad.length →
  ∀ (v : Fin K) (θ : Fin K → List Bool), WFQ ℓ v θ → look (tabulate pad K ℓ F) (v.1, List.ofFn θ) = F (v.1, List.ofFn θ)

def StT3a : Prop := ∀ (pad : U) (K ℓ Λ B : ℕ) (F : IQ → ℤ), 2 ^ ((K - 1) * ℓ) ≤ pad.length → 1 ≤ ℓ → ℓ ≤ Λ →
  (∀ (v : Fin K) (θ : Fin K → List Bool), WFQ ℓ v θ → (F (v.1, List.ofFn θ)).natAbs ≤ 2 ^ B) →
  WF K Λ B (List.replicate ℓ (), tabulate pad K ℓ F)

def StT3b : Prop := ∀ (K Λ B : ℕ) (I : PInst), WF K Λ B I → len I + 2 ≤ instLen K Λ B

def StT3c : Prop := ∀ (K Λ B : ℕ) (I : PInst), WF K Λ B I → BoundedInst I.1.length B (instOf (K := K) I.2)

/-! ### RebalF.lean: the rebalancing, from a network on g nodes to an explicit instance on K nodes -/

def StR : Prop := ∀ (C : Type) (pad : U) (K g : ℕ) (F : FNet C) (c : C) (N : Network (Fin g) (List Bool) (List Bool)) (P B : ℕ),
  2 ≤ K → 3 * K ^ 8 ≤ g → F.toP.Presents c N 0 0 → N.Sized P B →
  K ^ g ≤ pad.length → 2 ^ (P * (2 * g / K)) ≤ pad.length → 2 ^ P ≤ pad.length → 2 ^ ((K - 1) * betaC K g F.toP c) ≤ pad.length →
  ∃ J, rebalF pad K g F c = some J ∧ zval K J = N.value ∧ K ^ 3 * J.1.length ≤ K ^ 3 + K * N.U + g * P ∧
    WF K J.1.length (P * (2 * g / K) + B * (2 * g / K + 2 * g / K * (2 * g / K)) * K) J

/-! ### RebalG.lean: the rebalancing at the levels, on a grid of side g = K·L -/

/-- `StR` for `rebalG`: the label length β is given. -/
def StRG : Prop := ∀ (C : Type) (pad : U) (K g β : ℕ) (F : FNet C) (c : C) (N : Network (Fin g) (List Bool) (List Bool)) (P B M : ℕ),
  2 ≤ K → ColOK K g → F.toP.Presents c N 0 0 → N.Sized P B → 0 < M → (∀ a b, a ≠ b → N.c a b ≤ M) → 1 ≤ β →
  Dcol * N.U + 3 * g ^ 2 * M ≤ Dcol * K ^ 2 * β →
  K ^ g ≤ pad.length → 2 ^ (P * (2 * g / K)) ≤ pad.length → 2 ^ P ≤ pad.length → 2 ^ ((K - 1) * β) ≤ pad.length →
  ∃ J, rebalG pad K g β F c = some J ∧ zval K J = N.value ∧ J.1.length = β ∧
    WF K β (P * (2 * g / K) + B * (2 * g / K + 2 * g / K * (2 * g / K)) * K) J

/-! ### SideF.lean and Expand.lean: one level -/

def StS : Prop := ∀ (pad gU : U) (tr : Bool) (ℓU : U) (y : ℕ) (T : Tab), 2 ^ ℓU.length ≤ pad.length →
  sideF.toP.Presents ((pad, gU, tr), (ℓU, y, T)) (sideN gU.length tr ℓU.length (instOf (K := gU.length * gU.length) T) y) 0 0

/-- One pattern: the core of `StE`. -/
def StChild : Prop := ∀ (pad : U) (L : Lvl) (Λ B : ℕ) (I : PInst) (y : ℕ), 2 ≤ L.1.length → ColOK L.1.length L.2.length →
  WF (L.2.length * L.2.length) Λ B I → Bud pad.length L.1.length L.2.length Λ → y < (I.1.length + 1) ^ nRect L.2.length →
  ∃ J, childF pad L I y = some J ∧ zval L.1.length J = sideZ L.2.length I.1.length (instOf (K := L.2.length * L.2.length) I.2) y ∧
    WF L.1.length (lamNext L.1.length L.2.length Λ) (bNext L.1.length L.2.length Λ B) J

def StE : Prop := ∀ (pad : U) (L : Lvl) (Λ B : ℕ) (I : PInst), 2 ≤ L.1.length → ColOK L.1.length L.2.length →
  WF (L.2.length * L.2.length) Λ B I → Bud pad.length L.1.length L.2.length Λ →
  ((expand pad L I).map (zval L.1.length)).sum = zval (L.2.length * L.2.length) I ∧
  (∀ J ∈ expand pad L I, WF L.1.length (lamNext L.1.length L.2.length Λ) (bNext L.1.length L.2.length Λ B) J) ∧
  (expand pad L I).length ≤ (Λ + 1) ^ nRect L.2.length

/-! ### Descend.lean: brute force at the bottom, and all levels -/

def StBrute : Prop := ∀ (pad : U) (K : ℕ) (I : PInst), 2 ^ (K * (K - 1) / 2 * I.1.length) ≤ pad.length → bruteF pad K I = zval K I

def StD : Prop := ∀ (pad : U) (sched : List Lvl) (Kup Λ B : ℕ) (I : PInst), Chain Kup sched → Fits pad.length Kup Λ B 1 sched →
  WF Kup Λ B I → ((descend pad sched I).map (bruteF pad 256)).sum = zval Kup I

/-! ### MarkLayers.lean: the choice of the layers -/

/-- If the evaluation function is exact on the lists that are asked, the cap is at least n + 2 and
there are enough layers, then the last evaluation is the
number of satisfying assignments. -/
def StLayersE : Prop := ∀ (n w R : ℕ) (ev : List Fml → ℤ) (ψ : Fml), n + 2 ≤ w → 2 ^ R * ψ.length + 5 * 3 ^ R ≤ 3 ^ R * w →
  (∀ Ls, Asked n w R ψ Ls → ev Ls = trunc n w Ls) → ev ([] :: layersE ev w R ψ) = (nSat n ψ : ℤ)

/-! ### MarkCode.lean: the code of the labels -/

def StEncLen : Prop := ∀ (β b : ℕ) (x : List Bool), 0 < b → (enc β b x).length = x.count true * (1 + β) + (x.length + b - 1) / b

def StEncInj : Prop := ∀ (β b : ℕ) (x x' r r' : List Bool), 0 < b → b ≤ 2 ^ β → x.length = x'.length →
  enc β b x ++ r = enc β b x' ++ r' → x = x' ∧ r = r'

/-! ### MarkVal.lean, MarkProf.lean, MarkPi.lean, MarkSize.lean: the network of marks -/

def StMarkPresents : Prop := ∀ c : MCtx, markF.toP.Presents c (markN c.1.1.length c) 0 0

/-- The value of the network of one profile, admissible or not. -/
def StMarkVal : Prop := ∀ (k : ℕ) (gu nu βu bu : U) (Ls : List Fml) (y : ℕ), 0 < gu.length → 0 < bu.length → bu.length ≤ 2 ^ βu.length → WfL k nu.length Ls →
  (markN gu.length ((gu, nu, βu, bu), (Ls, y))).value =
    ∑ σ : Fin nu.length → Bool, ∑ P ∈ (vset (Mark.ext σ) Ls).powerset,
      by classical exact if Match gu.length nu.length Ls y P then sgnP Ls P else 0

/-- Every set of clause indices has exactly one profile number whose digits below the diagonal are
0; that number is admissible iff no layer has more than w
members of the set. -/
def StProfSum : Prop := ∀ (k g n w : ℕ) (Ls : List Fml) (P : Finset ℕ), 0 < g → WfL k n Ls → P ⊆ Finset.range (cls Ls).length →
  (∑ y ∈ Finset.range (nProf g (cls Ls).length Ls.length),
    by classical exact if adm k g n w Ls y = true ∧ Match g n Ls y P then (1 : ℤ) else 0) =
    (by classical exact if ∀ i < Ls.length, (layP Ls P i).card ≤ w then 1 else 0 : ℤ)

/-- The signed sum over the sets of violated clauses with at most w members in every layer. -/
def StPiSum : Prop := ∀ (w : ℕ) (Ls : List Fml) (σ : ℕ → Bool),
  (∑ P ∈ (vset σ Ls).powerset, by classical exact if ∀ i < Ls.length, (layP Ls P i).card ≤ w then sgnP Ls P else 0) =
    Tpl w (nvio σ (Ls.headD [])) * (Ls.tail.map fun L => Tsg w (nvio σ L)).prod

/-- The central identity: the values of the networks of the admissible profiles add up to the
cut-off sum. No hypothesis on the layers beyond their form. -/
def StMarkSum : Prop := ∀ (k : ℕ) (gu nu βu bu : U) (w : ℕ) (Ls : List Fml), 0 < gu.length → 0 < bu.length → bu.length ≤ 2 ^ βu.length → WfL k nu.length Ls →
  ∑ y ∈ Finset.range (nProf gu.length (cls Ls).length Ls.length),
    (if adm k gu.length nu.length w Ls y = true then (markN gu.length ((gu, nu, βu, bu), (Ls, y))).value else 0) = trunc nu.length w Ls

/-- The size of the network of an admissible profile, if every variable occurs in at most Δ clauses
and there are at most b·(n + 1) clauses. -/
def StMarkSized : Prop := ∀ (k : ℕ) (gu nu βu bu : U) (w Δ : ℕ) (Ls : List Fml) (y : ℕ), 0 < gu.length → 0 < bu.length → bu.length ≤ 2 ^ βu.length →
  WfL k nu.length Ls → (∀ v, (occ Ls.flatten v).length ≤ Δ) → Ls.flatten.length ≤ bu.length * (nu.length + 1) → adm k gu.length nu.length w Ls y = true →
  (markN gu.length ((gu, nu, βu, bu), (Ls, y))).Sized (Pb gu.length nu.length βu.length Δ) 0 ∧
    (markN gu.length ((gu, nu, βu, bu), (Ls, y))).U ≤ Ub k gu.length nu.length w βu.length Ls.length

/-! ### Eval.lean and Top.lean: one evaluation, one sparse formula, the sparsification tree, the whole function -/

/-- `valF` computes the value of every network that F presents, if its entries are 0, 1, −1 and the
pad is long enough. -/
def StValF : Prop := ∀ (C : Type) (F : FNet C) (c : C) (pad : U) (S : List Lvl × U) (Ub₀ P : ℕ)
  (N : Network (Fin (gU S.2).length) (List Bool) (List Bool)), NetFits pad.length S Ub₀ P → F.toP.Presents c N 0 0 → N.Sized P 0 → N.U ≤ Ub₀ →
  valF pad S F c = N.value

/-- One evaluation is exact: at most R₁ layers, which together hold at most m clauses, every
variable in at most Δ of them. -/
def StEval : Prop := ∀ (k : ℕ) (pad : U) (S : List Lvl × U) (p : U × U × U × U) (Ls : List Fml) (R₁ Δ m : ℕ),
  NetFits pad.length S (Ub k (3 * S.2.length ^ 8) p.1.length p.2.1.length p.2.2.1.length R₁) (Pb (3 * S.2.length ^ 8) p.1.length p.2.2.1.length Δ) →
  nProf (3 * S.2.length ^ 8) m R₁ ≤ pad.length → 0 < p.2.2.2.length → p.2.2.2.length ≤ 2 ^ p.2.2.1.length → m ≤ p.2.2.2.length * (p.1.length + 1) →
  WfL k p.1.length Ls → (∀ v, (occ Ls.flatten v).length ≤ Δ) → Ls.flatten.length ≤ m → Ls.length ≤ R₁ →
  evalF k pad S p Ls = trunc p.1.length p.2.1.length Ls

/-- `countM k` counts the satisfying assignments of a formula with clauses of 1 to k literals. -/
def StCountM : Prop := ∀ (k : ℕ) (pad : U) (S : List Lvl × U) (p : U × U × U × U) (R Δ m : ℕ) (ψ : Fml),
  MarkFits k pad.length S p.1.length p.2.2.1.length p.2.2.2.length R Δ m → p.2.1.length = p.1.length + 2 →
  WfL k p.1.length [ψ] → (∀ v, (occ ψ v).length ≤ Δ) → ψ.length ≤ m → countM k pad S p R ψ = (nSat p.1.length ψ : ℤ)

/-- Every leaf of the sparsification tree at width k has nonempty clauses only, and every variable
occurs in at most leafC τ k of them. -/
def StLeaf : Prop := ∀ (k τ n : ℕ) (ψ : PFml), 1 ≤ τ → (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) →
  ∀ x ∈ leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ), (∀ C ∈ x, C ≠ []) ∧ ∀ v, (occ x v).length ≤ leafC τ k

def StWalk : Prop := ∀ (k : ℕ) (pad : U) (τ : ℕ) (test : PFml → Bool) (r : PFml) (d : ℕ),
  (∀ x ∈ leaves (stepK (theta τ) k) d r, stepK (theta τ) k x = none) → 2 * (leaves (stepK (theta τ) k) d r).length ≤ pad.length + 1 →
  (∀ i, len ((roundB (stepK (theta τ) k) test)^[i] ([r], false)) ≤ pad.length) →
  walkF k pad τ test r = (leaves (stepK (theta τ) k) d r).any test

/-- The end of the correctness side; this is the last hypothesis, `h`, of `inRateTM_of_algorithm`
(proof/rates/PaddedDescent/Reduce.lean). -/
def StCorrect (C₀ s₀ : ℕ) : Prop := ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ → s₀ ≤ sOf n →
  (A (Sat3.enc φ, List.replicate (2 ^ (C₀ * (n / 2 ^ sOf n + 1))) ()) = true ↔ Sat3.Satisfiable φ)

/-! ### The arithmetic (the files Arith*.lean): the pad is long enough -/

def StSched : Prop := ∀ (pad : U) (t : ℕ), schedLen t ≤ pad.length →
  schedF pad t = (schedL t, List.replicate (Kseq t) (), List.replicate (Lseq t) ())

/-- The part of the arithmetic that does not know the width: for sOf n ≥ 1 the pad of length
2^(8·(⌊n/2^(sOf n)⌋ + 1)) suffices for all evaluations, for every width
k ≤ sOf n and every bound Δ ≤ 2^(betaOf (sOf n)) on the number of clauses in which a variable
occurs, and for the computation of the schedule. -/
def StA : Prop := ∀ k n F Δ : ℕ, 1 ≤ sOf n → 2 ^ (8 * (n / 2 ^ sOf n + 1)) ≤ F → k ≤ sOf n → Δ ≤ 2 ^ betaOf (sOf n) →
  MarkFits k F (schedL (depthOf (sOf n)), List.replicate (Kseq (depthOf (sOf n))) ()) n (betaOf (sOf n)) (2 ^ betaOf (sOf n)) (layersOf (sOf n)) Δ (Δ * n) ∧
  schedLen (depthOf (sOf n)) ≤ F

/-- The part of the arithmetic that knows the width k: for sOf n ≥ s0K k, the width is at most sOf
n, a variable occurs in at most 2^(betaOf (sOf n)) clauses of a leaf of the
sparsification tree (with 2 to spare), and the pad of length 2^(8·(⌊n/2^(sOf n)⌋ + 1)) suffices for
the rounds of the walk through the tree and for its stack. -/
def StAW : Prop := ∀ k n F : ℕ, 1 ≤ k → s0K k ≤ sOf n → 2 ^ (8 * (n / 2 ^ sOf n + 1)) ≤ F →
  k ≤ sOf n ∧ leafC (tauOf (sOf n)) k + 2 ≤ 2 ^ betaOf (sOf n) ∧
  2 * (∑ j ∈ Finset.range (k * n / tauOf (sOf n) + 1), (bsum (tauOf (sOf n)) k * n).choose j) ≤ F + 1 ∧
  stackLen k (tauOf (sOf n)) n (inLen k n) ≤ F

/-! ### The polynomial-time certificates (the files Cert*.lean) -/

/-- The lengths of a network are given in unary and its two functions are polynomial-time. -/
structure FKeeps {C : Type} [Enc C] (F : FNet C) : Prop where
  n : Unary fun p : C × ℕ => F.n p.1 p.2
  cap : Unary fun p : C × ℕ × ℕ => F.cap p.1 p.2.1 p.2.2
  W : PolyT F.W
  f : PolyT F.f

def StCertRebal : Prop := ∀ (C : Type) [Enc C] (F : FNet C), FKeeps F → ∀ (α : Type) [Enc α] (pad : α → U) (K g : α → ℕ) (c : α → C),
  PolyT pad → Unary K → Unary g → PolyT c → PolyT fun t => rebalF (pad t) (K t) (g t) F (c t)

/-- `StCertRebal` for `rebalG`: jointly also in the label length β, in unary. -/
def StCertRebalG : Prop := ∀ (C : Type) [Enc C] (F : FNet C), FKeeps F → ∀ (α : Type) [Enc α] (pad : α → U) (K g β : α → ℕ) (c : α → C),
  PolyT pad → Unary K → Unary g → Unary β → PolyT c → PolyT fun t => rebalG (pad t) (K t) (g t) (β t) F (c t)

def StCertSide : Prop := FKeeps sideF
def StCertMark : Prop := FKeeps markF
def StCertAdm : Prop := ∀ k : ℕ, PolyT fun q : (U × U × U) × List Fml × ℕ => adm k q.1.1.length q.1.2.1.length q.1.2.2.length q.2.1 q.2.2
def StCertExpand : Prop := PolyT fun p : U × Lvl × PInst => expand p.1 p.2.1 p.2.2
def StCertBrute : Prop := PolyT fun p : U × PInst => bruteF p.1 256 p.2
def StCertDescend : Prop := PolyT fun p : U × List Lvl × PInst => descend p.1 p.2.1 p.2.2
def StCertValF : Prop := ∀ (C : Type) [Enc C] (F : FNet C), FKeeps F → ∀ (α : Type) [Enc α] (pad : α → U) (S : α → List Lvl × U) (c : α → C),
  PolyT pad → PolyT S → PolyT c → PolyT fun t => valF (pad t) (S t) F (c t)
def StCertWalk : Prop := ∀ (k : ℕ) (α : Type) [Enc α] (pad : α → U) (τ : α → ℕ) (test : α → PFml → Bool) (r : α → PFml),
  PolyT pad → PolyT τ → (PolyT fun p : α × PFml => test p.1 p.2) → PolyT r → PolyT fun t => walkF k (pad t) (τ t) (test t) (r t)
def StCertA : Prop := PolyT A

end PaddedDescent.F
