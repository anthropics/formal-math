/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.NetDefs
public import ClauseBound.ParityChecks.RunDefs
public import ClauseBound.ParityChecks.Params
public import ClauseBound.Alg.TopNet

/-! # One sparse formula counted through parity checks: the program, and the interface lemmas

ψ has m clauses of 1 to k literals on n variables, and every variable occurs in at most Δ clauses.
The parameters q = (m, nb, r, i₀, β) are those of `parOf n Δ m` (r = 0 if m ≤ nb). Every sum
over marks is one evaluation `evW`: the sum, over the admissible profiles of the network of marks of
up to three layers on n + r variables (lists of clauses: ψ, the incidences of the checks as clauses
`incL`, and a suffix of ψ), of a weight times the value of the network, which a clique solver
computes. -/

@[expose] public section

namespace ClauseBound.ParityChecks

open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW

/-- n in unary. -/
def rep (n : ℕ) : U := List.replicate n ()

/-- The parameters; no checks if m ≤ nb. -/
def parQ (n Δ m : ℕ) : Par := if m ≤ nbOf n Δ then { parOf n Δ m with r := 0 } else parOf n Δ m

/-- The cap for the marks of the incidences, and for all layers. -/
def capM (q : Par) : ℕ := q.β - 1 + q.r

/-- The length of the blocks of the code of the labels, and the number of bits of a position in a
block. -/
def blkOL (Δ : ℕ) : ℕ := 2 * Δ + 16 * Δ * LD Δ + 1
def bitOL (Δ : ℕ) : ℕ := Nat.clog 2 (blkOL Δ)

/-- Bounds for the number of checks that contain a clause and for the number of clauses of a check,
in every state that is tried, if r ≤ 6n, m ≤ Δn and n < 2·nb·LD Δ. They do not depend
on the formula, so that one exponent of the pad serves all sparse formulas that come from one input. -/
def colMax (n Δ : ℕ) : ℕ := Nat.clog 2 (16 * Δ * n) + 18 * LD Δ + 2
def rowMax (n Δ : ℕ) : ℕ := Nat.clog 2 (96 * n) + 3 * Δ * LD Δ + 2

/-- A bound for the number of clauses of the three layers in which a variable occurs. -/
def occOL (n Δ : ℕ) : ℕ := max (Δ * (2 + colMax n Δ)) (rowMax n Δ)

/-- (number of variables, cap, code parameters) in unary, for the network of marks. -/
def parM (n Δ : ℕ) (q : Par) : U × U × U × U := (rep (n + q.r), rep (capM q), rep (bitOL Δ), rep (blkOL Δ))

/-- Bounds for U and P of the networks, if r ≤ 6n and the cap is at most 11n. -/
def UbOL (k K n Δ : ℕ) : ℕ := Ub (k + 1) (3 * K ^ 8) (7 * n) (11 * n) (bitOL Δ) 3
def PbOL (K n Δ : ℕ) : ℕ := Pb (3 * K ^ 8) (7 * n) (bitOL Δ) (occOL n Δ)

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx) (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (q : Par)

/-- One evaluation: `truncW (n + r) ws lo hi Ls` when the pad is long enough. -/
def evW (ws : List ℤ) (lo hi : List ℕ) (Ls : List Fml) : ℤ :=
  evalV (k + 1) pad (rep (3 * S.K i ^ 8))
    (fun c => GW c.2.1.length ws lo hi (tl c.1.1.length c.2.1 c.2.2) * valS S pad i (UbOL k (S.K i) n Δ) (PbOL (S.K i) n Δ) markF c)
    (parM n Δ q) Ls

/-- The two functions that the choice of the checks asks. -/
def orcA (ψ : Fml) (Ls : List Chk) : ℤ :=
  evW S k pad i n Δ q [1, -2] [q.nb + 1, 0] [q.nb + 1, capM q] [ψ, incL n ψ (Ls.take Ls.length) Ls.length] / 2 ^ q.r

def orcB (ψ : Fml) (Ls : List Chk) (cur : Chk) (e j : ℕ) : ℤ :=
  evW S k pad i n Δ q [1, -2, 1] [q.nb + 1, 0, j] [q.nb + 1, capM q, j] [ψ, incL n ψ (Ls ++ [cur]) Ls.length, ψ.drop e] / 2 ^ q.r

/-- The choice of the checks, with every growing list cut off by the pad. -/
def runToF (ψ : Fml) (Ls : List Chk) (e : ℕ) : Chk :=
  (List.range e).foldl (fun cur x => cap pad [] (q.decide1 (orcA S k pad i n Δ q ψ) (orcB S k pad i n Δ q ψ) Ls cur x)) (cap pad [] [])

def runF (ψ : Fml) : List Chk :=
  (List.range q.r).foldl (fun Ls _ => cap pad [] (Ls ++ [runToF S k pad i n Δ q ψ Ls q.m])) (cap pad [] [])

/-- The number of satisfying assignments of ψ among the 2ⁿ assignments. -/
def countOL (ψ : Fml) : ℕ :=
  ((evW S k pad i n Δ q [-1, -2] [0, 0] [q.nb, capM q] [ψ, incL n ψ ((runF S k pad i n Δ q ψ).take q.r) q.r] / 2 ^ q.r) % 2 ^ (n + 1)).toNat

end

/-! ### Ev.lean -/

/-- One evaluation is exact on three layers (or two) of clauses of 1 to k + 1 literals on n + r
variables in which no variable occurs too often. -/
def StEvW : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (ok : Idx → Prop), S.Correct ok → ∀ (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (q : Par)
  (ws : List ℤ) (lo hi : List ℕ) (Ls : List Fml), ok i → 2 ≤ S.K i → q.r ≤ 6 * n → capM q ≤ 11 * n → Ls.length ≤ 3 → WfL (k + 1) (n + q.r) Ls → (∀ v, (occ Ls.flatten v).length ≤ occOL n Δ) →
  Ls.flatten.length ≤ blkOL Δ * (n + q.r + 1) → (∀ l < Ls.length, hi.getD l 0 ≤ capM q) →
  nProf (3 * S.K i ^ 8) (cls Ls).length Ls.length ≤ pad.length → 2 ^ needNet S i (UbOL k (S.K i) n Δ) (PbOL (S.K i) n Δ) 0 ≤ pad.length →
  evW S k pad i n Δ q ws lo hi Ls = truncW (n + q.r) ws lo hi Ls

/-! ### Shape.lean: the layers of a state that is tried have the form that `StEvW` asks -/

def StShape : Prop := ∀ (k n Δ : ℕ) (q : Par) (ψ : Fml) (Lam : List Chk) (j e : ℕ), ψ.length = q.m → 2 ≤ q.nb → q.m ≤ Δ * n → q.r ≤ 6 * n → n < 2 * (q.nb * LD Δ) →
  WfL k n [ψ] → (∀ v, (occ ψ v).length ≤ Δ) → j ≤ q.r → (∀ L ∈ Lam, L.Nodup ∧ ∀ x ∈ L, x < q.m) → Tent q (lam q.m Lam) →
  WfL (k + 1) (n + q.r) [ψ, incL n ψ Lam j, ψ.drop e] ∧ (∀ v, (occ [ψ, incL n ψ Lam j, ψ.drop e].flatten v).length ≤ occOL n Δ) ∧
    [ψ, incL n ψ Lam j, ψ.drop e].flatten.length ≤ blkOL Δ * (n + q.r + 1)

/-! ### Count.lean -/

/-- What the count for one formula needs of the length F of the pad. -/
structure FitsOL {Idx : Type} [Enc Idx] (S : Solver Idx) (k : ℕ) (i : Idx) (n Δ : ℕ) (F : ℕ) : Prop where
  net : 2 ^ needNet S i (UbOL k (S.K i) n Δ) (PbOL (S.K i) n Δ) 0 ≤ F
  prof : nProf (3 * S.K i ^ 8) (blkOL Δ * (7 * n + 1)) 3 ≤ F
  lists : 8 * (6 * n + 1) * (Δ * n + 1) * (Nat.size (Δ * n) + 2) + 8 ≤ F

/-- The count is right. `Hyp` is what the choice of the checks needs of the parameters. -/
def StCountOL : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (ok : Idx → Prop), S.Correct ok → ∀ (k : ℕ) (pad : U) (i : Idx) (n Δ : ℕ) (ψ : Fml) (ε : ℚ),
  ok i → 2 ≤ S.K i → WfL k n [ψ] → (∀ v, (occ ψ v).length ≤ Δ) → ψ.length ≤ Δ * n → 2 ≤ nbOf n Δ → n < 2 * (nbOf n Δ * LD Δ) →
  (nbOf n Δ < ψ.length → Hyp (parOf n Δ ψ.length) (2 ^ n) ε ∧ (parOf n Δ ψ.length).r ≤ 6 * n ∧ (parOf n Δ ψ.length).β ≤ 5 * n ∧
    (parOf n Δ ψ.length).i₀ ≤ capM (parOf n Δ ψ.length)) → FitsOL S k i n Δ pad.length →
  countOL S k pad i n Δ (parQ n Δ ψ.length) ψ = nSat n ψ

/-! ### CertOL.lean -/

def StCertCountOL : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ k : ℕ,
  PolyT fun x : U × Idx × (U × U) × Fml => countOL S k x.1 x.2.1 x.2.2.1.1.length x.2.2.1.2.length (parQ x.2.2.1.1.length x.2.2.1.2.length x.2.2.2.length) x.2.2.2

end ClauseBound.ParityChecks
