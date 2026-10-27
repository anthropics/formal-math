/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppVariablesStatement
public import ClauseBound.ParityChecks.NetDefs
public import ClauseBound.ParityChecks.Params
public import ClauseBound.Alg.TopNet
public import VariableBound.Params.Defs
public import VariableBound.Search.Defs

/-! # Appendix D, Step 3: a network with two kinds of marks. Definitions and interface statements

## How to read it

* D = (ψ, 𝓛) is the data of a network: the formula ψ (a list of m clauses) and the list 𝓛 of checks,
  each check a list of numbers of clauses. The text numbers checks 1, …, r and nodes 1, …, g; Lean
  0, …, r − 1 and 0, …, g − 1.
* An object is a triple (κ, e, j): (0, e, 0) is the clause number e, (1, e, j) is the incidence (E,
  j) of the clause number e and the check number j. Objects are named by their position o in the
  list `objs D`.
* The variable v is held by the node v / ⌈n/g⌉ (`qv g n` = ⌈n/g⌉), the home of check j is j % g (in
  Lean's numbering from 0, which shifts the text's homes by one; nothing depends on which home a
  check has).
* A setting z_a is a word: ⌈n/g⌉ value bits, then one mark bit for each object that touches a, in
  the order of `tch`.
* A profile is a number y; its digits in base I + m + 1 are the numbers μ: `mu g D y a a κ` is
  μ_(a,κ), and `mu g D y a b κ` is μ_(a,b,κ) for a ≠ b.
* The set S_a of a network in Lean is always the set of all words of one length (`PNet.Presents`).
  «S_a restricted to the settings in which exactly …» is therefore written into W_a: W_a is 0 at the
  other settings. The same holds for
  value bits of variables with numbers ≥ n at the last nodes: they must be 0.
* The flag fl says which sum: false for X (|Π₀| = n̄ + 1, no sign), true for F (|Π₀| ≤ n̄, sign
  (−1)^|Π₀|).
* A set P of (positions of) objects stands for a tuple (Π₀, …, Π_r). -/

@[expose] public section

namespace VariableBound.Net

open Groundwork Groundwork.Prog Groundwork.Prog.Count PaddedDescent.F ClauseBound.Alg
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)
open ClauseBound.ParityChecks (Vof LD)

/-! ### Objects, homes, touches, owners, tests, settings -/

/-- The formula and the list of checks. -/
abbrev Dat := Fml × List (List ℕ)

/-- The objects: the clauses (kind 0), then the incidences (E, j) with E ∈ Λ_j (kind 1). -/
def objs (D : Dat) : List (ℕ × ℕ × ℕ) :=
  ((List.range D.1.length).map fun e => (0, e, 0)) ++ (List.range D.2.length).flatMap fun j => (D.2.getD j []).map fun e => (1, e, j)

/-- The object at the place o; for o beyond the list, the triple (0, m, 0), which is no object. -/
def obAt (D : Dat) (o : ℕ) : ℕ × ℕ × ℕ := (objs D).getD o (0, D.1.length, 0)

/-- The clause of the object o. -/
def clOf (D : Dat) (o : ℕ) : Cl := D.1.getD (obAt D o).2.1 []

/-- The home h(j) ≡ j (mod g) of check j. -/
def home (g j : ℕ) : ℕ := j % g

/-- The object o touches the node a: a holds a variable of its clause, or o is an incidence (E, j)
and a = h(j). -/
def tchB (g n : ℕ) (D : Dat) (a o : ℕ) : Bool :=
  ((clOf D o).any fun l => l.1 / qv g n == a) || ((obAt D o).1 == 1 && home g (obAt D o).2.2 == a)

/-- The objects that touch a, in order. -/
def tch (g n : ℕ) (D : Dat) (a : ℕ) : List ℕ := (List.range (objs D).length).filter (tchB g n D a)

/-- {a, b} with a < b is a test of o: a and b are neighbours in the chain a₁ < … < a_t of the nodes
that o touches. -/
def linkB (g n : ℕ) (D : Dat) (o a b : ℕ) : Bool :=
  decide (a < b) && tchB g n D a o && tchB g n D b o &&
    (List.range g).all fun c => !(decide (a < c) && decide (c < b) && tchB g n D c o)

/-- a is the owner of o: the least node that o touches. -/
def ownB (g n : ℕ) (D : Dat) (o a : ℕ) : Bool :=
  tchB g n D a o && (List.range g).all fun c => !(decide (c < a) && tchB g n D c o)

/-- The objects of kind κ with the test {a, b}, in order; their number is t_(a,b,κ). -/
def tst (g n : ℕ) (D : Dat) (a b κ : ℕ) : List ℕ :=
  (List.range (objs D).length).filter fun o => (obAt D o).1 == κ && linkB g n D o (min a b) (max a b)

/-- The mark that the setting z of node a gives to the object o. -/
def mark (g n : ℕ) (D : Dat) (a : ℕ) (z : List Bool) (o : ℕ) : Bool := z.getD (qv g n + (tch g n D a).idxOf o) false

/-- The string of the marks of the t_(a,b,κ) objects, in a fixed order. -/
def str (g n : ℕ) (D : Dat) (a b κ : ℕ) (z : List Bool) : List Bool := (tst g n D a b κ).map (mark g n D a z)

/-! ### «The total»: ranks of subsets -/

/-- The position of a string in the list, in lexicographic order with 0 before 1, of all strings of
its length with as many ones. -/
def rank : List Bool → ℕ
  | [] => 0
  | b :: x => (bif b then x.length.choose (x.count true + 1) else 0) + rank x

/-- ⌈log C(t, μ)⌉. -/
def cw (t μ : ℕ) : ℕ := Nat.clog 2 (t.choose μ)

/-! ### Profiles and the network of one profile -/

/-- The number that the profile y prescribes: μ_(a,κ) for b = a, μ_(a,b,κ) = μ_(b,a,κ) for b ≠ a. -/
def mu (g : ℕ) (D : Dat) (y a b κ : ℕ) : ℕ := digit (objs D).length y ((min a b * g + max a b) * 2 + κ)

/-- c_(a,b) = Σ_κ ⌈log C(t_(a,b,κ), μ_(a,b,κ))⌉. -/
def capD (g n : ℕ) (D : Dat) (y a b : ℕ) : ℕ := ((List.range 2).map fun κ => cw (tst g n D a b κ).length (mu g D y a b κ)).sum

/-- The label that a shows to b: for each kind the position of the string of marks, in ⌈log C(t, μ)⌉
bits. -/
def labD (g n : ℕ) (D : Dat) (y a b : ℕ) (z : List Bool) : List Bool :=
  (List.range 2).flatMap fun κ => toWord (cw (tst g n D a b κ).length (mu g D y a b κ)) (rank (str g n D a b κ z))

/-- q_j at the node a: the number of marked incidences of check j. -/
def qj (g n : ℕ) (D : Dat) (a : ℕ) (z : List Bool) (j : ℕ) : ℕ :=
  ((tch g n D a).filter fun o => (obAt D o).1 == 1 && (obAt D o).2.2 == j && mark g n D a z o).length

/-- The setting z of the node a belongs to the network of the profile y and no marked object has a
true literal at a. -/
def okD (g n : ℕ) (D : Dat) (y a : ℕ) (z : List Bool) : Bool :=
  ((List.range (qv g n)).all fun r => decide (a * qv g n + r < n) || !(z.getD r false)) &&
    ((tch g n D a).all fun o => !(mark g n D a z o) ||
      (clOf D o).all fun l => !(l.1 / qv g n == a) || (z.getD (l.1 % qv g n) false != l.2)) &&
    ((List.range 2).all fun κ =>
      ((tch g n D a).filter fun o => (obAt D o).1 == κ && ownB g n D o a && mark g n D a z o).length == mu g D y a a κ) &&
    ((List.range g).all fun b => b == a || (List.range 2).all fun κ => (str g n D a b κ z).count true == mu g D y a b κ)

/-- W_a(z_a): 0 if a marked object has a true literal at a (or z_a is not a setting of the profile);
otherwise ∏_(j : h(j) = a) σ_(q_j), times, for F only, (−1)^q, where q is the number of marked
clauses owned by a. -/
def WD (g n : ℕ) (D : Dat) (y : ℕ) (fl : Bool) (a : ℕ) (z : List Bool) : ℤ :=
  if okD g n D y a z then
    (((List.range D.2.length).filter fun j => home g j == a).map fun j => ParityChecks.sig (qj g n D a z j)).prod *
      (bif fl then (-1) ^ ((tch g n D a).filter fun o => (obAt D o).1 == 0 && ownB g n D o a && mark g n D a z o).length else 1)
  else 0

/-- ((g, n in unary), ((ψ, 𝓛), (profile, flag))). -/
abbrev DCtx := (U × U) × (Dat × (ℕ × Bool))

/-- The network of one profile, as functions. -/
def netD : FNet DCtx where
  n c a := qv c.1.1.length c.1.2.length + (tch c.1.1.length c.1.2.length c.2.1 a).length
  cap c a b := capD c.1.1.length c.1.2.length c.2.1 c.2.2.1 a b
  W x := WD x.1.1.1.length x.1.1.2.length x.1.2.1 x.1.2.2.1 x.1.2.2.2 x.2.1 x.2.2
  f x := if labD x.1.1.1.length x.1.1.2.length x.1.2.1 x.1.2.2.1 x.2.1.1 x.2.1.2 x.2.2.1 == x.2.2.2 then 1 else 0

/-- The network that netD presents. Ψ_(a,b) factors through c_(a,b) bits: f_(a,b)(z, θ) = [the label
of z is θ]. -/
def netDN (g : ℕ) (c : DCtx) : Network (Fin g) (List Bool) (List Bool) where
  S a := words (netD.n c a.val)
  W a z := netD.W (c, (a.val, z))
  Θ a b := words (netD.cap c a.val b.val)
  f a b z θ := netD.f (c, ((a.val, b.val), (z, θ)))
  c a b := netD.cap c a.val b.val

/-- n in unary. -/
def rep (n : ℕ) : U := List.replicate n ()

/-- The context of the network of the profile y. -/
def ctx (g n : ℕ) (D : Dat) (y : ℕ) (fl : Bool) : DCtx := ((rep g, rep n), (D, (y, fl)))

/-- Σ_a μ_(a,κ). -/
def tot (g : ℕ) (D : Dat) (y κ : ℕ) : ℕ := ((List.range g).map fun a => mu g D y a a κ).sum

/-- μ_κ = Σ_({a,b}) μ_(a,b,κ). -/
def totP (g : ℕ) (D : Dat) (y κ : ℕ) : ℕ := ((List.range g).map fun b => ((List.range b).map fun a => mu g D y a b κ).sum).sum

/-- The profile y is admissible: μ_(a,b,κ) ≤ t_(a,b,κ), Σ_({a,b}) μ_(a,b,κ) ≤ (k − 1 + κ)·Σ_a
μ_(a,κ), Σ_a μ_(a,0) = n̄ + 1 (for F: ≤ n̄) and Σ_a μ_(a,1) ≤ M. The digits of y at the places that
no μ reads, below 2g², are 0
(the sums run over y < `nPr`, so no higher digit occurs), so that every profile is one number. -/
def admD (k g n nb M : ℕ) (D : Dat) (fl : Bool) (y : ℕ) : Bool :=
  (bif fl then decide (tot g D y 0 ≤ nb) else tot g D y 0 == nb + 1) && decide (tot g D y 1 ≤ M) &&
    (List.range 2).all fun κ =>
      decide (totP g D y κ ≤ (k - 1 + κ) * tot g D y κ) &&
      (List.range g).all fun a => (List.range g).all fun b =>
        if b < a then digit (objs D).length y ((a * g + b) * 2 + κ) == 0
        else b == a || decide (mu g D y a b κ ≤ (tst g n D a b κ).length)

/-- The number of numbers y that are tried as profiles: (I + m + 1)^(2g²). -/
def nPr (g : ℕ) (D : Dat) : ℕ := nProf g (objs D).length 2

/-! ### Sets of marked objects -/

/-- ψ has clauses of 1 to k literals on variables below n; the checks are lists without repetition
of numbers of clauses. -/
def WfD (k n : ℕ) (D : Dat) : Prop := WfL k n [D.1] ∧ ∀ L ∈ D.2, L.Nodup ∧ ∀ e ∈ L, e < D.1.length

/-- The objects whose clause σ violates. -/
def vset (σ : ℕ → Bool) (D : Dat) : Finset ℕ := (Finset.range (objs D).length).filter fun o => vio σ (clOf D o) = true

/-- The members of P of kind κ. -/
def kP (D : Dat) (P : Finset ℕ) (κ : ℕ) : Finset ℕ := P.filter fun o => (obAt D o).1 = κ

/-- The members of P that are incidences of check j. -/
def chP (D : Dat) (P : Finset ℕ) (j : ℕ) : Finset ℕ := P.filter fun o => (obAt D o).1 = 1 ∧ (obAt D o).2.2 = j

/-- The number of members of P of kind κ that the node a owns. -/
def oc (g n : ℕ) (D : Dat) (P : Finset ℕ) (a κ : ℕ) : ℕ := (P.filter fun o => (obAt D o).1 = κ ∧ ownB g n D o a = true).card

/-- The number of members of P among the objects of kind κ with the test {a, b}. -/
def pw (g n : ℕ) (D : Dat) (P : Finset ℕ) (a b κ : ℕ) : ℕ := (P.filter fun o => o ∈ tst g n D a b κ).card

/-- The value of the term of P in display (65): ∏_j σ_(|Π_j|), for F times (−1)^|Π₀|. -/
def wt (D : Dat) (fl : Bool) (P : Finset ℕ) : ℤ :=
  (∏ j ∈ Finset.range D.2.length, ParityChecks.sig (chP D P j).card) * (bif fl then (-1) ^ (kP D P 0).card else 1)

/-- P belongs to the profile y. -/
def Match (g n : ℕ) (D : Dat) (y : ℕ) (P : Finset ℕ) : Prop :=
  ∀ κ < 2, ∀ a < g, oc g n D P a κ = mu g D y a a κ ∧ ∀ b < g, b ≠ a → pw g n D P a b κ = mu g D y a b κ

/-- |Π₀| = n̄ + 1 (for F: ≤ n̄) and |Π₁| + … + |Π_r| ≤ M. -/
def Lim (nb M : ℕ) (D : Dat) (fl : Bool) (P : Finset ℕ) : Prop :=
  (if fl = true then (kP D P 0).card ≤ nb else (kP D P 0).card = nb + 1) ∧ (kP D P 1).card ≤ M

/-! ### The right sides of display (65) -/

/-- The list 𝓛 of checks as sets of clauses of ψ. -/
def chks (D : Dat) : List (Finset (Fin D.1.length)) := chksD D.1.length D.2

/-- The right side of display (65): of its first line for fl = false, of its second line for fl =
true. -/
def rhsXF {X E : Type} [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) (M : ℕ) (fl : Bool) : ℤ :=
  bif fl then ∑ ξ, ∑ S₀ ∈ (V ξ).powerset with S₀.card ≤ nb, (-1) ^ S₀.card * ∑ S ∈ AppVariables.tup V L M ξ, ∏ j, ParityChecks.sig (S j).card
  else ∑ ξ, ∑ _S₀ ∈ (V ξ).powerset with _S₀.card = nb + 1, ∑ S ∈ AppVariables.tup V L M ξ, ∏ j, ParityChecks.sig (S j).card

/-- The right side of display (65) for the formula ψ on n variables and the list 𝓛. -/
def rhsD (n nb M : ℕ) (D : Dat) (fl : Bool) : ℤ := rhsXF (Vof (n := n) D.1) nb (chks D) M fl

/-- load(E) for the clause number e: the number of checks of the list that contain e. -/
def colD (D : Dat) (e : ℕ) : ℕ := (D.2.filter fun L => L.contains e).length

/-- For well-formed data (WfD), the list of sets has the numbers of the list of lists: r, |Λ_j| and
load(E). -/
def StChks : Prop := ∀ (k n : ℕ) (D : Dat), WfD k n D →
  (chks D).length = D.2.length ∧ (∀ j, ((chks D).getD j ∅).card = (D.2.getD j []).length) ∧ ∀ e : Fin D.1.length, AppVariables.load (chks D) e = colD D e.val

/-! ### Rank.lean: the labels -/

/-- The labels have c_(a,b) bits; two settings of the profile (the strings have μ ones) have the
same label iff they give the same marks to every object with the test {a, b}. -/
structure StLab : Prop where
  len : ∀ (g n : ℕ) (D : Dat) (y a b : ℕ) (z : List Bool), (labD g n D y a b z).length = capD g n D y a b
  inj : ∀ (g n : ℕ) (D : Dat) (y a b : ℕ) (z z' : List Bool),
    (∀ κ < 2, (str g n D a b κ z).count true = mu g D y a b κ) → (∀ κ < 2, (str g n D b a κ z').count true = mu g D y a b κ) →
    (labD g n D y a b z = labD g n D y b a z' ↔ ∀ κ < 2, str g n D a b κ z = str g n D b a κ z')

/-! ### Val.lean: the network of one profile -/

/-- The plain functions `netD` present the network `netDN`, in every context. -/
def StPresents : Prop := ∀ c : DCtx, netD.toP.Presents c (netDN c.1.1.length c) 0 0

/-- Step 3: «the nonzero terms are the tuples (ξ, Π₀, …, Π_r), each once, with the values in (65)»,
for the network of one profile y, admissible or not: for g > 0 and well-formed data (WfD), its value
is the sum over ξ and the
sets P of objects with violated clauses that belong to the profile. -/
def StVal : Prop := ∀ (k g n : ℕ) (D : Dat) (y : ℕ) (fl : Bool), 0 < g → WfD k n D →
  (netDN g (ctx g n D y fl)).value =
    ∑ σ : Fin n → Bool, ∑ P ∈ (vset (Mark.ext σ) D).powerset, by classical exact if Match g n D y P then wt D fl P else 0

/-! ### Prof.lean: profiles -/

/-- Step 3, «Profiles»: «every nonzero term belongs to exactly one profile», and that profile is
admissible iff |Π₀| = n̄ + 1 (for F: ≤ n̄) and Σ_j |Π_j| ≤ M. In Lean: for g > 0, well-formed data
(WfD) and a set P of places of
objects, the number of admissible profiles y < `nPr` to which P belongs is 1 if P is within these
limits, and 0 otherwise. -/
def StProf : Prop := ∀ (k g n nb M : ℕ) (D : Dat) (fl : Bool) (P : Finset ℕ), 0 < g → WfD k n D → P ⊆ Finset.range (objs D).length →
  (∑ y ∈ Finset.range (nPr g D), by classical exact if admD k g n nb M D fl y = true ∧ Match g n D y P then (1 : ℤ) else 0) =
    (by classical exact if Lim nb M D fl P then 1 else 0 : ℤ)

/-- Step 3, «Profiles»: the numbers tried as profiles (`nPr`), and so the admissible profiles, are
at most (I + m + 1)^(2(g² + g)), with I ≤ r·s incidences if every check has at most s clauses. -/
def StNPr : Prop := ∀ (g : ℕ) (D : Dat) (s : ℕ), (∀ L ∈ D.2, L.length ≤ s) →
  (objs D).length ≤ D.2.length * s + D.1.length ∧ nPr g D ≤ ((objs D).length + 1) ^ (2 * (g ^ 2 + g))

/-! ### Tuples.lean, Total.lean: sets of objects and tuples (Π₀, …, Π_r) -/

/-- For well-formed data (WfD): the sum over ξ and the sets P of objects with violated clauses,
within the limits, is the right side of display (65). -/
def StTuples : Prop := ∀ (k n nb M : ℕ) (D : Dat) (fl : Bool), WfD k n D →
  (∑ σ : Fin n → Bool, ∑ P ∈ (vset (Mark.ext σ) D).powerset, by classical exact if Lim nb M D fl P then wt D fl P else 0) = rhsD n nb M D fl

/-- Step 3, «Profiles»: «each right side of (65) is the sum of the values of the networks of the
admissible profiles», for g > 0 and well-formed data (WfD). -/
def StTotal : Prop := ∀ (k g n nb M : ℕ) (D : Dat) (fl : Bool), 0 < g → WfD k n D →
  ∑ y ∈ Finset.range (nPr g D), (if admD k g n nb M D fl y = true then (netDN g (ctx g n D y fl)).value else 0) = rhsD n nb M D fl

/-! ### SizeU.lean, SizeP.lean, SizeB.lean, SizeSmall.lean, Fit.lean: «The total» and «The parameters» -/

/-- The setting of Step 3 for m > n̄: the data are well formed (WfD), every variable occurs in at
most Δ ≥ 2 clauses, m ≤ Δn, n̄ is the number of the text, and the list has r ≤ M checks, M ≥ 1, with |Λ_j|
≤ s̄ = 16m/n̄. -/
structure Setting (k n Δ nb M : ℕ) (D : Dat) : Prop where
  wf : WfD k n D
  two : 2 ≤ Δ
  occ_le : ∀ v, (occ D.1 v).length ≤ Δ
  m_le : D.1.length ≤ Δ * n
  isNb : AppVariables.IsNb n Δ nb
  lt_m : nb < D.1.length
  r_le : D.2.length ≤ M
  one_le : 1 ≤ M
  row : ∀ L ∈ D.2, nb * L.length ≤ 16 * D.1.length

/-- Display (68), before display (61) is used: for g > 0, in the setting of Step 3 for m > n̄
(`Setting`), the network of an admissible profile has U ≤ 6(k−1)(n + log(2Δ)) + 2kM·log(96Δ·log(2Δ)) +
2g². -/
def StU : Prop := ∀ (k g n Δ nb M : ℕ) (D : Dat) (fl : Bool) (y : ℕ), 0 < g → Setting k n Δ nb M D → admD k g n nb M D fl y = true →
  ((netDN g (ctx g n D y fl)).U : ℝ) ≤
    6 * (k - 1 : ℕ) * (n + lg (2 * Δ)) + 2 * k * M * lg (96 * Δ * lg (2 * Δ)) + 2 * g ^ 2

/-- Display (68) as printed, with M ≤ 14n from display (61): for g > 0, in the setting of Step 3 for
m > n̄ (`Setting`), the network of an admissible profile has U ≤ 6k(n + log(2Δ)) +
28kn·log(96Δ·log(2Δ)) + 2g². -/
def StUPrinted : Prop := ∀ (k g n Δ nb M : ℕ) (D : Dat) (fl : Bool) (y : ℕ), 0 < g → Setting k n Δ nb M D → M ≤ 14 * n → admD k g n nb M D fl y = true →
  ((netDN g (ctx g n D y fl)).U : ℝ) ≤ 6 * k * (n + lg (2 * Δ)) + 28 * k * n * lg (96 * Δ * lg (2 * Δ)) + 2 * g ^ 2

/-- Display (68) with the logarithms rounded up, on g = 3K⁸ nodes: a number that can be computed and
does not depend on the formula. -/
def UbD (k K n Δ : ℕ) : ℕ := 6 * k * (n + LD Δ) + 28 * k * n * Nat.clog 2 (96 * Δ * LD Δ) + 2 * (3 * K ^ 8) ^ 2

/-- P₀ = ⌈n/g⌉(1 + Δ(t̄ + 3)) + ⌈r̄/g⌉·s̄. -/
def P0 (g n Δ tb rb : ℕ) (sb : ℚ) : ℚ := (qv g n : ℚ) * (1 + Δ * (tb + 3)) + (qv g rb : ℚ) * sb

/-- P = ⌈2P₀⌉. -/
def PD (g n Δ tb rb : ℕ) (sb : ℚ) : ℕ := ⌈2 * P0 g n Δ tb rb sb⌉₊

/-- B = (k + 1)M + 1. -/
def BD (k M : ℕ) : ℕ := (k + 1) * M + 1

/-- Step 3, «The parameters»: for a list with display (67), the network of an admissible profile
satisfies conditions (i) and (ii) of the definition of a network with P = ⌈2P₀⌉ and B = (k + 1)M + 1.
Needs: g > 0, s̄ ≥ 0, well-formed data (WfD), every variable in at most Δ clauses, r ≤ r̄, |Λ_j| ≤
s̄, load(E) ≤ t̄ + 2. -/
def StSized : Prop := ∀ (k g n Δ nb M tb rb : ℕ) (sb : ℚ) (D : Dat) (fl : Bool) (y : ℕ), 0 < g → 0 ≤ sb → WfD k n D → (∀ v, (occ D.1 v).length ≤ Δ) →
  D.2.length ≤ rb → (∀ L ∈ D.2, (L.length : ℚ) ≤ sb) → (∀ e < D.1.length, colD D e ≤ tb + 2) → admD k g n nb M D fl y = true →
  (netDN g (ctx g n D y fl)).Sized (PD g n Δ tb rb sb) (BD k M)

/-- Display (69): gP ≤ 2(n + g)(1 + Δ(t̄ + 3)) + 2(10n + g)·s̄ + g, for g > 0, s̄ ≥ 0 and r̄ ≤ 10n,
with P = ⌈2P₀⌉. -/
def StP : Prop := ∀ (g n Δ tb rb : ℕ) (sb : ℚ), 0 < g → 0 ≤ sb → rb ≤ 10 * n →
  ((g * PD g n Δ tb rb sb : ℕ) : ℚ) ≤ 2 * (n + g) * (1 + Δ * (tb + 3)) + 2 * (10 * n + g) * sb + g

/-- Bounds for t̄ and s̄ that do not depend on the formula: t̄ ≤ log m + 33·log(2Δ) + 1 with m ≤ Δn,
and s̄ < 32Δ·log(2Δ). -/
def tbMax (n Δ : ℕ) : ℕ := Nat.clog 2 (Δ * n) + 33 * LD Δ + 1
/-- The bound for s̄: 32Δ·⌈log(2Δ)⌉. -/
def sbMax (Δ : ℕ) : ℕ := 32 * Δ * LD Δ

/-- P = ⌈2P₀⌉ on g = 3K⁸ nodes with r̄ = 10n, t̄ = `tbMax` and s̄ = `sbMax`: it does not depend on
the formula. -/
def PbD (K n Δ : ℕ) : ℕ := PD (3 * K ^ 8) n Δ (tbMax n Δ) (10 * n) (sbMax Δ)
/-- B = (k + 1)M + 1 with M = 14n. -/
def BbD (k n : ℕ) : ℕ := BD k (14 * n)

/-- What one evaluation asks: ψ and the checks are well formed (WfD), every variable lies in at most
Δ ≥ 2 clauses, m ≤ Δn, n̄ is the number of the text (AppVariables.IsNb), M ≤ 14n, the list has r ≤
10n checks, and load(E) ≤ `tbMax` + 2 for
every clause. Further, either m > n̄, and then r ≤ M, M ≥ 1 and |Λ_j| ≤ 16m/n̄ for every j (display (67)
with the bounds of display (61)), or m ≤ n̄ and the list is empty. -/
structure Fit (k n Δ nb M : ℕ) (D : Dat) : Prop where
  wf : WfD k n D
  two : 2 ≤ Δ
  occ_le : ∀ v, (occ D.1 v).length ≤ Δ
  m_le : D.1.length ≤ Δ * n
  isNb : AppVariables.IsNb n Δ nb
  M_le : M ≤ 14 * n
  r_le : D.2.length ≤ 10 * n
  col : ∀ e < D.1.length, colD D e ≤ tbMax n Δ + 2
  big : nb < D.1.length → D.2.length ≤ M ∧ 1 ≤ M ∧ ∀ L ∈ D.2, nb * L.length ≤ 16 * D.1.length
  small : D.1.length ≤ nb → D.2 = []

/-- t̄ ≤ log m + 33·log(2Δ) + 1 gives t̄ ≤ `tbMax`, for 1 ≤ m ≤ Δn. -/
def StTbMax : Prop := ∀ n Δ m tb : ℕ, 1 ≤ m → m ≤ Δ * n → (tb : ℝ) ≤ lg m + 33 * lg (2 * Δ) + 1 → tb ≤ tbMax n Δ

/-- For a formula ψ with clauses of 1 to k literals on variables below n, every variable in at most
Δ ≥ 2 clauses, m ≤ Δn, n̄ the number of the text and M ≤ 14n: if m > n̄, a list with display (67)
for r̄ ≤ 10n, r̄ ≤ M,
1 ≤ M and t̄ ≤ `tbMax` is fit for an evaluation; if m ≤ n̄, the empty list is. -/
def StFit : Prop := ∀ (k n Δ nb rb tb M : ℕ) (ψ : Fml) (L : List (List ℕ)), WfL k n [ψ] → 2 ≤ Δ → (∀ v, (occ ψ v).length ≤ Δ) → ψ.length ≤ Δ * n → AppVariables.IsNb n Δ nb → M ≤ 14 * n →
  (nb < ψ.length → StructD ψ.length nb rb tb L → rb ≤ 10 * n → rb ≤ M → 1 ≤ M → tb ≤ tbMax n Δ → Fit k n Δ nb M (ψ, L)) ∧ (ψ.length ≤ nb → Fit k n Δ nb M (ψ, []))

/-- «The total» and «The parameters» with bounds that do not depend on the formula, the case m ≤ n̄
included: on g = 3K⁸ nodes, K > 0, for a list that is fit for an evaluation (`Fit`), the network of
an admissible profile has
size `PbD`, values of at most `BbD` bits and total at most `UbD`. -/
def StSize : Prop := ∀ (k K n Δ nb M : ℕ) (D : Dat) (fl : Bool) (y : ℕ), 0 < K → Fit k n Δ nb M D → admD k (3 * K ^ 8) n nb M D fl y = true →
  (netDN (3 * K ^ 8) (ctx (3 * K ^ 8) n D y fl)).Sized (PbD K n Δ) (BbD k n) ∧ (netDN (3 * K ^ 8) (ctx (3 * K ^ 8) n D y fl)).U ≤ UbD k K n Δ

/-- A bound for the number I + m of objects that does not depend on the formula, and the number of
profiles that goes with it. -/
def objMax (n Δ : ℕ) : ℕ := 10 * n * sbMax Δ + Δ * n
/-- The number of numbers tried as profiles on 3K⁸ nodes, if there were `objMax` objects. -/
def nPrMax (K n Δ : ℕ) : ℕ := nProf (3 * K ^ 8) (objMax n Δ) 2

/-- For a list that is fit for an evaluation (`Fit`), the number of numbers tried as profiles on 3K⁸
nodes is at most `nPrMax`. -/
def StNPrMax : Prop := ∀ (k K n Δ nb M : ℕ) (D : Dat), Fit k n Δ nb M D → nPr (3 * K ^ 8) D ≤ nPrMax K n Δ

/-- Bounds for the arithmetic of Step 4, on g = 3K⁸ nodes, for n ≥ 1 and Δ ≥ 2: `UbD` ≤
140·k·n·⌈log(2Δ)⌉ + 2g², and g·`PbD` is at most the right side of display (69) with t̄ = `tbMax` and
s̄ = `sbMax`. -/
def StBounds : Prop := ∀ (k K n Δ : ℕ), 1 ≤ n → 2 ≤ Δ →
  UbD k K n Δ ≤ 140 * k * n * LD Δ + 2 * (3 * K ^ 8) ^ 2 ∧
  3 * K ^ 8 * PbD K n Δ ≤ 2 * (n + 3 * K ^ 8) * (1 + Δ * (tbMax n Δ + 3)) + 2 * (10 * n + 3 * K ^ 8) * sbMax Δ + 3 * K ^ 8

/-- The case m ≤ n̄ as printed: for g > 0, the empty list of checks, ψ well formed (WfD) with at
most n̄ clauses, every variable in at most Δ of them, and an admissible profile: U ≤ 2(k − 1)n̄ (the
text adds ≤ 2kn, which needs n̄ ≤ n and is not part of this statement), and
P = 2⌈n/g⌉(1 + Δ) and B = 1 will do. -/
def StSmall : Prop := ∀ (k g n Δ nb M : ℕ) (ψ : Fml) (fl : Bool) (y : ℕ), 0 < g → WfD k n (ψ, []) → (∀ v, (occ ψ v).length ≤ Δ) → ψ.length ≤ nb →
  admD k g n nb M (ψ, []) fl y = true →
  (netDN g (ctx g n (ψ, []) y fl)).Sized (2 * (qv g n * (1 + Δ))) 1 ∧ (netDN g (ctx g n (ψ, []) y fl)).U ≤ 2 * (k - 1) * nb

/-! ### Ev.lean: the two sums as programs -/

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-- One evaluation: the sum, over the admissible profiles, of the values of their networks, each
computed by the clique solver as an exact integer. -/
def evD (k : ℕ) (pad : U) (i : Idx) (n Δ nb M : ℕ) (fl : Bool) (D : Dat) : ℤ :=
  sumF (nPr (3 * S.K i ^ 8) D) pad fun y =>
    bif admD k (3 * S.K i ^ 8) n nb M D fl y then valS S pad i (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) netD (ctx (3 * S.K i ^ 8) n D y fl) else 0

/-- X(𝓛): the sum reduced modulo 2^β. -/
def evX (k : ℕ) (pad : U) (i : Idx) (n Δ nb M β : ℕ) (D : Dat) : ℤ := evD S k pad i n Δ nb M false D % 2 ^ β

/-- F(𝓛): the sum reduced modulo 2^(n+1). -/
def evF (k : ℕ) (pad : U) (i : Idx) (n Δ nb M : ℕ) (D : Dat) : ℤ := evD S k pad i n Δ nb M true D % 2 ^ (n + 1)

end

/-- One evaluation is the right side of display (65), if the solver is right at the indices with
`ok`, ok i, K ≥ 2, the list is fit for an evaluation (`Fit`), and the pad fits: it is at least as
long as the number `nPr` of
numbers tried as profiles and as 2^`needNet` for the bounds `UbD`, `PbD`, `BbD`. -/
def StEvD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (ok : Idx → Prop), S.Correct ok → ∀ (k : ℕ) (pad : U) (i : Idx) (n Δ nb M : ℕ) (fl : Bool) (D : Dat),
  ok i → 2 ≤ S.K i → Fit k n Δ nb M D → nPr (3 * S.K i ^ 8) D ≤ pad.length → 2 ^ needNet S i (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) (BbD k n) ≤ pad.length →
  evD S k pad i n Δ nb M fl D = rhsD n nb M D fl

/-- The programs compute X(𝓛), and F(𝓛) if X(𝓛) = 0: display (65) and «the residues determine the
numbers». Needs the hypotheses of `StEvD` (solver right, ok i, K ≥ 2, `Fit`, the two conditions on
the pad), M ≥ β − 1 + r and
M ≥ n + r, with β = n + ⌈log C(m, n̄ + 1)⌉ + 1. -/
def StEvXF : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (ok : Idx → Prop), S.Correct ok → ∀ (k : ℕ) (pad : U) (i : Idx) (n Δ nb M : ℕ) (D : Dat),
  ok i → 2 ≤ S.K i → Fit k n Δ nb M D → nPr (3 * S.K i ^ 8) D ≤ pad.length → 2 ^ needNet S i (UbD k (S.K i) n Δ) (PbD (S.K i) n Δ) (BbD k n) ≤ pad.length →
  AppVariables.beta n D.1.length nb - 1 + D.2.length ≤ M → n + D.2.length ≤ M →
  evX S k pad i n Δ nb M (AppVariables.beta n D.1.length nb) D = AppVariables.Xsum (Vof (n := n) D.1) nb (chks D) ∧
    (AppVariables.Xsum (Vof (n := n) D.1) nb (chks D) = 0 → evF S k pad i n Δ nb M D = AppVariables.Fsum (Vof (n := n) D.1) nb (chks D))

/-! ### Cert*.lean: polynomial time -/

/-- Step 3, «The parameters»: binomial coefficients C(t, μ) are polynomial-time for t and μ given in
unary; the position of a string among those with as many ones is polynomial-time; and ⌈log C(t, μ)⌉
is
given in unary for t given in unary and μ polynomial-time. -/
structure StCertRank : Prop where
  choose : ∀ (α : Type) [Enc α] (t μ : α → ℕ), Unary t → Unary μ → PolyT fun x => (t x).choose (μ x)
  rank : PolyT rank
  cw : ∀ (α : Type) [Enc α] (t μ : α → ℕ), Unary t → PolyT μ → Unary fun x => cw (t x) (μ x)

/-- Condition (iii) of the definition of a network: «counting marks, multiplying powers of 2 and
finding the position of a string among those with as many ones take τ = n^O(1) operations». -/
def StCertNet : Prop := FKeeps netD

/-- The test «admissible» is polynomial-time jointly in all its arguments, for g given in unary and
the other arguments polynomial-time. -/
def StCertAdm : Prop := ∀ (α : Type) [Enc α] (k g n nb M y : α → ℕ) (D : α → Dat) (fl : α → Bool),
  PolyT k → Unary g → PolyT n → PolyT nb → PolyT M → PolyT D → PolyT fl → PolyT y → PolyT fun x => admD (k x) (g x) (n x) (nb x) (M x) (D x) (fl x) (y x)

/-- One evaluation is polynomial-time jointly in all its arguments, the width k included, for a
polynomial-time solver, with k, n and Δ given in unary and the other arguments polynomial-time. -/
def StCertEvD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (α : Type) [Enc α] (k n Δ nb M : α → ℕ) (pad : α → U) (i : α → Idx) (fl : α → Bool) (D : α → Dat),
  Unary k → Unary n → Unary Δ → PolyT nb → PolyT M → PolyT pad → PolyT i → PolyT fl → PolyT D →
  PolyT fun x => evD S (k x) (pad x) (i x) (n x) (Δ x) (nb x) (M x) (fl x) (D x)

end VariableBound.Net
