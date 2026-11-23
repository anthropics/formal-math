/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cut.StartB
import Nc.Cut.Groups
import Nc.Plus.UnitBits

/-!
# The cut from general exchange identities: definitions

A law has roles, slots (one bit per block, seen by the two roles at the ends of the slot), channels (strings shared by
two roles) and an index: the product of the equalities of the two copies of the bit of every slot is a sum, over
indices and strings, of products of tables of the roles. A move has a law and a party for every role. In a move `t`
units are given at every slot (missing units are replaced by zeros), and the strings on a channel (a label and the
string of the law for every block) are cut into new units.
-/

set_option linter.unusedSectionVars false

namespace Nc.G

open Finset

/-- A law. -/
structure Law (F : Type) [CommRing F] where
  /-- roles -/
  Ro : Type
  /-- slots -/
  Sl : Type
  /-- channels -/
  Cn : Type
  /-- indices -/
  I : Type
  [fRo : Fintype Ro]
  [dRo : DecidableEq Ro]
  [fSl : Fintype Sl]
  [dSl : DecidableEq Sl]
  [fCn : Fintype Cn]
  [dCn : DecidableEq Cn]
  [fI : Fintype I]
  [dI : DecidableEq I]
  /-- one end of a slot -/
  a : Sl → Ro
  /-- the other end of a slot -/
  b : Sl → Ro
  ab : ∀ e, a e ≠ b e
  /-- one end of a channel -/
  c : Cn → Ro
  /-- the other end of a channel -/
  d : Cn → Ro
  cd : ∀ ν, c ν ≠ d ν
  /-- length of labels -/
  lam : ℕ
  /-- labels -/
  lab : I → Fin lam → Bool
  lab_inj : Function.Injective lab
  /-- lengths of strings -/
  len : I → Cn → ℕ
  /-- the tables: a role sees the bits of its slots and the strings of its channels -/
  tab : (p : Ro) → (i : I) → ({e // a e = p ∨ b e = p} → Bool) →
    ((ν : {ν // c ν = p ∨ d ν = p}) → Fin (len i ν) → Bool) → F
  /-- the identity -/
  law : ∀ X : Ro → Sl → Bool, (if ∀ e, X (a e) e = X (b e) e then (1 : F) else 0) =
    ∑ i, ∑ g : ∀ ν, Fin (len i ν) → Bool, ∏ p, tab p i (fun e => X p e) (fun ν => g ν)
  /-- indices that agree along channels are equal -/
  conn : ∀ ι : Ro → I, (∀ ν, ι (c ν) = ι (d ν)) → ∀ p q, ι p = ι q

attribute [instance] Law.fRo Law.dRo Law.fSl Law.dSl Law.fCn Law.dCn Law.fI Law.dI

namespace Law

variable {F : Type} [CommRing F] (L : Law F)

/-- The slots of a role. -/
abbrev SlAt (p : L.Ro) := {e : L.Sl // L.a e = p ∨ L.b e = p}

/-- The channels of a role. -/
abbrev CnAt (p : L.Ro) := {ν : L.Cn // L.c ν = p ∨ L.d ν = p}

/-- The role at an end of a slot. -/
def slEnd (e : L.Sl) (d : Bool) : L.Ro := if d then L.b e else L.a e

/-- The role at an end of a channel. -/
def cnEnd (ν : L.Cn) (d : Bool) : L.Ro := if d then L.d ν else L.c ν

end Law

/-- The moves: a law, and a party for every role. -/
structure Sys (F : Type) [CommRing F] (A E : ℕ) where
  /-- the law of a move -/
  kind : Fin E → Law F
  /-- the parties of a move -/
  part : ∀ x, (kind x).Ro → Fin A
  inj : ∀ x, Function.Injective (part x)

namespace Sys

variable {F : Type} [CommRing F] {A E : ℕ} (M : Sys F A E)

/-- All roles. -/
abbrev R := Σ x, (M.kind x).Ro

/-- All slots. -/
abbrev Z := Σ x, (M.kind x).Sl

/-- All channels (new bundles). -/
abbrev N := Σ x, (M.kind x).Cn

/-- The party of a role. -/
def rp (r : M.R) : Fin A := M.part r.1 r.2

/-- The role at an end of a slot. -/
def zr (z : M.Z) (d : Bool) : M.R := ⟨z.1, (M.kind z.1).slEnd z.2 d⟩

/-- The role at an end of a channel. -/
def nr (ν : M.N) (d : Bool) : M.R := ⟨ν.1, (M.kind ν.1).cnEnd ν.2 d⟩

/-- The party at an end of a slot. -/
def zp (z : M.Z) (d : Bool) : Fin A := M.rp (M.zr z d)

/-- The party at an end of a channel. -/
def np (ν : M.N) (d : Bool) : Fin A := M.rp (M.nr ν d)

end Sys

/-- Names of units. `init a b k`: unit number `k` of the string from party `a` to party `b` (only the `A` base parties
have strings at the beginning); `new ν k`: unit number `k` of the channel `ν` of a move. -/
inductive Uid (A U0 : ℕ) (N : Type) (U1 : ℕ) where
  /-- initial unit -/
  | init (a b : Fin A) (k : Fin U0)
  /-- unit made by a move -/
  | new (ν : N) (k : Fin U1)
  deriving DecidableEq, Fintype

variable {F : Type} [CommRing F] {A A' E U0 U1 : ℕ} {N : Type} [Fintype N] [DecidableEq N]

/-- The holders of a unit (`np`: the parties at the ends of the channels). There are `A` base parties and `A'` extra
parties. -/
def cparty (np : N → Bool → Fin (A + A')) : Uid A U0 N U1 → Bool → Fin (A + A')
  | .init a b _, d => Fin.castAdd A' (if d then b else a)
  | .new ν _, d => np ν d

/-- First holder of a unit. -/
def hold0 (np : N → Bool → Fin (A + A')) (id : Uid A U0 N U1) : Fin (A + A') := cparty np id false

/-- Second holder of a unit. -/
def hold1 (np : N → Bool → Fin (A + A')) (id : Uid A U0 N U1) : Fin (A + A') := cparty np id true

/-- All units, in the order of the enumeration. -/
noncomputable def allIds (A U0 : ℕ) (N : Type) [Fintype N] [DecidableEq N] (U1 : ℕ) : List (Uid A U0 N U1) :=
  (univ : Finset (Uid A U0 N U1)).toList

/-- The number of a unit in its string. -/
def unum : Uid A U0 N U1 → ℕ
  | .init _ _ k => k
  | .new _ k => k

/-- The number of units of the string to which a unit belongs. -/
def ucnt (n : Fin A → Fin A → Fin (U0 + 1)) (o : N → Fin U1) : Uid A U0 N U1 → ℕ
  | .init a b _ => n a b
  | .new ν _ => (o ν).1 + 1

/-- The units at the beginning. -/
def seen0 (n : Fin A → Fin A → Fin (U0 + 1)) : Finset (Uid A U0 N U1) :=
  univ.filter fun id => (match id with
    | .init a b k => decide (k.1 < (n a b).1)
    | .new _ _ => false) = true

section Moves

variable (M : Sys F (A + A') E) {ub : ℕ}

/-- The new units of move `x` for the outcome `o`. -/
def newUnits (x : Fin E) (o : M.N → Fin U1) : Finset (Uid A U0 M.N U1) :=
  univ.filter fun id => (match id with
    | .init _ _ _ => false
    | .new ν k => decide (ν.1 = x ∧ k ≤ o ν)) = true

/-- The bits given at a slot: the bits of the units, and zeros up to `t` units. -/
def slotBits (t : ℕ) (ids : List (Uid A U0 N U1)) (y : Uid A U0 N U1 → UW ub) : List Bool :=
  (ids.flatMap fun id => uwBits (y id)) ++ List.replicate ((t - ids.length) * ub) false

/-- The string on a channel: for every block the label and the string of the law. -/
def chString {I : Type} {lam B : ℕ} (lb : I → Fin lam → Bool) (len : I → ℕ) (i : Fin B → I)
    (g : ∀ k, Fin (len (i k)) → Bool) : List Bool :=
  (List.ofFn fun k => List.ofFn (lb (i k)) ++ List.ofFn (g k)).flatten

/-- The copies of the new units of the channel `ν` are the `J + 1` units of the string. -/
def ChOk (ν : N) (J : ℕ) (str : List Bool) (y : Uid A U0 N U1 → UW ub) : Prop :=
  ucount ub str = J + 1 ∧ ∀ k : Fin U1, y (.new ν k) = unitsOf ub str k

open Classical in
/-- The table of the role `p` of move `x`: `ids e` are the units given at the slot `e`, `t` the number of units,
`o` the outcome. -/
noncomputable def role (x : Fin E) (p : (M.kind x).Ro) (t : ℕ)
    (ids : (M.kind x).SlAt p → List (Uid A U0 M.N U1)) (o : M.N → Fin U1)
    (y : Uid A U0 M.N U1 → UW ub) : F :=
  if ∀ e, ∀ id ∈ ids e, y id ≠ none then
    ∑ i : Fin (t * ub) → (M.kind x).I,
      ∑ g : ∀ k, ∀ ν : (M.kind x).CnAt p, Fin ((M.kind x).len (i k) ν) → Bool,
        if ∀ ν : (M.kind x).CnAt p, ChOk ⟨x, ν.1⟩ (o ⟨x, ν.1⟩).1
          (chString (M.kind x).lab (fun j => (M.kind x).len j ν) i fun k => g k ν) y
        then ∏ k : Fin (t * ub), (M.kind x).tab p (i k) (fun e => (slotBits t (ids e) y).getD k false) (g k) else 0
  else 0

end Moves

section Plans

variable (M : Sys F (A + A') E)

/-- A plan: which units are given at every slot, and the number of units of every move (slots with fewer units are
filled with zeros), as functions of the numbers of units at the beginning and of the outcomes of the earlier moves. -/
structure Plan (M : Sys F (A + A') E) (U0 U1 : ℕ) where
  /-- the units given -/
  cons : (Fin A → Fin A → Fin (U0 + 1)) → (M.N → Fin U1) → M.Z → Finset (Uid A U0 M.N U1)
  /-- the number of units -/
  num : (Fin A → Fin A → Fin (U0 + 1)) → (M.N → Fin U1) → Fin E → ℕ
  /-- outcomes that are allowed -/
  good : (Fin A → Fin A → Fin (U0 + 1)) → (M.N → Fin U1) → Fin E → Prop

namespace Plan

variable {M} (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1)

/-- The units seen before move `x` (for `x = E`: in the end). -/
def seenAt (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1) (x : ℕ) : Finset (Uid A U0 M.N U1) :=
  seen0 n ∪ (univ.filter fun x' : Fin E => x'.1 < x).biUnion fun x' => newUnits M x' o

/-- The units given before move `x`. -/
def used (x : ℕ) : Finset (Uid A U0 M.N U1) :=
  (univ.filter fun z : M.Z => z.1.1 < x).biUnion fun z => P.cons n o z

/-- The current units before move `x`. -/
def cur (x : ℕ) : Finset (Uid A U0 M.N U1) := seenAt n o x \ P.used n o x

/-- The outcome of the move `x` is possible: there is one index for every block. -/
def Poss (ub : ℕ) (x : Fin E) : Prop := ∃ ι : Fin (P.num n o x * ub) → (M.kind x).I, ∀ ν : (M.kind x).Cn,
  (o ⟨x, ν⟩).1 = (∑ k, ((M.kind x).lam + (M.kind x).len (ι k) ν)) / ub

/-- The rules that a plan obeys (`cap` bounds the numbers of units given in a move). -/
structure Ok (cap : ℕ) : Prop where
  causal : ∀ n o o' z, (∀ ν : M.N, ν.1 < z.1 → o ν = o' ν) → P.cons n o z = P.cons n o' z
  causal' : ∀ n o o' x, (∀ ν : M.N, ν.1 < x → o ν = o' ν) → P.num n o x = P.num n o' x
  causal'' : ∀ n o o' x, (∀ ν : M.N, ν.1 ≤ x → o ν = o' ν) → (P.good n o x ↔ P.good n o' x)
  sub : ∀ n o z, P.cons n o z ⊆ P.cur n o z.1
  hold : ∀ n o z, ∀ id ∈ P.cons n o z,
    (hold0 M.np id = M.zp z false ∧ hold1 M.np id = M.zp z true) ∨
    (hold1 M.np id = M.zp z false ∧ hold0 M.np id = M.zp z true)
  disj : ∀ n o (x : Fin E) e e', e ≠ e' → Disjoint (P.cons n o ⟨x, e⟩) (P.cons n o ⟨x, e'⟩)
  card : ∀ n o z, (P.cons n o z).card ≤ P.num n o z.1
  cap : ∀ n o x, P.num n o x ≤ cap

/-- The units given at a slot, in the order of the enumeration of all units. -/
noncomputable def ids (z : M.Z) : List (Uid A U0 M.N U1) :=
  (allIds A U0 M.N U1).filter fun id => id ∈ P.cons n o z

end Plan

variable {M} {ub : ℕ}

/-- The table of the role `p` of move `x` in the play. -/
noncomputable def roleAt (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1) (r : M.R)
    (y : Uid A U0 M.N U1 → UW ub) : F :=
  role M r.1 r.2 (P.num n o r.1) (fun e => P.ids n o ⟨r.1, e.1⟩) o y

/-- The table of party `a` after all moves, as a function of its copies of all units it has ever held. -/
noncomputable def partyTab (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1)
    (init : (Uid A U0 M.N U1 → UW ub) → F) (a : Fin (A + A')) (y : Uid A U0 M.N U1 → UW ub) : F :=
  init y * ∏ r : M.R, if M.rp r = a then roleAt P n o r y else 1

end Plans

section Start

variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {K c ub : ℕ} (mu : Letter S Unit Γ → Matrix Q Q F) (T : ℕ) (cb : Option Γ → Fin c → Bool)

open Classical in
/-- The table of party `p` at the beginning, as a function of its copies `y` of units. -/
noncomputable def tabInit (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → Cut.RowData (K + K))
    (n : Fin (K + K) → Fin (K + K) → ℕ) (p : Fin (K + K)) (y : Uid (K + K) U0 N U1 → UW ub) : F :=
  ∑ R ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T,
    ∑ C ∈ Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T,
      if (∀ s, Cut.RowOk (ρ s) (R s)) ∧ (∀ b, ucount ub (Cut.strOf cb fun s => R s b) = n p b ∧
          ∀ k : Fin U0, y (.init p b k) = unitsOf ub (Cut.strOf cb fun s => R s b) k) ∧
        (∀ b, ucount ub (Cut.strOf cb fun s => C s b) = n b p ∧
          ∀ k : Fin U0, y (.init b p k) = unitsOf ub (Cut.strOf cb fun s => C s b) k)
      then Cut.partyW mu T q x p R C else 0

/-- The table of a party after all moves: base parties start with the table of their block or part of the input, extra
parties with 1. -/
noncomputable def tabFinal {M : Sys F (K + K + A') E}
    (P : Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (ρ : Option S → Fin (K + K) → Cut.RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
    (o : M.N → Fin U1) (p : Fin (K + K + A')) : (Uid (K + K) U0 M.N U1 → UW ub) → F :=
  Fin.addCases (motive := fun _ => (Uid (K + K) U0 M.N U1 → UW ub) → F)
    (fun p => partyTab P n o (tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p) (Fin.castAdd A' p))
    (fun e => partyTab P n o (fun _ => 1) (Fin.natAdd (K + K) e)) p

/-- The value of a group. -/
noncomputable def grpVal {G : Type} [DecidableEq G] {M : Sys F (K + K + A') E}
    (P : Plan M U0 U1) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
    (ρ : Option S → Fin (K + K) → Cut.RowData (K + K)) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1))
    (o : M.N → Fin U1) (grp : Fin (K + K + A') → G) (g : G) (b : Uid (K + K) U0 M.N U1 → UW ub) : F :=
  groupVal (hold0 M.np) (hold1 M.np) none (Plan.seenAt n o E) (P.cur n o E) grp
    (tabFinal mu T cb P q x ρ n o) g b

end Start

end Nc.G
