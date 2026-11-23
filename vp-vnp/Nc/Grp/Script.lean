/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.GrpSteps
import NS1.Lists

/-!
# Scripts

The script of a group is a list of instructions for the program GROUP. Keys are bit lists (paths in a trie); contents of
units are lists of `ub` bits. All bit lists are `ofBits`, all small numbers `num`, all lists `listT`.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

/-- What a base party writes and reads. `flags`: for every tape (in the order of `univ.toList`) and every partner, **in
reverse order**: 0 = writes nothing, 1 = writes something, 2 = anything. `kR`, `kC`: for every partner (in order) the keys
of the units of the string to the partner, and from the partner. -/
structure Body where
  /-- row data -/
  flags : List (List ℕ)
  /-- keys of units written -/
  kR : List (List (List Bool))
  /-- keys of units read -/
  kC : List (List (List Bool))

/-- Instructions. -/
inductive Ins where
  /-- a block, from state number `q` to state number `q'` -/
  | block (q q' : ℕ) (B : Body)
  /-- an input party: its letters (their codes), **in reverse order** -/
  | input (part : List (List Bool)) (B : Body)
  /-- the contents at two keys agree -/
  | both (k k' : List Bool)
  /-- the content at a key is `w` -/
  | one (k w : List Bool)
  /-- a role, number `j` in the list of the roles of all laws, with `t` units. `slots`: for every slot (in the order of
  `univ.toList`) the keys of the units given, **in reverse order** (what is missing to `t` units is read as zeros). `keys`:
  for every channel (in the order of `univ.toList`) the keys of the new units. -/
  | role (j t : ℕ) (slots keys : List (List (List Bool)))

/-- Lists of keys. -/
def keysT (l : List (List (List Bool))) : Tree := listT (l.map fun ks => listT (ks.map ofBits))

namespace Body

/-- As a tree. -/
def tree (B : Body) : Tree :=
  .cons (listT (B.flags.map fun l => listT (l.map num))) (.cons (keysT B.kR) (keysT B.kC))

end Body

namespace Ins

/-- As a tree. -/
def tree : Ins → Tree
  | block q q' B => .cons (num 0) (.cons (.cons (num q) (num q')) B.tree)
  | input part B => .cons (num 1) (.cons (listT (part.map ofBits)) B.tree)
  | both k k' => .cons (num 2) (.cons (ofBits k) (ofBits k'))
  | one k w => .cons (num 3) (.cons (ofBits k) (ofBits w))
  | role j t slots keys => .cons (num (4 + j)) (.cons (num t)
      (.cons (keysT slots) (keysT keys)))

end Ins

/-- The argument of GROUP: `T` and `ub` in binary (most significant bit first), and the instructions. -/
def scriptT (bT bub : List Bool) (l : List Ins) : Tree :=
  .cons (.cons (ofBits bT) (ofBits bub)) (listT (l.map Ins.tree))

/-- The value of a binary number, most significant bit first. -/
def bval (w : List Bool) : ℕ := w.foldl (fun a b => 2 * a + b.toNat) 0

/-- The flag of a partner. -/
def rowFlag {A : ℕ} (d : RowData A) (b : Fin A) : ℕ :=
  if d.1 then 0 else if b = d.2.1 ∨ b = d.2.2 then 1 else if d.2.1 ≤ b ∧ b ≤ d.2.2 then 2 else 0

section group

variable {F : Type} [CommRing F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q] {A' K E U0 U1 ub c : ℕ} {Gr : Type} [DecidableEq Gr]

variable (qn : Q → ℕ) (cb : Option Γ → Fin c → Bool) {M : Sys F (K + K + A') E} (P : G.Plan M U0 U1)
  (q : Fin (K + 1) → Q) (x : Fin K → List Γ) (ρ : Option S → Fin (K + K) → RowData (K + K))
  (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (o : M.N → Fin U1) (grp : Fin (K + K + A') → Gr) (g : Gr)
  (key : Cell M U0 U1 → List Bool) (dkey : Fin (K + K) × Fin U0 → List Bool) (tg : M.R → ℕ)

/-- The body of the instruction of a base party. `dkey`: keys of the second copies of the units from a party to
itself. -/
noncomputable def bodyOf (p : Fin (K + K)) : Body where
  flags := (univ : Finset (Option S)).toList.map fun s => (List.ofFn fun b => rowFlag (ρ s p) b).reverse
  kR := List.ofFn fun b => ((List.finRange U0).filter fun k => k.1 < (n p b).1).map fun k =>
    key (Fin.castAdd A' p, .init p b k)
  kC := List.ofFn fun b => ((List.finRange U0).filter fun k => k.1 < (n b p).1).map fun k =>
    if b = p then dkey (p, k) else key (Fin.castAdd A' p, .init b p k)

/-- The instructions of a base party. -/
noncomputable def baseIns (p : Fin (K + K)) : List Ins :=
  Fin.addCases (motive := fun _ => Ins)
    (fun κ => .block (qn (q κ.castSucc)) (qn (q κ.succ)) (bodyOf ρ n key dkey (Fin.castAdd K κ)))
    (fun κ => .input ((x κ).map fun a => List.ofFn (cb (some a))).reverse (bodyOf ρ n key dkey (Fin.natAdd K κ))) p ::
  ((List.finRange U0).filter fun k => k.1 < (n p p).1).map fun k =>
    .both (key (Fin.castAdd A' p, .init p p k)) (dkey (p, k))

/-- The instruction of a role. -/
noncomputable def roleIns (r : M.R) : Ins :=
  .role (tg r) (P.num n o r.1)
    ((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map fun e =>
      ((P.ids n o ⟨r.1, e.1⟩).map fun id => key (M.rp r, id)).reverse)
    ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      ((List.finRange U1).filter fun k => k ≤ o ⟨r.1, ν.1⟩).map fun k => key (M.rp r, .new ⟨r.1, ν.1⟩ k))

/-- The instructions for the current units in the end. -/
noncomputable def endIns (b : G.Uid (K + K) U0 M.N U1 → UW ub) : List Ins :=
  ((G.allIds (K + K) U0 M.N U1).filter fun id => id ∈ P.cur n o E).filterMap fun id =>
    if grp (G.hold0 M.np id) = g then
      if grp (G.hold1 M.np id) = g then some (.both (key (G.hold0 M.np id, id)) (key (G.hold1 M.np id, id)))
      else some (.one (key (G.hold0 M.np id, id)) (uwBits (b id)))
    else if grp (G.hold1 M.np id) = g then some (.one (key (G.hold1 M.np id, id)) (uwBits (b id)))
    else none

/-- **The script of a group.** -/
noncomputable def script (b : G.Uid (K + K) U0 M.N U1 → UW ub) : List Ins :=
  (baseList (A' := A') grp g).flatMap (baseIns qn cb q x ρ n key dkey) ++
  (roleList grp g M).map (roleIns P n o key tg) ++ endIns P n o grp g key b

end group

end Nc.Grp
