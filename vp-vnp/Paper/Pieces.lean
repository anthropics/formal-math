/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Tree
import Paper.Runnet
import Paper.HeavyProg
import Nc.Dl.Cost
import Nc.G.Exact

/-!
# The paper, Proposition prop:pieces
-/

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 1000

namespace Paper

open Finset Nc Nc.G Nc.Dl Nc.Tow Nc.Vp Unc
open Nc.Tower (U x NN ee)
open NS1 (lg)

variable {A : Type} [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q]

section Identity

variable (mu : Nc.Letter S Unit Γ → Matrix Q Q A) {T c ub K N M b G₁ C : ℕ} (cb : Option Γ → Fin c → Bool)
  {laws : List (G.Law A)} {γ : ℝ}

/-- The contents of the units at a node, as copies of all units. -/
def yOf {AA E U1 : ℕ} {sysN : Type} [Fintype sysN] [DecidableEq sysN] (n : Fin AA → Fin AA → Fin (N + 1)) (a : Fin AA)
    (w : {u : NetUnit (fun a c => (n a c).1) // u.1 = a ∨ u.2.1 = a} → Fin ub → Bool) :
    Uid AA N sysN U1 → UW ub
  | .init p q k => if h : k.1 < (n p q).1 ∧ (p = a ∨ q = a) then some (w ⟨⟨p, q, ⟨k.1, h.1⟩⟩, h.2⟩) else none
  | .new _ _ => none

variable (TT : ThinTrees A laws (K + K) N ub M b G₁ C γ) (q : Fin (K + 1) → Q) (x : Fin K → List Γ)
  (ρ : Option S → Fin (K + K) → Nc.Cut.RowData (K + K)) (n : Dl.NN K N)

/-- The tables of the blocks and parts, as tables of the units at them. -/
noncomputable def runTab (a : Fin (K + K)) : NodeTable A (fun a c => (n a c).1) ub a := fun w =>
  G.tabInit mu T cb q x (fun s => ρ s a) (fun a b => (n a b).1) a
    (yOf (E := TT.E) (U1 := TT.U1) (sysN := TT.sys.N) n a w)

variable {mu cb TT q x ρ n}

theorem startTab_run (p : Fin (K + K + TT.A')) (y : Uid (K + K) N TT.sys.N TT.U1 → UW ub)
    (hy : ∀ a b (k : Fin N), ¬ (k.1 < (n a b).1 ∧ Holds (hold0 TT.sys.np) (hold1 TT.sys.np) p (Uid.init a b k : Uid (K + K) N TT.sys.N TT.U1)) →
      y (Uid.init a b k) = none) :
    startTab TT.sys TT.U1 n (runTab mu (T := T) cb TT q x ρ n) p y =
      initAll mu T cb TT.A' q x ρ n p y := by
  classical
  revert hy
  refine Fin.addCases (fun a => ?_) (fun e _ => ?_) p
  swap
  · simp only [startTab, initAll, Fin.addCases_right]
  intro hy
  simp only [startTab, initAll, Fin.addCases_left]
  split_ifs with hc
  · unfold runTab
    refine tabInit_congr fun p' q' k => ?_
    simp only [yOf]
    split_ifs with h
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hc ⟨⟨p', q', ⟨k.1, h.1⟩⟩, h.2⟩)
      have hk : Fin.castLE (Nat.le_of_lt_succ (n p' q').2) (⟨k.1, h.1⟩ : Fin (n p' q').1) = k := Fin.ext rfl
      simp only [hk] at hv ⊢
      rw [hv]
      rfl
    · refine (hy p' q' k fun h' => h ⟨h'.1, ?_⟩).symm
      rcases h'.2 with e | e
      · exact Or.inl (Fin.castAdd_injective _ _ e).symm
      · exact Or.inr (Fin.castAdd_injective _ _ e).symm
  · by_contra h0
    refine hc fun u => tabInit_ne_none (np := TT.sys.np) (Ne.symm h0) _ (init_mem_seen0.2 u.1.2.2.2) ?_
    rcases u.2 with e | e
    · exact Or.inl (congrArg (Fin.castAdd TT.A') e.symm)
    · exact Or.inr (congrArg (Fin.castAdd TT.A') e.symm)

open Classical in
/-- "Then apply Theorem thm:tree ... The units between different pieces are the cut units, and the value of a piece sums
over its inner units. Every assignment of units and letters is counted once": the value of one network of Lemma
lem:runnet, by the value of its thin trees and a regrouping of their nodes. -/
theorem prop_pieces_identity (hn : ∀ p, ∑ b, ((n p b).val + (n b p).val) ≤ N) {num : ℕ}
    (grp : (TT.sys.N → Fin TT.U1) → Fin (K + K + TT.A') → Fin num) :
    posVal (hold0 TT.sys.np) (hold1 TT.sys.np) (none : UW ub) (seen0 (N := TT.sys.N) (U1 := TT.U1) n) (seen0 n)
        (fun y => ∏ p : Fin (K + K), G.tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p
          (y (Fin.castAdd TT.A' p))) =
      ∑ o : TT.sys.N → Fin TT.U1, if ∀ z, TT.plan.good n o z then
        ∑ b ∈ Common (none : UW ub) (cutUnits (hold0 TT.sys.np) (hold1 TT.sys.np) (grp o) (TT.plan.cur n o TT.E)),
          ∏ g, G.grpVal mu T cb TT.plan q x ρ n o (grp o) g b
      else 0 := by
  have e0 : posVal (hold0 TT.sys.np) (hold1 TT.sys.np) (none : UW ub) (seen0 (N := TT.sys.N) (U1 := TT.U1) n) (seen0 n)
      (fun y => ∏ p : Fin (K + K), G.tabInit mu T cb q x (fun s => ρ s p) (fun a b => (n a b).1) p
        (y (Fin.castAdd TT.A' p))) =
      posVal (hold0 TT.sys.np) (hold1 TT.sys.np) (none : UW ub) (seen0 (N := TT.sys.N) (U1 := TT.U1) n) (seen0 n)
        (fun y => ∏ p, startTab TT.sys TT.U1 n (runTab mu (T := T) cb TT q x ρ n) p (y p)) := by
    unfold posVal
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [Nc.mem_contents_iff] at hy
    have e1 : ∀ p, startTab TT.sys TT.U1 n (runTab mu (T := T) cb TT q x ρ n) p (y p) =
        initAll mu T cb TT.A' q x ρ n p (y p) := fun p => startTab_run p (y p) fun a b k hk => hy p _ fun h => hk
      ⟨init_mem_seen0.1 h.1, h.2⟩
    simp only []
    rw [Finset.prod_congr rfl fun p _ => e1 p]
    conv_rhs => rw [Fin.prod_univ_add]
    simp [initAll]
  rw [e0, posVal_start, TT.value n hn]
  refine Finset.sum_congr rfl fun o _ => ?_
  by_cases hg : ∀ z, TT.plan.good n o z
  swap
  · rw [if_neg hg, if_neg hg]
  rw [if_pos hg, if_pos hg, ← posVal_groups, posVal_groups _ _ _ _ _ (grp o)]
  refine Finset.sum_congr rfl fun bb _ => Finset.prod_congr rfl fun g _ => ?_
  unfold G.grpVal groupVal
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Nc.mem_gcontents_iff] at hy
  congr 1
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [tabFinal_eq]
  simp only [partyTab]
  rw [startTab_run a (y a) fun p' q' k hk => hy a _ fun h => hk ⟨Plan.init_mem_seenAt.1 h.2.1, h.2.2⟩]

end Identity

open Classical in
/-- The pieces of Proposition prop:pieces for the scale v, K blocks of T steps and the parameter k, with the exponent
C and the list kinds of roles that may occur in moves. An input word is cut into K consecutive parts of ℓ ≤ T symbols;
ρ gives, for every node and side of a tape, the first and the last node that take the symbols of the node, n gives the
numbers of units, o the outcomes, and grp says in which piece a node is. At the beginning a node holds at most load
units. -/
structure PieceCut (kinds : List (Σ L : G.Law A, L.Ro)) (mu : Nc.Letter S Unit Γ → Matrix Q Q A)
    (b G₁ v K T k C : ℕ) where
  /-- bits for a symbol -/
  c : ℕ
  /-- the code of symbols -/
  cb : Option Γ → Fin c → Bool
  cb_inj : Function.Injective cb
  c_le : c ≤ C
  /-- bits of a unit -/
  ub : ℕ
  ub_pos : 0 < ub
  /-- the bound for units between two nodes -/
  U0 : ℕ
  /-- the bound for units at a node at the beginning -/
  load : ℕ
  /-- units have at most T bits, and a node starts with few of them -/
  unit_le : ub ≤ T ∧ load * ub ≤ T * lg v ^ C
  /-- the number of further nodes -/
  A' : ℕ
  /-- the number of moves -/
  E : ℕ
  /-- a bound for outcomes -/
  U1 : ℕ
  U1_pos : 0 < U1
  /-- the number of pieces -/
  num : ℕ
  /-- the digits of the program -/
  D : ℕ
  /-- the steps of the program -/
  steps : ℕ
  /-- the moves -/
  sys : Sys A (K + K + A') E
  /-- the plan -/
  plan : G.Plan sys U0 U1
  /-- a bound for the units of one move -/
  cap : ℕ
  /-- the plan is causal and gives only current units between the ends of their slots -/
  ok : plan.Ok cap
  /-- is the move a law move? -/
  isLaw : Fin E → Bool
  relay_kind : ∀ x, isLaw x = false → sys.kind x = relay A
  /-- what good means -/
  good_iff : ∀ n o x, plan.good n o x ↔ if isLaw x then
      b * ∑ ν : (sys.kind x).Cn, (o ⟨x, ν⟩).val ^ 2 ≤ G₁ * plan.num n o x ^ 2 ∧
        ∀ ν : (sys.kind x).Cn, plan.num n o x ≤ o ⟨x, ν⟩
    else ∀ ν : (sys.kind x).Cn, (o ⟨x, ν⟩).val = plan.num n o x
  /-- every possible outcome is good -/
  poss_good : ∀ n o x, plan.Poss n o ub x → plan.good n o x
  /-- the piece of a node -/
  grp : Dl.NN K U0 → (sys.N → Fin U1) → Fin (K + K + A') → Fin num
  /-- the program that computes units, moves, good outcomes and pieces from n and o -/
  tab : SlpTab plan grp D steps
  /-- it checks that no node has more than load units -/
  tab_valid : ∀ n, tab.valid n ↔ ∀ p, ∑ b, ((n p b).val + (n b p).val) ≤ load
  /-- its numbers have room for the units, the outcomes and the pieces -/
  digits : U0 < D ∧ U1 ≤ D ∧ num ≤ D ∧ 1 < D
  /-- every role at a move is from the fixed list, so its numbers of channels and slots are bounded -/
  kinds_mem : ∀ r : sys.R, ⟨sys.kind r.1, r.2⟩ ∈ kinds
  outcomes_le : Fintype.card sys.N ≤ v ^ C
  num_le : num ≤ k * lg v ^ C
  blocks_le : ∀ n o, (∀ p, ∑ b, ((n p b).val + (n b p).val) ≤ load) → (∀ x, plan.good n o x) → ∀ g,
    (univ.filter fun p : Fin (K + K) => grp n o (Fin.castAdd A' p) = g).card * k ≤ C * K
  cut_le : ∀ n o, (∀ p, ∑ b, ((n p b).val + (n b p).val) ≤ load) → (∀ x, plan.good n o x) → ∀ g,
    ((plan.cur n o E).filter (Nc.Plus.OneIn (hold0 sys.np) (hold1 sys.np) (grp n o) g)).card * ub * v ^ 300 ≤
      K * T * lg v ^ C
  all_le : ∀ n o, (∀ p, ∑ b, ((n p b).val + (n b p).val) ≤ load) → (∀ x, plan.good n o x) → ∀ g,
    (evG grp n o g + pdG plan grp n o g) * ub * k ≤ K * T * lg v ^ C
  steps_le : D ≤ v ^ C ∧ steps ≤ v ^ C ∧ K + K + A' ≤ v ^ C ∧ E ≤ v ^ C ∧ U0 ≤ v ^ C ∧ U1 ≤ v ^ C
  value : ∀ (i e : Q) (u : Unit → List Γ) (ℓ : ℕ), ℓ ≤ T → (u ()).length ≤ K * ℓ →
    Nc.runVal mu i e (K * T) u = ∑ q : Fin (K + 1) → Q, if q 0 = i ∧ q (Fin.last K) = e then
      ∑ ρ : Option S → Fin (K + K) → Nc.Cut.RowData (K + K), if Nc.Cut.ValidRows ρ then
        ∑ n : Dl.NN K U0, if ∀ p, ∑ b, ((n p b).val + (n b p).val) ≤ load then
          ∑ o : sys.N → Fin U1, if ∀ x, plan.good n o x then
            ∑ b ∈ Nc.Common (none : Nc.UW ub) (Nc.cutUnits (hold0 sys.np) (hold1 sys.np) (grp n o) (plan.cur n o E)),
              ∏ g, grpVal mu T cb plan q (Nc.Cut.parts ℓ (u ())) ρ n o (grp n o) g b
          else 0
        else 0
      else 0
    else 0

section Build

variable {K N ℓ M b G₁ C : ℕ} {laws : List (G.Law A)} {γ : ℝ} (TT : ThinTrees A laws (K + K) N ℓ M b G₁ C γ)

/-- The tree of the numbers of units and outcomes x. -/
def treeAt (x : Dl.NN K N × (TT.sys.N → Fin TT.U1)) : Staged (K + K + TT.A') where
  par := TT.par x.1 x.2
  stage := TT.stage
  depth := TT.depth
  root := TT.root
  stage_le := TT.stage_le
  stage_root := TT.stage_root
  stage_par := TT.stage_par x.1 x.2

/-- The given nodes: blocks and parts. -/
def given (K A' : ℕ) (p : Fin (K + K + A')) : ℕ := if (p : ℕ) < K + K then 1 else 0

/-- The bound Ŷ for the total of Theorem thm:tree(b). -/
def yhat (N M C : ℕ) : ℕ := lg M ^ C * M * (N + M ^ 2)

variable (k : ℕ)

/-- The piece of a node. -/
noncomputable def pieceAt (n : Dl.NN K N) (o : TT.sys.N → Fin TT.U1) (p : Fin (K + K + TT.A')) : ℕ :=
  (treeAt TT (n, o)).piece (given K TT.A') (TT.up n o) M (yhat N M C) k p

/-- The number of pieces. -/
def pieceNum : ℕ := min (1 + C + b * (TT.depth * k)) (K + K + TT.A')

theorem pieceNum_pos : 0 < pieceNum TT k := lt_min (by omega) (Fin.pos TT.root)

/-- The piece of a node, as a number below the number of pieces. -/
noncomputable def pieceFin (n : Dl.NN K N) (o : TT.sys.N → Fin TT.U1) (p : Fin (K + K + TT.A')) : Fin (pieceNum TT k) :=
  if h : pieceAt TT k n o p < pieceNum TT k then ⟨_, h⟩ else ⟨0, pieceNum_pos TT k⟩

theorem sum_given (A' : ℕ) : ∑ p, given K A' p = K + K := by
  rw [Fin.sum_univ_add]
  simp [given]

theorem given_le (A' : ℕ) (p : Fin (K + K + A')) : given K A' p ≤ 1 := by
  unfold given
  split_ifs <;> omega

variable {TT k} {n : Dl.NN K N} {o : TT.sys.N → Fin TT.U1} (hn : ∀ p, ∑ c, ((n p c).val + (n c p).val) ≤ N)
  (hg : ∀ z, TT.plan.good n o z) (hK : 0 < K) (hM : K + K ≤ M) (hk : 0 < k)
include hn hg hK hM hk

theorem yhat_pos : 0 < yhat N M C := by
  have hlg : 0 < lg M := Nat.succ_pos _
  have hM0 : 0 < M := by omega
  exact Nat.mul_pos (Nat.mul_pos (Nat.pow_pos hlg) hM0) (Nat.add_pos_right _ (Nat.pow_pos hM0))

theorem pieceFin_val (p : Fin (K + K + TT.A')) : (pieceFin TT k n o p : ℕ) = pieceAt TT k n o p := by
  have h : pieceAt TT k n o p < pieceNum TT k := lt_min
    (prop_pieces_count hk (by omega) (yhat_pos hn hg hK hM hk) ((sum_given _).le.trans hM) (TT.up_total n hn o hg)
      (fun p hp => TT.children_le n o p hp) (TT.root_children_le n o) p)
    (Staged.piece_lt p)
  rw [pieceFin, dif_pos h]

theorem pieceFin_iff (p : Fin (K + K + TT.A')) (g : Fin (pieceNum TT k)) :
    pieceFin TT k n o p = g ↔ pieceAt TT k n o p = g.val := by rw [Fin.ext_iff, pieceFin_val hn hg hK hM hk]

/-- "A subtree has at most 4M/k given nodes and a single node has fewer still." -/
theorem piece_given (hk' : k ≤ 4 * M) (g : Fin (pieceNum TT k)) :
    k * ∑ p ∈ univ.filter (fun p => pieceFin TT k n o p = g), given K TT.A' p ≤ 4 * M := by
  classical
  rw [Finset.mul_sum, Finset.filter_congr fun p _ => pieceFin_iff hn hg hK hM hk p g]
  refine Staged.piece_sum_le _ _ (fun p => ?_) (fun x hx => ?_) _
  · exact (Nat.mul_le_mul_left _ (given_le _ p)).trans (by rwa [Nat.mul_one])
  · refine le_trans (le_of_eq ?_) (Staged.light_le (by omega) (yhat_pos hn hg hK hM hk) hx).1
    unfold Staged.below
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by split_ifs <;> simp

theorem piece_blocks (hk' : k ≤ 4 * M) (g : Fin (pieceNum TT k)) :
    (univ.filter fun p : Fin (K + K) => pieceFin TT k n o (Fin.castAdd TT.A' p) = g).card * k ≤ 4 * M := by
  refine le_trans ?_ (piece_given hn hg hK hM hk hk' g)
  rw [Nat.mul_comm]
  refine Nat.mul_le_mul_left _ ?_
  rw [Finset.sum_filter, Fin.sum_univ_add, card_filter]
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) (Nat.le_add_right _ _)
  simp [given]

variable {w : ℕ} (hkw : k ≤ w)
  (hnode : ∀ X : ℕ, (X : ℝ) ≤ (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - γ) * (N + (M : ℝ) ^ 2) → X * w ≤ yhat N M C)
include hkw hnode

open Classical in
/-- "By (b) of the theorem a piece has at most ΛM^(1−γ)Nℓ bits in cut units, besides the dead ones." -/
theorem piece_cut (g : Fin (pieceNum TT k)) :
    ((TT.plan.cur n o TT.E).filter (Nc.Plus.OneIn (hold0 TT.sys.np) (hold1 TT.sys.np) (pieceFin TT k n o) g)).card * w ≤
      yhat N M C + M ^ C * w := by
  obtain ⟨x, hx⟩ := Staged.piece_boundary (T := treeAt TT (n, o)) (giv := given K TT.A') (u := TT.up n o) (M := M)
    (Y := yhat N M C) (k := k) g.val
  refine le_trans (Nat.mul_le_mul_right w (card_le_card (t := (cutUnits (hold0 TT.sys.np) (hold1 TT.sys.np) id
    (TT.plan.cur n o TT.E \ TT.dead o)).filter (Holds (hold0 TT.sys.np) (hold1 TT.sys.np) x) ∪ TT.dead o) ?_)) ?_
  · intro id hid
    obtain ⟨hcur, hone⟩ := mem_filter.1 hid
    by_cases hd : id ∈ TT.dead o
    · exact mem_union_right _ hd
    refine mem_union_left _ ?_
    have hl : hold0 TT.sys.np id ≠ hold1 TT.sys.np id := fun e => by
      unfold Nc.Plus.OneIn at hone
      rw [e] at hone
      tauto
    have hu : id ∈ cutUnits (hold0 TT.sys.np) (hold1 TT.sys.np) _root_.id (TT.plan.cur n o TT.E \ TT.dead o) :=
      mem_filter.2 ⟨mem_sdiff.2 ⟨hcur, hd⟩, hl⟩
    refine mem_filter.2 ⟨hu, ?_⟩
    obtain ⟨q, hq, he⟩ := TT.edge n hn o hg id hu
    have hne : ¬ (pieceAt TT k n o q = g.val ↔ pieceAt TT k n o (TT.par n o q) = g.val) := by
      rw [← pieceFin_iff hn hg hK hM hk, ← pieceFin_iff hn hg hK hM hk]
      unfold Nc.Plus.OneIn at hone
      rcases Sym2.eq_iff.1 he with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2] at hone
        tauto
      · rw [e1, e2] at hone
        tauto
    have hxm : x ∈ s(hold0 TT.sys.np id, hold1 TT.sys.np id) := by
      rw [he, Sym2.mem_iff]
      exact (hx q hq hne).imp Eq.symm Eq.symm
    exact (Sym2.mem_iff.1 hxm)
  · refine (Nat.mul_le_mul_right _ (card_union_le _ _)).trans ?_
    rw [add_mul]
    exact Nat.add_le_add (hnode _ (TT.node_le n hn o hg x)) (Nat.mul_le_mul_right _ (TT.dead_le o))

open Classical in
/-- "Units used up and zeros in slots change this by a constant factor only": the bits in all. -/
theorem piece_all (hk' : k ≤ 4 * M) (g : Fin (pieceNum TT k)) :
    (evG (fun n o => pieceFin TT k n o) n o g + pdG TT.plan (fun n o => pieceFin TT k n o) n o g) * k ≤
      C * (4 * yhat N M C) + 4 * M * (lg M ^ C * N) + 2 * C * M ^ C * k := by
  set S := univ.filter fun p => pieceFin TT k n o p = g with hS
  have h1 : evG (fun n o => pieceFin TT k n o) n o g + pdG TT.plan (fun n o => pieceFin TT k n o) n o g =
      ∑ p ∈ S, (((Plan.seenAt n o TT.E).filter (Holds (hold0 TT.sys.np) (hold1 TT.sys.np) p)).card +
        ∑ r ∈ univ.filter (fun r : TT.sys.R => TT.sys.rp r = p),
          (1 + Fintype.card ((TT.sys.kind r.1).SlAt r.2)) * TT.plan.num n o r.1) := by
    rw [Finset.sum_add_distrib]
    congr 1
    unfold pdG
    rw [← Finset.sum_fiberwise_of_maps_to (g := TT.sys.rp) (t := S)
      (fun r hr => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hr).2⟩)]
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr ?_ fun _ _ => rfl
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun r _ => ⟨fun e => e.2, fun e => ⟨?_, e⟩⟩
    rw [e]
    exact (mem_filter.1 hp).2
  rw [h1]
  refine (Nat.mul_le_mul_right _ (Finset.sum_le_sum fun p _ => TT.copies_le n hn o hg p)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, add_mul, add_mul]
  refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
  · rw [← Finset.mul_sum, Nat.mul_assoc, Finset.sum_mul]
    refine Nat.mul_le_mul_left _ ?_
    rw [hS, Finset.filter_congr fun p _ => pieceFin_iff hn hg hK hM hk p g]
    refine Staged.piece_sum_le _ _ (fun p => ?_) (fun y hy => ?_) _
    · refine (Nat.mul_le_mul_left _ hkw).trans ((hnode _ ?_).trans (Nat.le_mul_of_pos_left _ (by norm_num)))
      exact TT.up_node n hn o hg p
    · have h2 := (Staged.light_le (by omega) (yhat_pos hn hg hK hM hk) hy).2
      have h3 := Staged.below_kids (T := treeAt TT (n, o)) (TT.up n o) y
      have e : (treeAt TT (n, o)).below (fun p => (TT.up n o p + (treeAt TT (n, o)).kids (TT.up n o) p) * k) y =
          ((treeAt TT (n, o)).below (TT.up n o) y + (treeAt TT (n, o)).below ((treeAt TT (n, o)).kids (TT.up n o)) y) * k := by
        unfold Staged.below
        rw [← Finset.sum_add_distrib, Finset.sum_mul]
        exact Finset.sum_congr rfl fun q _ => by split_ifs <;> simp
      refine le_of_eq_of_le e ?_
      calc _ ≤ ((treeAt TT (n, o)).below (TT.up n o) y + (treeAt TT (n, o)).below (TT.up n o) y) * k :=
            Nat.mul_le_mul_right _ (Nat.add_le_add_left h3 _)
        _ = 2 * (k * (treeAt TT (n, o)).below (TT.up n o) y) := by ring
        _ ≤ _ := by omega
  · calc (∑ p ∈ S, if (p : ℕ) < K + K then lg M ^ C * N else 0) * k =
        (k * ∑ p ∈ S, given K TT.A' p) * (lg M ^ C * N) := by
          rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun p _ => ?_
          unfold given
          split_ifs <;> ring
      _ ≤ _ := Nat.mul_le_mul_right _ (piece_given hn hg hK hM hk hk' g)
  · refine Nat.mul_le_mul_right _ ?_
    calc ∑ p ∈ S, C * ((TT.dead o).filter (Holds (hold0 TT.sys.np) (hold1 TT.sys.np) p)).card ≤
        C * ∑ p, ((TT.dead o).filter (Holds (hold0 TT.sys.np) (hold1 TT.sys.np) p)).card := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum_of_subset (subset_univ _)
      _ ≤ C * (2 * (TT.dead o).card) := by
          refine Nat.mul_le_mul_left _ ?_
          simp only [card_filter]
          rw [Finset.sum_comm, Nat.mul_comm 2, ← smul_eq_mul (a := (TT.dead o).card), ← Finset.sum_const]
          refine Finset.sum_le_sum fun u _ => ?_
          rw [← card_filter]
          refine (card_le_card (t := {hold0 TT.sys.np u, hold1 TT.sys.np u}) fun p hp => ?_).trans card_le_two
          rw [mem_insert, mem_singleton]
          exact (mem_filter.1 hp).2
      _ ≤ C * (2 * M ^ C) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (TT.dead_le o))
      _ = _ := by ring

end Build

theorem ind_ite {X : Type} {P : X → Prop} {x : X} {i : Decidable (P x)} : ind P x = @ite ℕ (P x) i 1 0 := by
  by_cases hp : P x
  · rw [ind_true hp, if_pos hp]
  · rw [ind_false hp, if_neg hp]

theorem ind_eq_one {X : Type} {P : X → Prop} {x : X} : ind P x = 1 ↔ P x := by
  by_cases hp : P x
  · simp [ind_true hp, hp]
  · simp [ind_false hp, hp]

section Prog

/-- The inputs are added to a program. -/
theorem slp_inputs {Inp ι : Type} [Fintype ι] {D p : ℕ} {inp : ι → Inp → Fin D} {H : Set (Inp → ℕ)}
    (h : SlpN inp p H) : SlpN inp (p + Fintype.card ι) (H ∪ Set.range fun i x => (inp i x : ℕ)) := by
  classical
  have : ∀ s : Finset ι, SlpN inp (p + s.card) (H ∪ (fun i x => (inp i x : ℕ)) '' (s : Set ι)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h
    | insert i s hi ih =>
      rw [card_insert_of_notMem hi]
      refine (ih.snoc (inp i) (Or.inl ⟨i, rfl⟩)).mono ?_
      rintro f (hf | ⟨j, hj, rfl⟩)
      · exact Set.mem_insert_of_mem _ (Or.inl hf)
      · rcases mem_insert.mp (mem_coe.mp hj) with h | h
        · subst h; exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (Or.inr ⟨j, mem_coe.mpr h, rfl⟩)
  have h2 := this univ
  rw [coe_univ, Set.image_univ, card_univ] at h2
  exact h2

variable {K N ℓ M b G₁ C : ℕ} {laws : List (G.Law A)} {γ : ℝ} (TT : ThinTrees A laws (K + K) N ℓ M b G₁ C γ)

open Classical in
/-- "The units, the pieces and what each table does are computed from the numbers of units and the outcomes": the
program of Theorem thm:tree(d), extended by the pieces and by the check of the numbers. -/
theorem prop_pieces_program (k : ℕ) {Y : ℕ} (hY : 16 ≤ Y) (hMY : (M * N) ^ C ≤ Y) (hKY : K + K ≤ Y) (hNY : N ≤ Y)
    (hdY : TT.depth ≤ Y) (hin : (K + K) * (K + K) + Fintype.card TT.sys.N ≤ Y) :
    N < Y ^ 4 ∧ TT.U1 ≤ Y ^ 4 ∧ pieceNum TT k ≤ Y ^ 4 ∧
    ∃ tab : SlpTab TT.plan (fun n o => pieceFin TT k n o) (Y ^ 4) (Y ^ 15),
      ∀ n, tab.valid n ↔ ∀ p, ∑ c, ((n p c).val + (n c p).val) ≤ N := by
  obtain ⟨D₀, s₀, inp₀, H₀, d1, d2, d3, d4, d5, d6, i1, i2, hS, p1, p2, p3, p4, p5, p6⟩ := TT.computed
  have hA : Alph (Y ^ 4) Y := ⟨by omega, le_rfl⟩
  have hY4 : Y < Y ^ 4 := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ < Y ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hDY : D₀ ≤ Y := d1.trans hMY
  have hP : K + K + TT.A' ≤ Y := d3.trans hMY
  have hnum : pieceNum TT k ≤ Y := (min_le_right _ _).trans hP
  refine ⟨by omega, by omega, by omega, ?_⟩
  let inp : (Fin (K + K) × Fin (K + K)) ⊕ TT.sys.N → Dl.NN K N × (TT.sys.N → Fin TT.U1) → Fin (Y ^ 4) := fun i x =>
    ⟨(inp₀ i x).1, by have := (inp₀ i x).2; omega⟩
  have s0 := slp_inputs (slp_cast (inp' := inp) (show D₀ ≤ Y ^ 4 by omega) (fun i x => rfl) hS)
  set H : Set (Dl.NN K N × (TT.sys.N → Fin TT.U1) → ℕ) := H₀ ∪ Set.range fun i x => (inp i x : ℕ) with hH
  obtain ⟨p₀, hp₀⟩ : ∃ p₀, p₀ = s₀ + Fintype.card ((Fin (K + K) × Fin (K + K)) ⊕ TT.sys.N) := ⟨_, rfl⟩
  have hS0 : SY inp Y p₀ 0 H := by
    unfold SY
    rw [Nat.zero_mul, Nat.add_zero, hp₀]
    exact s0
  have hlt : ∀ f ∈ H₀, ∀ x, f x ≤ Y := fun f hf x => by
    obtain ⟨fn, -, h2⟩ := hS
    obtain ⟨i, -, e⟩ := h2 f hf
    rw [← e x]
    exact (fn i x).2.le.trans hDY
  obtain ⟨H1, s1, u1, f1⟩ := Staged.piece_prog (T := treeAt TT) (st := TT.stage) (dp := TT.depth) (rt := TT.root)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hA hP (giv := given K TT.A') (u := fun x => TT.up x.1 x.2) (M := M)
    (Yh := yhat N M C) (k := k) hS0 (fun q q' => Or.inl (p1 q q')) (fun q => Or.inl (p5 q)) (given_le _)
    (fun x q => hlt _ (p5 q) x)
  obtain ⟨H2, s2, u2, f2⟩ := s1.add hA (fun p x => (pieceFin TT k x.1 x.2 p : ℕ)) (a := 1) (e := 1)
    (by rw [Fintype.card_fin, pow_one]; exact hP) (fun p => by
      have e : ∀ x : Dl.NN K N × (TT.sys.N → Fin TT.U1), (pieceFin TT k x.1 x.2 p : ℕ) =
          (fun a => if a < pieceNum TT k then a else 0) (pieceAt TT k x.1 x.2 p) := fun x => by
        unfold pieceFin
        split_ifs with h <;> simp [h]
      refine CY.congr ?_ fun x => (e x).symm
      exact CY.op1 hA (fun a => if a < pieceNum TT k then a else 0) (CY.base (f1 p) hA.pos) fun x => by
        refine lt_of_eq_of_lt (e x).symm ?_
        exact hA.lt_of_le ((pieceFin TT k x.1 x.2 p).2.le.trans hnum)) (by omega)
  obtain ⟨H3, s3, u3, f3⟩ := s2.add hA (fun id => ind fun x : Dl.NN K N × (TT.sys.N → Fin TT.U1) =>
      id ∈ TT.plan.cur x.1 x.2 TT.E ∧
        pieceFin TT k x.1 x.2 (hold0 TT.sys.np id) ≠ pieceFin TT k x.1 x.2 (hold1 TT.sys.np id)) (a := 2) (e := 1)
    (by rw [pow_one]; exact d6.trans hMY) (fun id => by
      refine (PY.congr (PY.and hA ((PY.base (u2 (u1 (Or.inl (p2 id)))) hA.pos).mono hA.pos (show 0 ≤ 1 by omega))
        (PY.rel hA (fun a c => a ≠ c) (CY.base (f2 (hold0 TT.sys.np id)) hA.pos)
          (CY.base (f2 (hold1 TT.sys.np id)) hA.pos))) fun x => ?_).toCY
      exact and_congr_right fun _ => not_congr Fin.val_inj) (by omega)
  have hin' : ∀ i, (fun x => (inp i x : ℕ)) ∈ H3 := fun i => u3 (u2 (u1 (Or.inr ⟨i, rfl⟩)))
  obtain ⟨H4, s4, u4, f4⟩ := s3.add hA (fun p : Fin (K + K) => ind fun x : Dl.NN K N × (TT.sys.N → Fin TT.U1) =>
      ∑ c, ((x.1 p c).val + (x.1 c p).val) ≤ N) (a := 4) (e := 1) (by rw [Fintype.card_fin, pow_one]; exact hKY)
    (fun p => by
      have hb : ∀ (x : Dl.NN K N × (TT.sys.N → Fin TT.U1)) c, (x.1 p c).val + (x.1 c p).val ≤ 2 * Y := fun x c => by
        have := (x.1 p c).2
        have := (x.1 c p).2
        omega
      have h1 : CY (Y ^ 4) H3 Y 3 fun x : Dl.NN K N × (TT.sys.N → Fin TT.U1) =>
          ∑ c ∈ univ, ((x.1 p c).val + (x.1 c p).val) := by
        refine CY.sum hA univ (by simpa using hKY) (fun c _ => CY.op hA (fun a b => a + b)
          ((CY.base (hin' (.inl (p, c))) hA.pos).congr fun x => i1 p c x)
          ((CY.base (hin' (.inl (c, p))) hA.pos).congr fun x => i1 c p x)
          fun x => hA.lt_of_le3 ((hb x c).trans ?_)) fun x => hA.lt_of_le3 ?_
        · exact Nat.mul_le_mul_left _ (Nat.le_self_pow (by norm_num) _)
        · calc ∑ c ∈ univ, ((x.1 p c).val + (x.1 c p).val) ≤ ∑ _c : Fin (K + K), 2 * Y :=
                Finset.sum_le_sum fun c _ => hb x c
            _ = (K + K) * (2 * Y) := by simp
            _ ≤ Y * (2 * Y) := Nat.mul_le_mul_right _ hKY
            _ = 2 * Y ^ 2 := by ring
            _ ≤ 2 * Y ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hA.pos (by norm_num))
      exact (PY.rel1 hA (fun a => a ≤ N) h1).toCY) (by omega)
  obtain ⟨H5, s5, u5, f5⟩ := s4.add hA (fun _ : Unit => ind fun x : Dl.NN K N × (TT.sys.N → Fin TT.U1) =>
      ∀ p, ∑ c, ((x.1 p c).val + (x.1 c p).val) ≤ N) (a := 2) (e := 1) (by rw [Fintype.card_unit, pow_one]; omega)
    (fun _ => (PY.forall_univ hA (by simpa using hKY) fun p => PY.base (f4 p) hA.pos).toCY) (by omega)
  have hsteps : p₀ + (0 + 2 * TT.depth + 9 + 1 + 1 + 1 + 1) * Y ^ 12 ≤ Y ^ 15 := by
    have h1 : p₀ ≤ 2 * Y := by
      rw [hp₀, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      have := d2.trans hMY
      omega
    have h2 : 0 + 2 * TT.depth + 9 + 1 + 1 + 1 + 1 ≤ 3 * Y := by omega
    have h3 : 2 * Y ≤ 2 * Y * Y ^ 12 := Nat.le_mul_of_pos_right _ (Nat.pow_pos hA.pos)
    calc _ ≤ 2 * Y * Y ^ 12 + 3 * Y * Y ^ 12 := Nat.add_le_add (h1.trans h3) (Nat.mul_le_mul_right _ h2)
      _ = 5 * Y ^ 13 := by ring
      _ ≤ Y * Y ^ 13 := Nat.mul_le_mul_right _ (by omega)
      _ = Y ^ 14 := by ring
      _ ≤ Y ^ 15 := Nat.pow_le_pow_right hA.pos (by norm_num)
  obtain ⟨fn, hst, hfn⟩ := SlpN.le hA.zero_lt hsteps s5
  have ex : ∀ f, f ∈ H5 → ∃ q : Fin (Y ^ 15), ∀ x, (fn q x : ℕ) = f x := by
    intro f hf
    obtain ⟨q, hq, hx⟩ := hfn f hf
    exact ⟨⟨q, hq⟩, hx⟩
  choose ix hix using ex
  have l0 : ∀ f, f ∈ H₀ → f ∈ H5 := fun f hf => u5 (u4 (u3 (u2 (u1 (Or.inl hf)))))
  refine ⟨{
    fn := fn
    inp := inp
    inpN := fun a c x => i1 a c x
    inpO := fun ν x => i2 ν x
    step := hst
    kcur := fun id => ix _ (l0 _ (p2 id))
    hcur := fun id x => by rw [hix]; exact ind_ite (P := fun x : Dl.NN K N × _ => id ∈ TT.plan.cur x.1 x.2 TT.E)
    kcut := fun id => ix _ (u5 (u4 (f3 id)))
    hcut := fun id x => (hix _ _ x).trans ind_ite
    kcons := fun z id => ix _ (l0 _ (p3 z id))
    hcons := fun z id x => by rw [hix]; exact ind_ite (P := fun x : Dl.NN K N × _ => id ∈ TT.plan.cons x.1 x.2 z)
    knum := fun y => ix _ (l0 _ (p4 y))
    hnum := fun y x => by rw [hix]
    kcond := fun y => match y with
      | none => ix _ (f5 ())
      | some y => ix _ (l0 _ (p6 y))
    valid := fun n => ∀ p, ∑ c, ((n p c).val + (n c p).val) ≤ N
    hgood := fun y x => by
      rw [hix]
      exact ind_eq_one (P := fun x : Dl.NN K N × _ => TT.plan.good x.1 x.2 y)
    hvalid := fun x => by
      rw [hix]
      exact ind_eq_one (P := fun x : Dl.NN K N × (TT.sys.N → Fin TT.U1) => ∀ p, ∑ c, ((x.1 p c).val + (x.1 c p).val) ≤ N)
    kgrp := fun p => ix _ (u5 (u4 (u3 (f2 p))))
    hgrp := fun p x => by rw [hix] }, fun n => Iff.rfl⟩

end Prog

/-- **Paper: proof of Proposition prop:pieces.** "All M^C dead units together have at most T/v^300 bits." -/
theorem prop_pieces_dead {v e M C₀ a' T : ℕ} (hv : 1 ≤ v) (hM : M ≤ v ^ (e + 1)) (ha : (e + 1) * C₀ + 300 ≤ a') {ub : ℕ}
    (hub : ub = T / v ^ a') : M ^ C₀ * v ^ 300 * ub ≤ T := by
  refine le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM C₀))) ?_
  rw [← pow_mul, ← pow_add, Nat.mul_comm, hub]
  exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hv ha)).trans (Nat.div_mul_le_self _ _)

/-- The numbers of Proposition prop:pieces: "units of ⌊T/v^a'⌋ bits, so that all M^C dead units together have at most
T/v^300 bits", and N, a bound for the units at a node. -/
theorem pieces_numbers {c σ v e M C₀ a' T : ℕ} (hc : 1 ≤ c) (hσ : 1 ≤ σ) (hv : 8 * c + 2 * σ + 16 ≤ v) (hM1 : 1 ≤ M)
    (hM : M ≤ v ^ (e + 1)) (ha : (e + 2) * (C₀ + 2) + 300 ≤ a') (hT : v ^ (a' + e + 3) ≤ T) {ub load : ℕ}
    (hub : ub = T / v ^ a') (hload : load = 2 * ((T + M * σ) * c / ub + M)) :
    0 < ub ∧ ub ≤ T ∧ load * ub ≤ (4 * c + 4) * T ∧ M ^ 2 * ub ≤ T ∧ M ^ C₀ * v ^ 300 * ub ≤ T ∧
      load ≤ v ^ (a' + 1) ∧ (T + σ) * c / ub + 1 ≤ load := by
  have pw : ∀ x y, x ≤ y → v ^ x ≤ v ^ y := fun x y h => Nat.pow_le_pow_right (by omega) h
  have hp : 0 < v ^ a' := Nat.pow_pos (by omega)
  have hub0 : 0 < ub := hub ▸ Nat.div_pos ((pw a' _ (by omega)).trans hT) hp
  have hubT : ub * v ^ a' ≤ T := hub ▸ Nat.div_mul_le_self _ _
  have hTub : T < (ub + 1) * v ^ a' := by
    rw [hub, add_mul, one_mul]
    exact Nat.lt_div_mul_add hp
  have hMσ : M * σ ≤ T := by
    calc M * σ ≤ v ^ (e + 1) * v := Nat.mul_le_mul hM (by omega)
      _ ≤ T := by rw [← pow_succ]; exact (pw _ _ (by omega)).trans hT
  have hmul : ∀ d, d ≤ a' → v ^ d * ub ≤ T := fun d hd => by
    rw [Nat.mul_comm]
    exact (Nat.mul_le_mul_left _ (pw d a' hd)).trans hubT
  have hM2 : M ^ 2 * ub ≤ T := by
    refine le_trans (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM 2)) ?_
    rw [← pow_mul]
    exact hmul _ (by nlinarith)
  have hMub : M * ub ≤ T := (Nat.mul_le_mul_right _ (Nat.le_self_pow (by norm_num) M)).trans hM2
  have h2T : (T + M * σ) * c ≤ 2 * T * c := Nat.mul_le_mul_right _ (by omega)
  refine ⟨hub0, (Nat.le_mul_of_pos_right _ hp).trans hubT, ?_, hM2, ?_, ?_, ?_⟩
  · have h1 := Nat.div_mul_le_self ((T + M * σ) * c) ub
    have e1 : load * ub = 2 * ((T + M * σ) * c / ub * ub) + 2 * (M * ub) := by rw [hload]; ring
    have e2 : (4 * c + 4) * T = 2 * (2 * T * c) + 4 * T := by ring
    omega
  · exact prop_pieces_dead (by omega) hM (by nlinarith) hub
  · have h1 : (T + M * σ) * c / ub ≤ 4 * c * v ^ a' := by
      refine Nat.div_le_of_le_mul (h2T.trans ?_)
      calc 2 * T * c ≤ 2 * ((ub + ub) * v ^ a') * c := by
            refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hTub.le.trans ?_))
            gcongr
            omega
        _ = ub * (4 * c * v ^ a') := by ring
    have h2 : M ≤ v ^ a' := hM.trans (pw _ _ (by nlinarith))
    calc load ≤ 2 * (4 * c * v ^ a' + v ^ a') := by rw [hload]; gcongr
      _ = (8 * c + 2) * v ^ a' := by ring
      _ ≤ v * v ^ a' := Nat.mul_le_mul_right _ (by omega)
      _ = v ^ (a' + 1) := (pow_succ' v a').symm
  · have h1 : (T + σ) * c / ub ≤ (T + M * σ) * c / ub :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hM1) _))
    omega

/-- The gain: units at one node against all units. -/
theorem pieces_gain {M q w Λ R X : ℕ} (hq : 0 < q) (hM : 0 < M) (hw : w ^ q ≤ M)
    (hX : (X : ℝ) ≤ (Λ : ℝ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * R) : X * w ≤ Λ * M * R := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : (w : ℝ) ≤ (M : ℝ) ^ (1 / (q : ℝ)) := by
    have h2 : (w : ℝ) ^ q ≤ (M : ℝ) := by exact_mod_cast hw
    have h3 := Real.rpow_le_rpow (by positivity) h2 (show (0 : ℝ) ≤ (q : ℝ)⁻¹ by positivity)
    rw [Real.pow_rpow_inv_natCast (Nat.cast_nonneg w) hq.ne'] at h3
    rwa [one_div]
  have h4 : ((X * w : ℕ) : ℝ) ≤ ((Λ * M * R : ℕ) : ℝ) := by
    push_cast
    refine (mul_le_mul hX h1 (Nat.cast_nonneg _) (by positivity)).trans (le_of_eq ?_)
    calc (Λ : ℝ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * R * (M : ℝ) ^ (1 / (q : ℝ)) =
        Λ * ((M : ℝ) ^ (1 - 1 / (q : ℝ)) * (M : ℝ) ^ (1 / (q : ℝ))) * R := by ring
      _ = _ := by rw [← Real.rpow_add hM0, sub_add_cancel, Real.rpow_one]
  exact_mod_cast h4

set_option maxHeartbeats 1600000 in
/-- **Paper: Proposition prop:pieces.** "For every tape automaton over A there are constants a, e, C (a and e do not
depend on the automaton) such that for all large v there is K with v^e ≤ K ≤ Cv^e and the following holds for all
T ≥ v^a with lg T ≤ (lg v)² and all 2 ≤ k ≤ v^64. Cut an input word of at most KT′ symbols, T′ ≤ T, into K consecutive
parts. The value of the automaton in KT steps is the sum, over boundary states, valid data ρ as in Lemma lem:runnet,
numbers of units, good outcomes, and the contents of cut units, of products of the values of at most kΛ pieces. A piece
has at most CK/k blocks and parts, at most KTΛ/v^300 bits in cut units, and at most KTΛ/k bits in all. The units, the
pieces and what each table does are computed from the numbers of units and the outcomes by v^C binary operations on
numbers below v^C."
Here Λ = (lg v)^C, e ≥ 300 (as chosen in the printed proof) and the bound on lg T is not needed; bits in all count every copy that the nodes of the piece ever
hold and the zeros in slots. What a table does is given by the units and the number of each move (cons and num),
because the kind of each role is one of the fixed list of roles of the relay and the laws. A step is one binary
operation on numbers below v^C, in a program that may depend on v, T and k. The proof applies Lemma lem:runnet, then
Theorem thm:tree, and calls the nodes heavy as printed. -/
theorem prop_pieces {h : ℕ} [NeZero h] (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h3 : 3 ≤ h)
    (hgain : 1 + 8 * VL.C₁ ≤ (h : ℝ) / 4) :
    ∃ a e : ℕ, 300 ≤ e ∧ ∀ (Γ S Q : Type) [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
      (mu : Nc.Letter S Unit Γ → Matrix Q Q A),
      ∃ C v₀ : ℕ, ∀ v, v₀ ≤ v → ∃ K, v ^ e ≤ K ∧ K ≤ C * v ^ e ∧
        ∀ T k, v ^ a ≤ T → 2 ≤ k → k ≤ v ^ 64 →
          Nonempty (PieceCut (kindList A ((univ : Finset VL.Di).toList.map VL.L)) mu (2 ^ ee h)
            (goodBound VL.C₁ VL.a₁) v K T k C) := by
  classical
  obtain ⟨C₀, htree⟩ := thm_tree VL h3 hgain
  have hq : 0 < ee h := by
    unfold Nc.Tower.ee
    have : 3 * 2 ≤ h * (h - 1) := Nat.mul_le_mul h3 (by omega)
    omega
  obtain ⟨e, he⟩ : ∃ e, e = 300 * ee h + 64 := ⟨_, rfl⟩
  obtain ⟨a', ha'⟩ : ∃ a', a' = (e + 2) * (C₀ + 2) + 300 := ⟨_, rfl⟩
  refine ⟨a' + e + 3, e, by omega, fun Γ S Q _ _ _ _ _ _ mu => ?_⟩
  obtain ⟨c, hc⟩ : ∃ c, c = Fintype.card (Option Γ) := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; exact Fintype.card_pos
  obtain ⟨cb, hcb⟩ : ∃ cb : Option Γ → Fin c → Bool, Function.Injective cb := by
    refine ⟨fun z j => decide (Fin.cast hc.symm (Fintype.equivFin _ z) = j), fun z z' h => ?_⟩
    have := congrFun h (Fin.cast hc.symm (Fintype.equivFin _ z'))
    simp only [decide_true, decide_eq_true_eq] at this
    exact (Fintype.equivFin _).injective (Fin.ext (by simpa using congrArg Fin.val this))
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = Fintype.card S + 1 := ⟨_, rfl⟩
  obtain ⟨bY, hbY⟩ : ∃ b, b = (e + a' + 2) * C₀ + 2 * e + a' + 8 := ⟨_, rfl⟩
  obtain ⟨Ee, hEe⟩ : ∃ x, x = (e + 2) ^ C₀ := ⟨_, rfl⟩
  have hEe1 : 1 ≤ Ee := hEe ▸ Nat.one_le_pow _ _ (by omega)
  obtain ⟨W, hW⟩ : ∃ W, W = 18 * (C₀ + 1) * (4 * c + 5) * Ee := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = W + C₀ + (1 + C₀ + 2 ^ ee h * Ee) + 16 * bY + c + 8 + (4 * c + 4) := ⟨_, rfl⟩
  refine ⟨C, 8 * c + 2 * σ + 16, fun v hv => ?_⟩
  have hv1 : 1 ≤ v := by omega
  refine ⟨v ^ e, le_rfl, Nat.le_mul_of_pos_left _ (by omega), fun T k hT hk hk' => ?_⟩
  obtain ⟨K, hK⟩ : ∃ K, K = v ^ e := ⟨_, rfl⟩
  rw [← hK]
  have vp : ∀ {x y}, x ≤ y → v ^ x ≤ v ^ y := fun h => Nat.pow_le_pow_right hv1 h
  have hK0 : 0 < K := hK ▸ Nat.pow_pos hv1
  have hMv : K + K ≤ v ^ (e + 1) := by
    rw [pow_succ, ← hK]
    calc K + K = K * 2 := (Nat.mul_two K).symm
      _ ≤ K * v := Nat.mul_le_mul_left _ (by omega)
  obtain ⟨ub, hub⟩ : ∃ ub, ub = T / v ^ a' := ⟨_, rfl⟩
  obtain ⟨load, hload⟩ : ∃ l, l = 2 * ((T + (K + K) * σ) * c / ub + (K + K)) := ⟨_, rfl⟩
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := pieces_numbers (C₀ := C₀) (σ := σ) hc0 (by omega) hv (by omega) hMv ha'.ge hT
    hub hload
  have hload1 : 1 ≤ load := (Nat.le_add_left 1 _).trans b7
  obtain ⟨TT⟩ := htree A (K + K) (K + K) load ub (by omega) le_rfl hload1 b1
  have hk64 : k ≤ v ^ 300 := hk'.trans (vp (by norm_num))
  have hkM : k ≤ 4 * (K + K) := by
    have : v ^ 64 ≤ K := hK ▸ vp (by omega)
    omega
  have hγ : (1 / Real.logb 2 ((2 ^ ee h : ℕ) : ℝ)) = 1 / (ee h : ℝ) := by
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  have hnode : ∀ X : ℕ, (X : ℝ) ≤ (lg (K + K) ^ C₀ : ℕ) *
      ((K + K : ℕ) : ℝ) ^ (1 - 1 / Real.logb 2 ((2 ^ ee h : ℕ) : ℝ)) * (load + ((K + K : ℕ) : ℝ) ^ 2) →
      X * v ^ 300 ≤ yhat load (K + K) C₀ := by
    intro X hX
    rw [hγ] at hX
    refine pieces_gain hq (by omega) ?_ (R := load + (K + K) ^ 2) (by push_cast at hX ⊢; exact hX)
    rw [← pow_mul]
    exact (vp (show 300 * ee h ≤ e by omega)).trans (by omega)
  -- bits
  obtain ⟨L, hL⟩ : ∃ L, L = lg v := ⟨_, rfl⟩
  have hL2 : 2 ≤ L := hL ▸ lg_two (by omega)
  have hPL : lg (K + K) ^ C₀ ≤ Ee * L ^ C₀ := by
    rw [hEe, ← mul_pow]
    refine Nat.pow_le_pow_left ?_ _
    have h1 : K + K < 2 ^ ((e + 1) * L) := by
      calc K + K ≤ v ^ (e + 1) := hMv
        _ < (2 ^ L) ^ (e + 1) := Nat.pow_lt_pow_left (hL ▸ Nat.lt_pow_succ_log_self (by norm_num) v) (by omega)
        _ = 2 ^ ((e + 1) * L) := by rw [← pow_mul, Nat.mul_comm]
    have h2 : Nat.log 2 (K + K) < (e + 1) * L := Nat.log_lt_of_lt_pow (by omega) h1
    have e1 : (e + 2) * L = (e + 1) * L + L := by ring
    unfold lg
    omega
  have hWC : ∀ X, X ≤ W * L ^ C₀ * (K * T) → X ≤ K * T * lg v ^ C := fun X hX => by
    rw [← hL, Nat.mul_comm (K * T)]
    exact hX.trans (Nat.mul_le_mul_right _ (const_mul_pow_le hL2 (by omega)))
  have hYub : yhat load (K + K) C₀ * ub ≤ 2 * (4 * c + 5) * Ee * L ^ C₀ * (K * T) := by
    calc yhat load (K + K) C₀ * ub = lg (K + K) ^ C₀ * (K + K) * (load * ub + (K + K) ^ 2 * ub) := by unfold yhat; ring
      _ ≤ Ee * L ^ C₀ * (K + K) * ((4 * c + 4) * T + T) := by gcongr
      _ = _ := by ring
  have hKT : T ≤ K * T := Nat.le_mul_of_pos_left _ hK0
  have hL1 : 1 ≤ L ^ C₀ := Nat.one_le_pow _ _ (by omega)
  -- the program
  have hNc : Fintype.card TT.sys.N ≤ ((K + K) * load) ^ C₀ := by
    obtain ⟨-, -, -, -, -, -, -, -, -, d6, -⟩ := TT.computed
    exact (Fintype.card_le_of_injective (fun ν => (Uid.new ν ⟨0, TT.U1_pos⟩ : Uid (K + K) load TT.sys.N TT.U1))
      fun a b e => (Uid.new.inj e).1).trans d6
  have hMN : ((K + K) * load) ^ C₀ ≤ v ^ ((e + a' + 2) * C₀) := by
    rw [pow_mul]
    refine Nat.pow_le_pow_left ((Nat.mul_le_mul hMv b6).trans ?_) _
    rw [← pow_add]
    exact vp (by omega)
  have hdep : TT.depth ≤ Ee * L ^ C₀ := TT.depth_le.trans hPL
  have hdY : TT.depth ≤ v ^ bY := by
    refine TT.depth_le.trans (le_trans ?_ (hMN.trans (vp (by omega))))
    refine Nat.pow_le_pow_left ?_ _
    exact (Nat.succ_le_of_lt (Nat.log_lt_self 2 (by omega))).trans (Nat.le_mul_of_pos_right _ hload1)
  have hin : (K + K) * (K + K) + Fintype.card TT.sys.N ≤ v ^ bY := by
    have h1 : (K + K) * (K + K) ≤ v ^ (bY - 1) := by
      refine (Nat.mul_le_mul hMv hMv).trans ?_
      rw [← pow_add]
      exact vp (by omega)
    have h2 : Fintype.card TT.sys.N ≤ v ^ (bY - 1) := hNc.trans (hMN.trans (vp (by omega)))
    calc _ ≤ v ^ (bY - 1) * 2 := by omega
      _ ≤ v ^ (bY - 1) * v := Nat.mul_le_mul_left _ (by omega)
      _ = v ^ bY := by rw [← pow_succ]; congr 1; omega
  obtain ⟨g1, g2, g3, tab, htab⟩ := prop_pieces_program TT k (Y := v ^ bY)
    (le_trans (by omega) (Nat.le_self_pow (show bY ≠ 0 by omega) v)) (hMN.trans (vp (by omega)))
    (hMv.trans (vp (by omega))) (b6.trans (vp (by omega))) hdY hin
  refine ⟨{
    c := c
    cb := cb
    cb_inj := hcb
    c_le := by omega
    ub := ub
    ub_pos := b1
    U0 := load
    load := load
    unit_le := ⟨b2, ?_⟩
    A' := TT.A'
    E := TT.E
    U1 := TT.U1
    U1_pos := TT.U1_pos
    num := pieceNum TT k
    D := (v ^ bY) ^ 4
    steps := (v ^ bY) ^ 15
    sys := TT.sys
    plan := TT.plan
    cap := TT.cap
    ok := TT.ok
    isLaw := TT.isLaw
    relay_kind := fun x hx => by simpa [hx] using TT.kinds x
    good_iff := TT.good_iff
    poss_good := TT.poss_good
    grp := fun n o => pieceFin TT k n o
    tab := tab
    tab_valid := htab
    digits := ⟨g1, g2, g3, ?_⟩
    kinds_mem := fun r => ?_
    outcomes_le := hNc.trans (hMN.trans (vp (by omega)))
    num_le := ?_
    blocks_le := fun n o hn hg g => ?_
    cut_le := fun n o hn hg g => ?_
    all_le := fun n o hn hg g => ?_
    steps_le := ?_
    value := fun i e' u ℓ' hℓ hu => ?_ }⟩
  · rw [← hL, Nat.mul_comm T]
    refine b3.trans (Nat.mul_le_mul_right _ (le_trans (le_of_eq ?_) (const_mul_pow_le (e := 0) hL2 (show 4 * c + 4 + 0 ≤ C by omega))))
    simp
  · exact Nat.one_lt_pow (by norm_num) (Nat.one_lt_pow (by omega) (by omega))
  · have hk' : TT.sys.kind r.1 ∈ relay A :: (univ : Finset VL.Di).toList.map VL.L := by
      have h1 := TT.kinds r.1
      split_ifs at h1 with hl
      · obtain ⟨L', h2, h4⟩ := List.mem_map.1 h1
        rw [← h4]
        exact List.mem_cons_of_mem _ h2
      · rw [h1]
        exact List.mem_cons_self
    exact List.mem_flatMap.2 ⟨_, hk', List.mem_map.2 ⟨r.2, by simp, rfl⟩⟩
  · refine (min_le_left _ _).trans ?_
    rw [← hL]
    calc 1 + C₀ + 2 ^ ee h * (TT.depth * k) ≤ (1 + C₀) * (L ^ C₀ * k) + 2 ^ ee h * (Ee * L ^ C₀ * k) :=
          Nat.add_le_add (Nat.le_mul_of_pos_right _ (Nat.mul_pos hL1 (by omega)))
            (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hdep))
      _ = k * ((1 + C₀ + 2 ^ ee h * Ee) * L ^ C₀) := by ring
      _ ≤ k * L ^ C := Nat.mul_le_mul_left _ (const_mul_pow_le hL2 (by omega))
  · refine (piece_blocks hn hg hK0 le_rfl (by omega) hkM g).trans ?_
    calc 4 * (K + K) = 8 * K := by ring
      _ ≤ C * K := Nat.mul_le_mul_right _ (by omega)
  · refine hWC _ ?_
    have h1 := piece_cut hn hg hK0 le_rfl (by omega) hk64 hnode g
    calc _ = _ * v ^ 300 * ub := by ring
      _ ≤ (yhat load (K + K) C₀ + (K + K) ^ C₀ * v ^ 300) * ub := Nat.mul_le_mul_right _ h1
      _ = yhat load (K + K) C₀ * ub + (K + K) ^ C₀ * v ^ 300 * ub := by ring
      _ ≤ 2 * (4 * c + 5) * Ee * L ^ C₀ * (K * T) + 1 * L ^ C₀ * (K * T) :=
          Nat.add_le_add hYub (b5.trans (hKT.trans (Nat.le_mul_of_pos_left _ (by omega))))
      _ = (2 * (4 * c + 5) * Ee + 1) * L ^ C₀ * (K * T) := by ring
      _ ≤ _ := by
          refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
          rw [hW]
          nlinarith
  · refine hWC _ ?_
    have h1 := piece_all hn hg hK0 le_rfl (by omega) hk64 hnode hkM g
    have h2 : (K + K) ^ C₀ * k * ub ≤ T := (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk64)).trans b5
    calc _ = _ * k * ub := by ring
      _ ≤ (C₀ * (4 * yhat load (K + K) C₀) + 4 * (K + K) * (lg (K + K) ^ C₀ * load) + 2 * C₀ * (K + K) ^ C₀ * k) * ub :=
          Nat.mul_le_mul_right _ h1
      _ = 4 * C₀ * (yhat load (K + K) C₀ * ub) + 8 * K * lg (K + K) ^ C₀ * (load * ub) +
          2 * C₀ * ((K + K) ^ C₀ * k * ub) := by ring
      _ ≤ 4 * C₀ * (2 * (4 * c + 5) * Ee * L ^ C₀ * (K * T)) + 8 * K * (Ee * L ^ C₀) * ((4 * c + 4) * T) +
          2 * C₀ * (1 * L ^ C₀ * (K * T)) :=
          Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hYub) (Nat.mul_le_mul (Nat.mul_le_mul_left _ hPL) b3))
            (Nat.mul_le_mul_left _ (h2.trans (hKT.trans (Nat.le_mul_of_pos_left _ (by omega)))))
      _ = (8 * C₀ * (4 * c + 5) * Ee + 8 * (4 * c + 4) * Ee + 2 * C₀) * L ^ C₀ * (K * T) := by ring
      _ ≤ _ := by
          refine Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ ?_)
          rw [hW]
          nlinarith [Nat.zero_le (C₀ * c * Ee)]
  · obtain ⟨-, -, -, -, -, -, d3, d4, d5, -⟩ := TT.computed
    have hMY := hMN.trans (vp (show (e + a' + 2) * C₀ ≤ C by omega))
    refine ⟨?_, ?_, d3.trans hMY, d4.trans hMY, b6.trans (vp (by omega)), d5.trans hMY⟩
    · rw [← pow_mul]
      exact vp (by omega)
    · rw [← pow_mul]
      exact vp (by omega)
  · have hU : (T + (Fintype.card S + 1)) * c / ub + 1 ≤ load := by rwa [← hσ]
    obtain ⟨hr1, hr2⟩ := lem_runnet (U0 := load) (U1 := TT.U1) (A' := TT.A') mu cb hcb hc0 b1 hU TT.sys.np i e' u hℓ hu
    rw [hr1]
    refine Finset.sum_congr rfl fun q _ => if_congr Iff.rfl ?_ rfl
    refine Finset.sum_congr rfl fun ρ _ => if_congr Iff.rfl ?_ rfl
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : ∀ p, ∑ b, ((n p b).val + (n b p).val) ≤ load
    · rw [if_pos hn]
      exact prop_pieces_identity hn fun o => pieceFin TT k n o
    · rw [if_neg hn]
      push Not at hn
      obtain ⟨p, hp⟩ := hn
      unfold posVal
      refine Finset.sum_eq_zero fun y _ => ?_
      split_ifs
      swap
      · rfl
      refine Finset.prod_eq_zero (mem_univ p) ?_
      by_contra h0
      have := hr2 q (fun s => ρ s p) n p _ h0
      rw [← hσ, ← hload] at this
      exact absurd this (not_le.2 hp)

end Paper
