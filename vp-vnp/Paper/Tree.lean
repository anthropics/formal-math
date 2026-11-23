/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Tower
import Paper.Laws

/-!
# The paper, section "Networks are sums of thin trees": Theorem thm:tree

A network is given by numbers of units between pairs of nodes and, at every node, a table of the bits of the units at
it. The moves of the tower plan rewrite its value as a sum, over good outcomes, of values of networks on trees.
-/

set_option linter.unusedSectionVars false

namespace Paper

open Finset Nc Nc.G Nc.Tow Nc.Vp Unc
open Nc.Tower (U x NN ee JJ tower SL2 gen XX npair npair_sym)
open NS1 (lg)

/-- The units of a network with n a c units from a to c. -/
abbrev NetUnit {AA : ℕ} (n : Fin AA → Fin AA → ℕ) := Σ a c : Fin AA, Fin (n a c)

/-- A table of the node a, with values in R, of the contents of the units at a. -/
abbrev NodeTable (R : Type) {AA : ℕ} (n : Fin AA → Fin AA → ℕ) (ℓ : ℕ) (a : Fin AA) :=
  ({u : NetUnit n // u.1 = a ∨ u.2.1 = a} → Fin ℓ → Bool) → R

/-- The value of a network: the sum over all contents of the units of the product of the tables. -/
def netValue {R : Type} [CommRing R] {AA ℓ : ℕ} {n : Fin AA → Fin AA → ℕ} (tab : ∀ a, NodeTable R n ℓ a) : R :=
  ∑ w : NetUnit n → Fin ℓ → Bool, ∏ a, tab a fun u => w u.1

/-- A law over A is a law over every A-algebra. -/
noncomputable def lawMap {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) (L : G.Law A) : G.Law R where
  Ro := L.Ro
  Sl := L.Sl
  Cn := L.Cn
  I := L.I
  a := L.a
  b := L.b
  ab := L.ab
  c := L.c
  d := L.d
  cd := L.cd
  lam := L.lam
  lab := L.lab
  lab_inj := L.lab_inj
  len := L.len
  tab p i s y := f (L.tab p i s y)
  law X := @laws_over_algebras A _ L R _ f.toAlgebra X
  conn := L.conn

/-- The laws at the vertices of a tower, over an A-algebra. -/
noncomputable def flagMap {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {h b D J r : ℕ} {T : Tower h b D J r}
    (FL : FlagLaws A T) : FlagLaws R T where
  Di := FL.Di
  L d := lawMap f (FL.L d)
  ro := FL.ro
  cn := FL.cn
  ends := FL.ends
  lam_pos := FL.lam_pos
  nonempty := FL.nonempty
  a₁ := FL.a₁
  a₁_pos := FL.a₁_pos
  C₁ := FL.C₁
  C₁_nonneg := FL.C₁_nonneg
  G₁ := FL.G₁
  G₁_le := FL.G₁_le
  L1 := FL.L1
  L2 := FL.L2

theorem TCst_map {A R : Type} [CommRing A] [CommRing R] (f : A →+* R) {h b D J r : ℕ} {T : Tower h b D J r}
    {FL : FlagLaws A T} {laws : List (G.Law A)} {c p q : ℕ} {ρ : ℝ} (hC : TCst FL laws c ρ p q) :
    TCst (flagMap f FL) (laws.map (lawMap f)) c ρ p q where
  r_pos := hC.r_pos
  b_pos := hC.b_pos
  h_pos := hC.h_pos
  bD := hC.bD
  ρ_pos := hC.ρ_pos
  ρ_lt := hC.ρ_lt
  gain := hC.gain
  two := hC.two
  near := hC.near
  h_le := hC.h_le
  b_le := hC.b_le
  r_le := hC.r_le
  nr_le := hC.nr_le
  g_le := hC.g_le
  di_le := hC.di_le
  fl_le := hC.fl_le
  sl_le := hC.sl_le
  bot := hC.bot
  bot_pos := hC.bot_pos
  cst := hC.cst
  inv := hC.inv
  pq := hC.pq
  pow := hC.pow
  mem d := List.mem_map.2 ⟨_, hC.mem d, rfl⟩
  len L hL := by
    obtain ⟨L', h1, rfl⟩ := List.mem_map.1 hL
    exact ⟨⟨(hC.len L' h1).1.len_le⟩, (hC.len L' h1).2⟩

section Start

variable {R : Type} [CommRing R] {AA A' E N U1 ℓ : ℕ} {S : Sys R (AA + A') E} {n : Fin AA → Fin AA → Fin (N + 1)}

/-- The tables with which the moves start: every node of the network has its table, applied to the units at it, and
every other node the table 1. -/
noncomputable def startTab (S : Sys R (AA + A') E) (U1 : ℕ) (n : Fin AA → Fin AA → Fin (N + 1))
    (tab : ∀ a, NodeTable R (fun a c => (n a c).1) ℓ a) : Fin (AA + A') → (Uid AA N S.N U1 → UW ℓ) → R :=
  Fin.addCases (motive := fun _ => (Uid AA N S.N U1 → UW ℓ) → R)
    (fun a y => if ∀ u : {u : NetUnit (fun a c => (n a c).1) // u.1 = a ∨ u.2.1 = a},
        y (.init u.1.1 u.1.2.1 (Fin.castLE (Nat.le_of_lt_succ (n u.1.1 u.1.2.1).2) u.1.2.2)) ≠ none then
        tab a fun u => (y (.init u.1.1 u.1.2.1 (Fin.castLE (Nat.le_of_lt_succ (n u.1.1 u.1.2.1).2) u.1.2.2))).getD
          fun _ => false
      else 0)
    (fun _ _ => 1)

theorem startTab_congr (tab : ∀ a, NodeTable R (fun a c => (n a c).1) ℓ a) (p : Fin (AA + A'))
    {y y' : Uid AA N S.N U1 → UW ℓ} (h : ∀ b c k, y (.init b c k) = y' (.init b c k)) :
    startTab S U1 n tab p y = startTab S U1 n tab p y' := by
  refine Fin.addCases (fun a => ?_) (fun e => ?_) p
  · simp only [startTab, Fin.addCases_left, h]
  · simp only [startTab, Fin.addCases_right]

theorem startTab_ne_none (tab : ∀ a, NodeTable R (fun a c => (n a c).1) ℓ a) (p : Fin (AA + A'))
    (y : Uid AA N S.N U1 → UW ℓ) (h : startTab S U1 n tab p y ≠ 0) :
    ∀ id ∈ seen0 (N := S.N) (U1 := U1) n, Holds (hold0 S.np) (hold1 S.np) p id → y id ≠ none := by
  intro id hid hh
  rcases id with ⟨b, c, k⟩ | ⟨ν, k⟩
  swap
  · simp [seen0] at hid
  have hk : k.1 < (n b c).1 := by simpa [seen0] using hid
  revert h hh
  refine Fin.addCases (fun a => ?_) (fun e => ?_) p
  · intro h hh
    simp only [startTab, Fin.addCases_left] at h
    split_ifs at h with hc
    swap
    · exact absurd rfl h
    have ha : b = a ∨ c = a := by
      rcases hh with hh | hh
      · exact Or.inl (Fin.castAdd_injective _ _ hh).symm
      · exact Or.inr (Fin.castAdd_injective _ _ hh).symm
    exact hc ⟨⟨b, c, ⟨k.1, hk⟩⟩, ha⟩
  · intro h hh
    rcases hh with hh | hh <;> exact absurd (congrArg Fin.val hh) (by simp [hold0, hold1, cparty]; omega)

open Classical in
/-- The position with which the moves start has the value of the network. -/
theorem posVal_start (tab : ∀ a, NodeTable R (fun a c => (n a c).1) ℓ a) :
    posVal (hold0 S.np) (hold1 S.np) (none : UW ℓ) (seen0 (N := S.N) (U1 := U1) n) (seen0 n)
      (fun y => ∏ p, startTab S U1 n tab p (y p)) = netValue tab := by
  have e0 : posVal (hold0 S.np) (hold1 S.np) (none : UW ℓ) (seen0 (N := S.N) (U1 := U1) n) (seen0 n)
      (fun y => ∏ p, startTab S U1 n tab p (y p)) = ∑ z ∈ Common (none : UW ℓ) (seen0 (N := S.N) (U1 := U1) n),
        ∏ p, startTab S U1 n tab p (ext (hold0 S.np) (hold1 S.np) (seen0 n) (fun _ _ => none) z p) := by
    have h1 := sum_contents_union (hold0 S.np) (hold1 S.np) (none : UW ℓ) ∅ (seen0 (N := S.N) (U1 := U1) n)
      (disjoint_empty_left _) (fun y => ∏ p, startTab S U1 n tab p (y p))
    rw [empty_union] at h1
    rw [posVal, h1]
    have h2 : Contents (hold0 S.np) (hold1 S.np) (none : UW ℓ) (∅ : Finset (Uid AA N S.N U1)) = {fun _ _ => none} := by
      ext y
      simp [Contents, funext_iff]
    rw [h2, Finset.sum_singleton]
  rw [e0]
  have hne : ∀ z, (∏ p, startTab S U1 n tab p (ext (hold0 S.np) (hold1 S.np) (seen0 n) (fun _ _ => none) z p)) ≠ 0 →
      ∀ id ∈ seen0 (N := S.N) (U1 := U1) n, z id ≠ none := by
    intro z hz id hid
    have h1 : startTab S U1 n tab (hold0 S.np id) (ext (hold0 S.np) (hold1 S.np) (seen0 n) (fun _ _ => none) z
        (hold0 S.np id)) ≠ 0 := fun h => hz (Finset.prod_eq_zero (mem_univ _) h)
    have h2 := startTab_ne_none tab _ _ h1 id hid (Or.inl rfl)
    rwa [ext_self hid (Or.inl rfl)] at h2
  let un : NetUnit (fun a c => (n a c).1) → Uid AA N S.N U1 := fun u =>
    .init u.1 u.2.1 (Fin.castLE (Nat.le_of_lt_succ (n u.1 u.2.1).2) u.2.2)
  have hun : ∀ u, un u ∈ seen0 (N := S.N) (U1 := U1) n := fun u => by
    simp [un, seen0]
  let W : (NetUnit (fun a c => (n a c).1) → Fin ℓ → Bool) → Uid AA N S.N U1 → UW ℓ := fun w id => match id with
    | .init a c k => if hk : k.1 < (n a c).1 then some (w ⟨a, c, ⟨k.1, hk⟩⟩) else none
    | .new _ _ => none
  have hW : ∀ w u, W w (un u) = some (w u) := by
    rintro w ⟨a, c, k⟩
    simp [W, un]
  rw [← Finset.sum_filter_of_ne (p := fun z => ∀ id ∈ seen0 (N := S.N) (U1 := U1) n, z id ≠ none) fun z _ hz => hne z hz]
  symm
  unfold netValue
  refine Finset.sum_bij' (fun w _ => W w) (fun z _ u => (z (un u)).getD fun _ => false) ?_ ?_ ?_ ?_ ?_
  · intro w _
    simp only [Finset.mem_filter, mem_common_iff]
    constructor
    · intro id hid
      rcases id with ⟨a, c, k⟩ | ⟨ν, k⟩
      · simp only [W]
        rw [dif_neg]
        simpa [seen0] using hid
      · rfl
    · intro id hid
      rcases id with ⟨a, c, k⟩ | ⟨ν, k⟩
      · simp only [W]
        rw [dif_pos (by simpa [seen0] using hid)]
        exact Option.some_ne_none _
      · simp [seen0] at hid
  · intro z _
    exact mem_univ _
  · intro w _
    funext u
    simp [hW]
  · intro z hz
    simp only [Finset.mem_filter, mem_common_iff] at hz
    funext id
    rcases id with ⟨a, c, k⟩ | ⟨ν, k⟩
    · simp only [W]
      split_ifs with hk
      · have h1 := hz.2 (.init a c k) (by simp [seen0, hk])
        have e : un ⟨a, c, ⟨k.1, hk⟩⟩ = .init a c k := rfl
        rw [e]
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h1
        rw [hv]
        rfl
      · exact (hz.1 _ (by simp [seen0, hk])).symm
    · exact (hz.1 _ (by simp [seen0])).symm
  · intro w _
    rw [Fin.prod_univ_add]
    have e2 : ∀ e : Fin A', startTab S U1 n tab (Fin.natAdd AA e)
        (ext (hold0 S.np) (hold1 S.np) (seen0 n) (fun _ _ => none) (W w) (Fin.natAdd AA e)) = 1 := fun e => by
      simp only [startTab, Fin.addCases_right]
    rw [Finset.prod_congr rfl (fun e _ => e2 e), Finset.prod_const_one, mul_one]
    refine Finset.prod_congr rfl fun a _ => ?_
    have e3 : ∀ u : {u : NetUnit (fun a c => (n a c).1) // u.1 = a ∨ u.2.1 = a},
        ext (hold0 S.np) (hold1 S.np) (seen0 n) (fun _ _ => none) (W w) (Fin.castAdd A' a) (un u.1) = some (w u.1) := by
      rintro ⟨u, hu⟩
      rw [ext_self (hun u), hW]
      rcases hu with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    simp only [startTab, Fin.addCases_left, un] at e3 ⊢
    simp [e3]

end Start

open Classical in
/-- The networks on trees of Theorem thm:tree, for networks on AA nodes with units of ℓ bits, at most N units at a
node and at most M nodes, over R, with the exponent C, the gain γ and the integer G₁ of the test for good outcomes.
The nodes are the parties 0, ..., AA + A' − 1. For numbers n of units and outcomes o the units of the tree are those
that are current at the end, plan.cur. A unit from a node to itself is allowed; it stays at its node, whose value sums
over it. -/
structure ThinTrees (R : Type) [CommRing R] (laws : List (G.Law R)) (AA N ℓ M b G₁ C : ℕ) (γ : ℝ) where
  /-- the number of further nodes -/
  A' : ℕ
  /-- the number of moves -/
  E : ℕ
  /-- a bound for outcomes -/
  U1 : ℕ
  U1_pos : 0 < U1
  /-- the moves -/
  sys : Sys R (AA + A') E
  /-- the units given in the moves, their numbers, and the good outcomes -/
  plan : Plan sys N U1
  /-- a bound for the units of one move -/
  cap : ℕ
  /-- the plan is causal and gives only current units between the ends of their slots -/
  ok : plan.Ok cap
  /-- the stage of a node -/
  stage : Fin (AA + A') → ℕ
  /-- the depth of the tree -/
  depth : ℕ
  /-- the root -/
  root : Fin (AA + A')
  /-- the parent of a node -/
  par : (Fin AA → Fin AA → Fin (N + 1)) → (sys.N → Fin U1) → Fin (AA + A') → Fin (AA + A')
  /-- the number of units between a node and its parent, as the program bounds it: the load at the node -/
  up : (Fin AA → Fin AA → Fin (N + 1)) → (sys.N → Fin U1) → Fin (AA + A') → ℕ
  /-- the dead units -/
  dead : (sys.N → Fin U1) → Finset (Uid AA N sys.N U1)
  /-- is the move a law move? -/
  isLaw : Fin E → Bool
  depth_le : depth ≤ lg M ^ C
  stage_le : ∀ p, stage p ≤ depth
  stage_given : ∀ a, stage (Fin.castAdd A' a) = 0
  stage_root : ∀ p, stage p = depth ↔ p = root
  stage_par : ∀ n o p, p ≠ root → stage (par n o p) = stage p + 1
  children_le : ∀ n o q, q ≠ root → (univ.filter fun p => p ≠ root ∧ par n o p = q).card ≤ b
  root_children_le : ∀ n o, (univ.filter fun p => p ≠ root ∧ par n o p = root).card ≤ C
  dead_le : ∀ o, (dead o).card ≤ M ^ C
  kinds : ∀ x, if isLaw x then sys.kind x ∈ laws else sys.kind x = relay R
  law_stage : ∀ r : sys.R, isLaw r.1 = true → 0 < stage (sys.rp r)
  /-- what good means -/
  good_iff : ∀ n o x, plan.good n o x ↔ if isLaw x then
      b * ∑ ν : (sys.kind x).Cn, (o ⟨x, ν⟩).val ^ 2 ≤ G₁ * plan.num n o x ^ 2 ∧
        ∀ ν : (sys.kind x).Cn, plan.num n o x ≤ o ⟨x, ν⟩
    else ∀ ν : (sys.kind x).Cn, (o ⟨x, ν⟩).val = plan.num n o x
  /-- every possible outcome is good -/
  poss_good : ∀ n o x, plan.Poss n o ℓ x → plan.good n o x
  edge : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) →
    ∀ u ∈ cutUnits (hold0 sys.np) (hold1 sys.np) id (plan.cur n o E \ dead o),
      ∃ p, p ≠ root ∧ s(hold0 sys.np u, hold1 sys.np u) = s(p, par n o p)
  node_le : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) →
    ∀ p, (((cutUnits (hold0 sys.np) (hold1 sys.np) id (plan.cur n o E \ dead o)).filter
        (Holds (hold0 sys.np) (hold1 sys.np) p)).card : ℝ) ≤
      (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - γ) * (N + (M : ℝ) ^ 2)
  total_le : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) →
    (cutUnits (hold0 sys.np) (hold1 sys.np) id (plan.cur n o E \ dead o)).card ≤ lg M ^ C * M * (N + M ^ 2)
  between_le : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) → ∀ p, p ≠ root →
    ((cutUnits (hold0 sys.np) (hold1 sys.np) id (plan.cur n o E \ dead o)).filter
      (fun u => s(hold0 sys.np u, hold1 sys.np u) = s(p, par n o p))).card ≤ up n o p
  up_node : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) →
    ∀ p, ((up n o p + ∑ q ∈ univ.filter (fun q => q ≠ root ∧ par n o q = p), up n o q : ℕ) : ℝ) ≤
      (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - γ) * (N + (M : ℝ) ^ 2)
  up_total : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) →
    ∑ p, up n o p ≤ lg M ^ C * M * (N + M ^ 2)
  layers_le : ∀ n o, (∀ x, plan.good n o x) → ∀ p,
    ∑ r ∈ univ.filter (fun r : sys.R => sys.rp r = p ∧ isLaw r.1 = true), plan.num n o r.1 ≤
      ((Plan.seenAt n o E).filter (Holds (hold0 sys.np) (hold1 sys.np) p)).card
  /-- copies: what a node ever holds, with the zeros in slots and the counts of the moves, against the units that it
  has in the end -/
  copies_le : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) → ∀ o, (∀ x, plan.good n o x) → ∀ p,
    ((Plan.seenAt n o E).filter (Holds (hold0 sys.np) (hold1 sys.np) p)).card +
        ∑ r ∈ univ.filter (fun r : sys.R => sys.rp r = p),
          (1 + Fintype.card ((sys.kind r.1).SlAt r.2)) * plan.num n o r.1 ≤
      C * (up n o p + ∑ q ∈ univ.filter (fun q => q ≠ root ∧ par n o q = p), up n o q) +
        (if (p : ℕ) < AA then lg M ^ C * N else 0) +
        C * ((dead o).filter (Holds (hold0 sys.np) (hold1 sys.np) p)).card
  value : ∀ n, (∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) →
    ∀ tab : ∀ a, NodeTable R (fun a c => (n a c).1) ℓ a,
      netValue tab = ∑ o : sys.N → Fin U1, if ∀ x, plan.good n o x then
        ∑ w ∈ Common (none : UW ℓ) (cutUnits (hold0 sys.np) (hold1 sys.np) id (plan.cur n o E)), ∏ p,
          groupVal (hold0 sys.np) (hold1 sys.np) none (Plan.seenAt n o E) (plan.cur n o E) id
            (fun a => partyTab plan n o (startTab sys U1 n tab a) a) p w
        else 0
  computed : ∃ (D steps : ℕ) (inp : (Fin AA × Fin AA) ⊕ sys.N → (Fin AA → Fin AA → Fin (N + 1)) × (sys.N → Fin U1) → Fin D)
      (H : Set ((Fin AA → Fin AA → Fin (N + 1)) × (sys.N → Fin U1) → ℕ)),
    D ≤ (M * N) ^ C ∧ steps ≤ (M * N) ^ C ∧ AA + A' ≤ (M * N) ^ C ∧ E ≤ (M * N) ^ C ∧ U1 ≤ (M * N) ^ C ∧
    Fintype.card (Uid AA N sys.N U1) ≤ (M * N) ^ C ∧
    (∀ a c x, (inp (.inl (a, c)) x : ℕ) = x.1 a c) ∧ (∀ ν x, (inp (.inr ν) x : ℕ) = x.2 ν) ∧ SlpN inp steps H ∧
    (∀ p q, (ind fun x => par x.1 x.2 p = q) ∈ H) ∧ (∀ u, (ind fun x => u ∈ plan.cur x.1 x.2 E) ∈ H) ∧
    (∀ z u, (ind fun x => u ∈ plan.cons x.1 x.2 z) ∈ H) ∧ (∀ y, (fun x => plan.num x.1 x.2 y) ∈ H) ∧
    (∀ p, (fun x => up x.1 x.2 p) ∈ H) ∧ ∀ y, (ind fun x => plan.good x.1 x.2 y) ∈ H

/-- The integer of the test for good outcomes: "the test for good outcomes compare[s] integers, as C₀ is an integer". -/
noncomputable def goodBound (C₁ : ℝ) (a₁ : ℕ) : ℕ := ⌊2 * C₁ * (a₁ : ℝ) ^ 2⌋₊

/-- Without units from a node to itself every current unit joins two nodes: thin trees give the printed formula. -/
theorem cutUnits_id_cur {R : Type} [CommRing R] {AA A' E N U1 : ℕ} {S : Sys R (AA + A') E} (P : Plan S N U1)
    {n : Fin AA → Fin AA → Fin (N + 1)} (hn : ∀ a, n a a = 0) (o : S.N → Fin U1) :
    cutUnits (hold0 S.np) (hold1 S.np) id (P.cur n o E) = P.cur n o E := by
  unfold cutUnits
  rw [filter_true_of_mem]
  intro u hu he
  have hseen := (Plan.mem_cur.1 hu).1
  cases u with
  | init a b k =>
    have hk := Plan.init_mem_seenAt.1 hseen
    have hab : a = b := Fin.castAdd_injective _ _ he
    subst hab
    rw [hn a] at hk
    exact Nat.not_lt_zero _ hk
  | new ν k => exact (S.kind ν.1).cd ν.2 (S.inj ν.1 he)

/-- **Paper: the paragraph before Theorem thm:tree.** "An outcome is good if ‖o‖_* ≤ √C₁a₁t and o_e ≥ t for all e":
at a law move the integer test of the trees of thm_tree implies this, and is equivalent to it when 2C₁a₁² is an
integer, as it is for C₁ = 4C₀ with the integer C₀ of the laws. -/
theorem thm_tree_good {R : Type} [CommRing R] {laws : List (G.Law R)} {AA N ℓ M b C a₁ : ℕ} {γ C₁ : ℝ}
    (T : ThinTrees R laws AA N ℓ M b (goodBound C₁ a₁) C γ) (hC : 0 ≤ C₁) {n o x} (hlaw : T.isLaw x = true) :
    let printed := √((b : ℝ) / 2 * ∑ ν : (T.sys.kind x).Cn, ((o ⟨x, ν⟩).val : ℝ) ^ 2) ≤ √C₁ * a₁ * T.plan.num n o x ∧
      ∀ ν : (T.sys.kind x).Cn, T.plan.num n o x ≤ o ⟨x, ν⟩
    (T.plan.good n o x → printed) ∧
      ((∃ g : ℕ, 2 * C₁ * (a₁ : ℝ) ^ 2 = g) → printed → T.plan.good n o x) := by
  intro printed
  have h3 : 0 ≤ √C₁ * (a₁ : ℝ) * (T.plan.num n o x : ℝ) := by positivity
  have e : printed ↔ (b : ℝ) * ∑ ν : (T.sys.kind x).Cn, ((o ⟨x, ν⟩).val : ℝ) ^ 2 ≤
      2 * C₁ * (a₁ : ℝ) ^ 2 * (T.plan.num n o x : ℝ) ^ 2 ∧ ∀ ν : (T.sys.kind x).Cn, T.plan.num n o x ≤ o ⟨x, ν⟩ := by
    refine and_congr_left fun _ => ?_
    rw [Real.sqrt_le_left h3, mul_pow, mul_pow, Real.sq_sqrt hC]
    constructor <;> intro h <;> linarith
  rw [e, T.good_iff n o x, if_pos hlaw]
  refine ⟨fun h => ⟨?_, h.2⟩, fun ⟨g, hg⟩ h => ⟨?_, h.2⟩⟩
  · have h2 : (b : ℝ) * ∑ ν : (T.sys.kind x).Cn, ((o ⟨x, ν⟩).val : ℝ) ^ 2 ≤
        goodBound C₁ a₁ * (T.plan.num n o x : ℝ) ^ 2 := by exact_mod_cast h.1
    exact h2.trans (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (sq_nonneg _))
  · have h2 := h.1
    rw [hg] at h2
    have h4 : goodBound C₁ a₁ = g := by rw [goodBound, hg, Nat.floor_natCast]
    calc b * ∑ ν : (T.sys.kind x).Cn, (o ⟨x, ν⟩).val ^ 2 ≤ g * T.plan.num n o x ^ 2 := by exact_mod_cast h2
      _ = _ := by simp only [h4]

section Build

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' N U1 : ℕ} {T : Tower h b D J r} (R : Routes T m Uu)
  {ch : Fin AA ↪ T.X 0} (FL : FlagLaws F T) (Pl : Place T ch A') {ρ : ℝ} {lhat : ℕ}

/-- The stage of a node of the tree. -/
def ndStage : Nd T → ℕ
  | none => J + 1
  | some s => s.1.1

/-- The parent of a node of the tree. -/
noncomputable def ndPar (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) : Nd T → Nd T
  | none => none
  | some s => parN hh Lf s.1.1 s.2

theorem ndStage_par (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) {ν : Nd T} (hν : ν ≠ none) :
    ndStage (ndPar hh Lf ν) = ndStage ν + 1 := by
  rcases ν with _ | ⟨j, c⟩
  · exact absurd rfl hν
  · show ndStage (parN hh Lf j.1 c) = j.1 + 1
    unfold parN
    split_ifs with hj
    · rfl
    · have := j.2
      show J + 1 = j.1 + 1
      omega

theorem card_ndChildren (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) [DecidableEq (Nd T)] {ν : Nd T} (hν : ν ≠ none) :
    (univ.filter fun μ : Nd T => μ ≠ none ∧ ndPar hh Lf μ = ν).card ≤ b := by
  rcases nd_cases ν with rfl | ⟨i, hi, c', rfl⟩
  · exact absurd rfl hν
  rcases i with _ | j
  · refine le_of_eq_of_le (card_eq_zero.2 (filter_false_of_mem fun μ _ hμ => ?_)) (Nat.zero_le _)
    have := ndStage_par hh Lf hμ.1
    rw [hμ.2] at this
    exact absurd this.symm (Nat.succ_ne_zero _)
  · refine le_trans ?_ (card_children (hh := hh) (Lf := Lf) (j := j) (by omega) c')
    refine le_trans (card_le_card ?_) (card_image_le (f := fun c : T.X j => nd T j (by omega) c))
    intro μ hμ
    obtain ⟨-, hμ1, hμ2⟩ := mem_filter.1 hμ
    have hs := ndStage_par hh Lf hμ1
    rw [hμ2] at hs
    rcases nd_cases μ with rfl | ⟨i, hi', c, rfl⟩
    · exact absurd rfl hμ1
    have e : i = j := by
      simp only [ndStage, nd] at hs
      omega
    subst e
    refine mem_image.2 ⟨c, mem_filter.2 ⟨mem_univ _, ?_⟩, rfl⟩
    have h2 : parN hh Lf i c = nd T (i + 1) hi c' := hμ2
    unfold parN at h2
    rw [dif_pos hi, nd_inj] at h2
    exact h2

theorem card_ndRoot (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) [DecidableEq (Nd T)] :
    (univ.filter fun μ : Nd T => μ ≠ none ∧ ndPar hh Lf μ = none).card ≤ Fintype.card (T.X J) := by
  rw [← card_univ (α := T.X J)]
  refine le_trans (card_le_card ?_) (card_image_le (f := fun c : T.X J => nd T J le_rfl c))
  intro μ hμ
  obtain ⟨-, hμ1, hμ2⟩ := mem_filter.1 hμ
  rcases nd_cases μ with rfl | ⟨i, hi', c, rfl⟩
  · exact absurd rfl hμ1
  have h2 : parN hh Lf i c = none := hμ2
  unfold parN at h2
  split_ifs at h2 with hi
  · exact absurd h2 nd_ne_none
  · have e : i = J := by omega
    subst e
    exact mem_image.2 ⟨c, mem_univ _, rfl⟩

theorem ndStage_eq_top {ν : Nd T} : ndStage ν = J + 1 ↔ ν = none := by
  rcases ν with _ | ⟨j, c⟩
  · simp [ndStage]
  · have := j.2
    simp [ndStage]
    omega

/-- The parent of a party. -/
noncomputable def treePar (hh : 0 < h) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1)
    (p : Fin (AA + A')) : Fin (AA + A') :=
  Pl.pt (ndPar hh (lev (load R ch FL N (nn n) (oo R FL Pl o))) (Pl.pt.symm p))

/-- The load at a party: the number of units between it and its parent. -/
noncomputable def treeUp (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1) (p : Fin (AA + A')) : ℕ :=
  onN (fb (lev (load R ch FL N (nn n) (oo R FL Pl o)))) 0 (Pl.pt.symm p)

variable {R FL Pl}

theorem valid_of (n : Fin AA → Fin AA → Fin (N + 1)) (h : ∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) : Valid N (nn n) := by
  intro a
  refine le_trans (Finset.sum_le_sum fun c _ => ?_) (h a)
  split_ifs
  · exact Nat.zero_le _
  · exact le_rfl

/-- Every unit of the end is dead or lies between a chamber and its parent. -/
theorem cur_tree (hH : THypR FL ρ) {n : Fin AA → Fin AA → Fin (N + 1)}
    (hv : Valid N (nn n)) {o : (sys R FL Pl).N → Fin U1} (hg : ∀ x, (plan R FL Pl N N U1).good n o x)
    {u : Un R FL Pl N U1} (hu : u ∈ (plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL)))
    (hd : u ∉ deadU R FL Pl N o) (hloop : hold0 (sys R FL Pl).np u ≠ hold1 (sys R FL Pl).np u) :
    ∃ s : Σ j : Fin (J + 1), T.X j, u ∈ AsU R FL Pl N n o s ∧
      s(hold0 (sys R FL Pl).np u, hold1 (sys R FL Pl).np u) =
        s(Pl.pt (some s), treePar R FL Pl hH.h_pos n o (Pl.pt (some s))) := by
  classical
  have hr := hH.r_pos
  have hb := hH.b_pos
  have hh := hH.h_pos
  have hp : ∀ mv, GoodMv R ch FL N (nn n) (oo R FL Pl o) mv := fun mv => by
    have h1 : GoodMv R ch FL N (nn n) (oo R FL Pl o) (eE R FL ((eE R FL).symm mv)) := hg ((eE R FL).symm mv)
    rwa [Equiv.apply_symm_apply] at h1
  obtain ⟨hseen, hal⟩ := cur_end hr hb hh hu
  cases u with
  | init a c kk =>
    exfalso
    have hkn := mem_seen_init.1 hseen
    have hdone : tgB T R ch a c kk = .done := hal ⟨hv, hkn⟩
    have hne : a ≠ c := fun e => by
      subst e
      exact hloop rfl
    unfold tgB at hdone
    rw [if_neg hne] at hdone
    split_ifs at hdone with hs
    exact (edgeO_hold (R := R) (ch := ch) (AA := AA) (m := m) (c := ch a) (c' := ch c) (γ := gam T ch a kk) (s := 0)
      (R.pl_pos (fun e => hne (ch.injective e)) _)).1 hdone
  | new ν kk =>
    have hko := mem_seen_new.1 hseen
    have halv : alv R ch FL N (nn n) (oo R FL Pl o) (eN R FL Pl ν) = (o ν).1 := by
      rw [alv_good _ (hp _)]
      unfold oo
      rw [Equiv.symm_apply_apply]
    have hlt : kk.1 < (o ν).1 := by
      by_contra hge
      refine hd (mem_image.2 ⟨ν, mem_univ _, ?_⟩)
      rw [Fin.le_def] at hko
      have e : kk = o ν := Fin.ext (by omega)
      rw [e]
    have hA : AlU R FL Pl N n o (Uid.new ν kk : Un R FL Pl N U1) := by
      change kk.1 < alv R ch FL N (nn n) (oo R FL Pl o) (eN R FL Pl ν)
      rw [halv]
      exact hlt
    have hdone : tgM R ch FL (eN R FL Pl ν).1 (eN R FL Pl ν).2 = .done := hal hA
    have e0 : hold0 (sys R FL Pl).np (Uid.new ν kk : Un R FL Pl N U1) =
        Pl.pt (partM R ch FL (eN R FL Pl ν).1 ((kindM R ch FL (eN R FL Pl ν).1).cnEnd (eN R FL Pl ν).2 false)) :=
      np_eq R FL Pl ν false
    have e1 : hold1 (sys R FL Pl).np (Uid.new ν kk : Un R FL Pl N U1) =
        Pl.pt (partM R ch FL (eN R FL Pl ν).1 ((kindM R ch FL (eN R FL Pl ν).1).cnEnd (eN R FL Pl ν).2 true)) :=
      np_eq R FL Pl ν true
    rw [e0, e1]
    have hmem : ∀ s, IsCh R ch FL (eN R FL Pl ν) s → (Uid.new ν kk : Un R FL Pl N U1) ∈ AsU R FL Pl N n o s :=
      fun s hs => mem_AsU_new.2 ⟨hA, hs⟩
    have hal' : alv R ch FL N (nn n) (oo R FL Pl o) (eN R FL Pl ν) ≠ 0 := by omega
    revert hdone hal' hmem
    generalize eN R FL Pl ν = w
    intro hdone hmem hal'
    rcases w with ⟨⟨x, hx⟩ | l, β⟩
    · have hnum : num R ch FL N (nn n) (oo R FL Pl o) (.inl ⟨x, hx⟩) ≠ 0 := by
        have := alv_le_num (lhat := N) (n := nn n) (o := oo R FL Pl o) (FL := FL) hr hb ⟨x, hx⟩ β
        omega
      obtain ⟨j, hj, c, h1, h2⟩ := done_hold hr hb hh hx (β := β) hdone hnum
      refine ⟨⟨⟨j, Nat.lt_succ_of_le hj⟩, c⟩, hmem _ ⟨⟨x, hx⟩, β, rfl, hdone, h1⟩, ?_⟩
      have h3 : s(partM R ch FL (.inl ⟨x, hx⟩) ((kindM R ch FL (.inl ⟨x, hx⟩)).cnEnd β false),
          partM R ch FL (.inl ⟨x, hx⟩) ((kindM R ch FL (.inl ⟨x, hx⟩)).cnEnd β true)) =
          s(nd T j hj c, parN hh (lev (load R ch FL N (nn n) (oo R FL Pl o))) j c) := h2
      have h4 := congrArg (Sym2.map Pl.pt) h3
      simp only [Sym2.map_mk] at h4
      rw [h4, treePar, Equiv.symm_apply_apply]
      rfl
    · simp [tgM] at hdone

/-- The law moves at a node have no more layers than the node has units. -/
theorem layers_le_seen (hH : THypR FL ρ) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1)
    (hg : ∀ x, (plan R FL Pl N N U1).good n o x) (p : Fin (AA + A')) :
    ∑ r' ∈ univ.filter (fun r' : (sys R FL Pl).R => (sys R FL Pl).rp r' = p ∧ (eE R FL r'.1).isRight = true),
      (plan R FL Pl N N U1).num n o r'.1 ≤
    ((Plan.seenAt n o (Fintype.card (Mv T R ch FL))).filter
      (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) p)).card := by
  classical
  have key : ∀ r' ∈ univ.filter (fun r' : (sys R FL Pl).R => (sys R FL Pl).rp r' = p ∧ (eE R FL r'.1).isRight = true),
      ∃ ν : (sys R FL Pl).N, ν.1 = r'.1 ∧ (∃ d, (sys R FL Pl).np ν d = p) ∧
        (plan R FL Pl N N U1).num n o r'.1 ≤ (o ν).1 := by
    rintro ⟨x, ro⟩ hr'
    obtain ⟨-, hrp, hlaw⟩ := mem_filter.1 hr'
    have hch : ∀ mv : Mv T R ch FL, mv.isRight = true → ∀ ro : (kindM R ch FL mv).Ro,
        GoodMv R ch FL N (nn n) (oo R FL Pl o) mv →
        ∃ ν : (kindM R ch FL mv).Cn, (∃ d, (kindM R ch FL mv).cnEnd ν d = ro) ∧
          num R ch FL N (nn n) (oo R FL Pl o) mv ≤ oo R FL Pl o ⟨mv, ν⟩ := by
      rintro (y | l) hl ro hgood
      · simp at hl
      obtain ⟨ν, hν⟩ := hH.near (FL.ro l.2.2.2 ro)
      refine ⟨(FL.cn l.2.2.2).symm ν, ?_, hgood.2 _⟩
      have h1 := FL.ends l.2.2.2 ((FL.cn l.2.2.2).symm ν)
      rw [Equiv.apply_symm_apply] at h1
      have h2 : FL.ro l.2.2.2 ro ∈ s(T.cN ν, T.dN ν) := by
        rcases hν with hν | hν <;> simp [hν]
      rw [← h1, Sym2.mem_iff] at h2
      rcases h2 with h2 | h2
      · exact ⟨false, ((FL.ro l.2.2.2).injective h2).symm⟩
      · exact ⟨true, ((FL.ro l.2.2.2).injective h2).symm⟩
    obtain ⟨ν, ⟨d, hd⟩, hle⟩ := hch (eE R FL x) hlaw ro (hg x)
    refine ⟨⟨x, ν⟩, rfl, ⟨d, ?_⟩, ?_⟩
    · rw [← hrp]
      exact congrArg (fun z => (sys R FL Pl).rp ⟨x, z⟩) hd
    · have e : (eN R FL Pl).symm ⟨eE R FL x, ν⟩ = ⟨x, ν⟩ := by
        rw [Equiv.symm_apply_eq]
        rfl
      unfold oo at hle
      rw [e] at hle
      exact hle
  choose ν hν1 hν2 hν3 using key
  let Fr : ∀ r' ∈ univ.filter (fun r' : (sys R FL Pl).R => (sys R FL Pl).rp r' = p ∧ (eE R FL r'.1).isRight = true),
      Finset (Un R FL Pl N U1) := fun r' hr' =>
    (univ.filter fun k : Fin U1 => k.1 < (plan R FL Pl N N U1).num n o r'.1).image (Uid.new (ν r' hr'))
  rw [← Finset.sum_attach]
  calc _ = ∑ q ∈ (univ.filter fun r' : (sys R FL Pl).R =>
        (sys R FL Pl).rp r' = p ∧ (eE R FL r'.1).isRight = true).attach, (Fr q.1 q.2).card := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [card_image_of_injective _ (fun k k' e => (Uid.new.inj e).2), card_fin_lt']
        exact (hν3 q.1 q.2).trans (o _).2.le
    _ = ((univ.filter fun r' : (sys R FL Pl).R =>
        (sys R FL Pl).rp r' = p ∧ (eE R FL r'.1).isRight = true).attach.biUnion fun q => Fr q.1 q.2).card := by
        rw [card_biUnion]
        intro q _ q' _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro u hu hu'
        obtain ⟨k, -, rfl⟩ := mem_image.1 hu
        obtain ⟨k', -, e⟩ := mem_image.1 hu'
        apply hne
        have e1 : (ν q'.1 q'.2).1 = (ν q.1 q.2).1 := congrArg Sigma.fst (Uid.new.inj e).1
        rw [hν1, hν1] at e1
        obtain ⟨⟨x, ro⟩, hq⟩ := q
        obtain ⟨⟨x', ro'⟩, hq'⟩ := q'
        simp only at e1
        subst e1
        have a1 := (mem_filter.1 hq).2.1
        have a2 := (mem_filter.1 hq').2.1
        obtain rfl : ro = ro' := (sys R FL Pl).inj x' (a1.trans a2.symm)
        rfl
    _ ≤ _ := by
        refine card_le_card fun u hu => ?_
        obtain ⟨q, -, hu⟩ := mem_biUnion.1 hu
        obtain ⟨k, hk, rfl⟩ := mem_image.1 hu
        refine mem_filter.2 ⟨mem_seen_new.2 ?_, ?_⟩
        · rw [Fin.le_def]
          have := (mem_filter.1 hk).2
          have := hν3 q.1 q.2
          omega
        · obtain ⟨d, hd⟩ := hν2 q.1 q.2
          cases d
          · exact Or.inl hd.symm
          · exact Or.inr hd.symm

end Build

section Good

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' N U1 ℓ : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'}

/-- "Every possible outcome is good, by Theorem thm:laws(b), the triangle inequality over the tℓ layers, and λ ≥ 1." -/
theorem thm_tree_poss_good (hℓ : 0 < ℓ) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1)
    (x : Fin (Fintype.card (Mv T R ch FL))) (hp : (Tow.plan R FL Pl N N U1).Poss n o ℓ x) :
    (Tow.plan R FL Pl N N U1).good n o x := by
  refine poss_good hℓ ?_
  obtain ⟨ι, hι⟩ := hp
  refine ⟨ι, fun ν => ?_⟩
  have h1 : (eN R FL Pl).symm ⟨eE R FL x, ν⟩ = ⟨x, ν⟩ := by
    rw [Equiv.symm_apply_eq]
    rfl
  unfold oo
  rw [h1]
  exact hι ν

end Good

section Program

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r}
variable {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}
variable {Inp ι : Type} {Dd Y p TM : ℕ} {inp : ι → Inp → Fin Dd} {H : Set (Inp → ℕ)}
variable {nI : Inp → Fin AA → Fin AA → Fin (U0 + 1)} {oI : Inp → (sys R FL Pl).N → Fin U1}

/-- The program of the tower plan, with the parents and the loads. -/
theorem tree_slp (hA : Alph Dd Y) (hB : Bnd R ch FL U0 U1 Y) (hB2 : Bnd2 R FL Pl U0 U1 Y TM) (hh : 0 < h) (hb : 0 < b)
    (hS : SlpN inp p H) (hn : ∀ a c, (fun x => ((nI x a c : Fin (U0 + 1)) : ℕ)) ∈ H)
    (ho : ∀ ν, (fun x => ((oI x ν : Fin U1) : ℕ)) ∈ H) (lhat : ℕ) :
    ∃ H', SlpN inp (p + Y ^ 16) H' ∧ Units nI oI lhat TM H' ∧
      HostOk hh (fun x => load R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x))) H' ∧
      ∀ (j : ℕ) (_ : j ≤ J) (c : T.X j), (fun x => fb (lev (load R ch FL lhat (nn (nI x)) (oo R FL Pl (oI x)))) j c) ∈ H' := by
  have hR : Rng (nX nI) (oX oI : Inp → NM R FL (ch := ch) → ℕ) U0 U1 := rng
  have hS0 : SY inp Y p 0 H := by
    unfold SY
    rw [Nat.zero_mul, Nat.add_zero]
    exact hS
  have hb0 : Base (nX nI) (oX oI : Inp → NM R FL (ch := ch) → ℕ) H := ⟨hn, fun ν => ho _⟩
  obtain ⟨H1, s1, u1, f1⟩ := after_stage hA hB hR hb hS0 hb0 (lhat := lhat)
  obtain ⟨H2, s2, u2, f2⟩ := units_stage hA hB hB2 s1 f1
  obtain ⟨H3, s3, u3, f3⟩ := host_stage hh (L := fun x => load R ch FL lhat (nX nI x) (oX oI x)) hA hB s2
    (fun j i => u2 (f1.isMin j i))
  obtain ⟨H4, s4, u4, f4⟩ := fb_stage (L := fun x => load R ch FL lhat (nX nI x) (oX oI x)) hA hB
    (fun x τ => ld_le (hR.n x) (hR.o x) _ τ) s3 (fun τ => u3 (u2 (f1.load τ)))
  refine ⟨H4, ?_, (f2.weaken u3).weaken u4, fun j hj c c' => u4 (f3 j hj c c'), f4⟩
  refine SlpN.le hA.zero_lt ?_ s4
  have h3 := hA.three
  have h4 : 0 + 11 + 8 * Y + 9 + 1 + 1 ≤ Y ^ 4 := by
    have e1 : Y ^ 4 = Y ^ 3 * Y := by ring
    have e2 : 3 ^ 3 ≤ Y ^ 3 := Nat.pow_le_pow_left h3 3
    have e3 : 3 ^ 3 * Y ≤ Y ^ 3 * Y := Nat.mul_le_mul_right _ e2
    omega
  have h5 : (0 + 11 + 8 * Y + 9 + 1 + 1) * Y ^ 12 ≤ Y ^ 16 := by
    calc _ ≤ Y ^ 4 * Y ^ 12 := Nat.mul_le_mul_right _ h4
      _ = Y ^ 16 := by ring
  exact Nat.add_le_add_left h5 p

/-- Parents are computed: the indicator of "q is the parent of p". -/
theorem par_computed {U0' : ℕ} {n' : Inp → Fin AA → Fin AA → Fin (U0' + 1)} {o' : Inp → (sys R FL Pl).N → Fin U1}
    (hh : 0 < h) (hH : HostOk hh (fun x => load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x))) H) (a q : Fin (AA + A')) :
    (ind fun x => treePar R FL Pl hh (n' x) (o' x) a = q) ∈ H ∪ {(fun _ => 0), (fun _ => 1)} := by
  classical
  have hconst : ∀ P : Prop, (ind fun _ : Inp => P) ∈ H ∪ {(fun _ => 0), (fun _ => 1)} := by
    intro P
    by_cases hP : P
    · refine Or.inr (Or.inr (funext fun x => ?_))
      exact ind_true (P := fun _ : Inp => P) hP
    · refine Or.inr (Or.inl (funext fun x => ?_))
      exact ind_false (P := fun _ : Inp => P) hP
  rcases nd_cases (Pl.pt.symm a) with e | ⟨j, hj, c, e⟩
  · simp only [treePar, e, ndPar]
    exact hconst _
  simp only [treePar, e]
  by_cases hjJ : j < J
  · rcases nd_cases (Pl.pt.symm q) with eq | ⟨i, hi, c', eq⟩
    · have : ∀ x, ¬ (Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) := by
        intro x hx
        have := congrArg Pl.pt.symm hx
        rw [Equiv.symm_apply_apply, eq] at this
        simp only [ndPar, nd, parN, dif_pos (show j + 1 ≤ J by omega)] at this
        exact absurd this (Option.some_ne_none _)
      rw [show (fun x => Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) =
        fun _ => False from funext fun x => eq_false (this x)]
      exact hconst _
    · by_cases hij : i = j + 1
      · subst hij
        refine Or.inl ?_
        have e2 : (fun x => Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) =
            fun x => hostj hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) c = c' := by
          funext x
          rw [← Equiv.eq_symm_apply, eq]
          simp only [ndPar, nd, parN, dif_pos (show j + 1 ≤ J by omega)]
          simp
        rw [e2]
        exact hH j hjJ c c'
      · have : ∀ x, ¬ (Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) := by
          intro x hx
          have := congrArg Pl.pt.symm hx
          rw [Equiv.symm_apply_apply, eq] at this
          have h1 := congrArg ndStage this
          rw [ndStage_par hh _ nd_ne_none] at h1
          exact hij h1.symm
        rw [show (fun x => Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) =
          fun _ => False from funext fun x => eq_false (this x)]
        exact hconst _
  · have e2 : (fun x => Pl.pt (ndPar hh (lev (load R ch FL U0' (nn (n' x)) (oo R FL Pl (o' x)))) (nd T j hj c)) = q) =
        fun _ => Pl.pt none = q := by
      funext x
      simp only [ndPar, nd, parN, dif_neg (show ¬ j + 1 ≤ J by omega)]
    rw [e2]
    exact hconst _

end Program

section Numbers

theorem lg_two {M : ℕ} (hM : 2 ≤ M) : 2 ≤ lg M := by
  unfold lg
  have := Nat.log_pos (b := 2) (n := M) (by norm_num) hM
  omega

/-- A constant times a power is a higher power. -/
theorem const_mul_pow_le {L : ℕ} (hL : 2 ≤ L) {k e C : ℕ} (h : k + e ≤ C) : k * L ^ e ≤ L ^ C := by
  calc k * L ^ e ≤ L ^ k * L ^ e :=
        Nat.mul_le_mul_right _ ((Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hL k))
    _ = L ^ (k + e) := (pow_add _ _ _).symm
    _ ≤ L ^ C := Nat.pow_le_pow_right (by omega) h

/-- The constant in front of the bounds for loads. -/
def cKap (c : ℕ) : ℕ := 2 * c * (c * (c * (2 * c + 1) ^ 7 * c * (1 + 2 * c ^ 2)))

theorem kapB_tree {c m X M J N : ℕ} (hX : X ≤ c * M) (hm : m ≤ c * (J + 1) ^ 7) (hJ : J + 1 ≤ (2 * c + 1) * lg M) :
    2 * c * kapB c m X N ≤ cKap c * (lg M ^ 7 * M * (N + M ^ 2)) := by
  have h1 : N + 2 * X ^ 2 ≤ (1 + 2 * c ^ 2) * (N + M ^ 2) := by
    have : X ^ 2 ≤ (c * M) ^ 2 := Nat.pow_le_pow_left hX 2
    nlinarith
  unfold kapB
  calc 2 * c * (c * (m * X * (N + 2 * X ^ 2))) ≤
      2 * c * (c * (c * ((2 * c + 1) ^ 7 * lg M ^ 7) * (c * M) * ((1 + 2 * c ^ 2) * (N + M ^ 2)))) := by
        have := m_le hm hJ
        gcongr
    _ = _ := by unfold cKap; ring

/-- The gain, as a power of M. -/
theorem gain_rpow {B A M X q : ℕ} (hq : 0 < q) (hM : 0 < M) (hX : M ≤ X) (h : B ^ q * X ^ 1 ≤ A ^ q) :
    (B : ℝ) ≤ (A : ℝ) * (M : ℝ) ^ (-(1 / (q : ℝ))) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h1 : ((B : ℝ) * (M : ℝ) ^ (1 / (q : ℝ))) ^ q ≤ (A : ℝ) ^ q := by
    rw [mul_pow, ← Real.rpow_natCast ((M : ℝ) ^ (1 / (q : ℝ))) q, ← Real.rpow_mul hM0.le,
      one_div_mul_cancel (by exact_mod_cast hq.ne'), Real.rpow_one]
    have h2 : B ^ q * M ≤ A ^ q := (Nat.mul_le_mul_left _ (by rwa [pow_one])).trans h
    exact_mod_cast h2
  have h3 := le_of_pow_le_pow_left₀ hq.ne' (Nat.cast_nonneg A) h1
  rw [Real.rpow_neg hM0.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact h3

/-- Powers of a constant times Z are powers of Z. -/
theorem const_pow_le {c Z a C : ℕ} (hZ : 2 ≤ Z) (h : (c + 4) * a ≤ C) : ((c + 3) * Z) ^ a ≤ Z ^ C := by
  calc ((c + 3) * Z) ^ a ≤ (Z ^ (c + 3) * Z) ^ a := by
        gcongr
        exact (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hZ _)
    _ = Z ^ ((c + 4) * a) := by rw [← pow_succ, ← pow_mul]
    _ ≤ Z ^ C := Nat.pow_le_pow_right (by omega) h

end Numbers

section Lemmas

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' N U1 ℓ c : ℕ} {T : Tower h b D J r}
  {R : Routes T m Uu} {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {ρ : ℝ}

/-- Units are few: the bounds in numbers. -/
theorem tree_nums {c M N X J m : ℕ} (hc : 1 ≤ c) (hM : 2 ≤ M) (hN : 1 ≤ N) (hX : X ≤ c * M) (hJ : J + 1 ≤ X)
    (hm : m ≤ c * (J + 1) ^ 7) :
    c ≤ ((c + 3) * M) ^ 9 ∧ m ≤ ((c + 3) * M) ^ 9 ∧ X ≤ ((c + 3) * M) ^ 9 ∧ M ≤ ((c + 3) * M) ^ 9 ∧
      ((c + 3) * M) ^ 9 ≤ ((c + 3) * (M * N)) ^ 30 ∧ N ≤ ((c + 3) * (M * N)) ^ 30 ∧
      capB c m X N N * (c + c) + 1 ≤ ((c + 3) * (M * N)) ^ 30 := by
  obtain ⟨G, hG⟩ : ∃ G, G = (c + 3) * (M * N) := ⟨_, rfl⟩
  obtain ⟨G0, hG0⟩ : ∃ G0, G0 = (c + 3) * M := ⟨_, rfl⟩
  rw [← hG, ← hG0]
  have hG0G : G0 ≤ G := by rw [hG0, hG]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hN)
  have hXG : X ≤ G0 := by rw [hG0]; exact hX.trans (Nat.mul_le_mul_right _ (by omega))
  have hcG : c + 3 ≤ G0 := by rw [hG0]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hMG : M ≤ G0 := by rw [hG0]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hNG : N ≤ G := by
    rw [hG]
    exact (Nat.le_mul_of_pos_left _ (by omega : 0 < M)).trans (Nat.le_mul_of_pos_left _ (by omega))
  have q : ∀ a a', a ≤ a' → G0 ^ a ≤ G0 ^ a' := fun a a' ha => Nat.pow_le_pow_right (by omega) ha
  have p : ∀ a a', a ≤ a' → G ^ a ≤ G ^ a' := fun a a' ha => Nat.pow_le_pow_right (by omega) ha
  have hG9 : G0 ≤ G0 ^ 9 := Nat.le_self_pow (by norm_num) _
  have hG30 : G ≤ G ^ 30 := Nat.le_self_pow (by norm_num) _
  have hm8 : m ≤ G0 ^ 8 := by
    calc m ≤ c * (J + 1) ^ 7 := hm
      _ ≤ G0 * G0 ^ 7 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (hJ.trans hXG) 7)
      _ = G0 ^ 8 := by ring
  refine ⟨by omega, hm8.trans (q 8 9 (by norm_num)), by omega, by omega,
    (Nat.pow_le_pow_left hG0G 9).trans (p 9 30 (by norm_num)), by omega, ?_⟩
  have hm8' : m ≤ G ^ 8 := hm8.trans (Nat.pow_le_pow_left hG0G 8)
  have h1 : kapB c m X N ≤ G ^ 15 := by
    unfold kapB
    calc c * (m * X * (N + 2 * X ^ 2)) ≤ G * (G ^ 8 * G * (G + G * G ^ 2)) := by
          gcongr <;> omega
      _ = G ^ 11 + G ^ 13 := by ring
      _ ≤ G ^ 13 + G ^ 13 := Nat.add_le_add_right (p 11 13 (by norm_num)) _
      _ = 2 * G ^ 13 := by ring
      _ ≤ G * G ^ 13 := Nat.mul_le_mul_right _ (by omega)
      _ = G ^ 14 := by ring
      _ ≤ G ^ 15 := p 14 15 (by norm_num)
  have h2 : capB c m X N N ≤ G ^ 18 := by
    unfold capB
    have e1 : G ≤ G ^ 17 := Nat.le_self_pow (by norm_num) _
    calc N + 2 + 3 * c * kapB c m X N ≤ G + G + G * G * G ^ 15 := by gcongr <;> omega
      _ = G + G + G ^ 17 := by ring
      _ ≤ G ^ 17 + G ^ 17 + G ^ 17 := by omega
      _ = 3 * G ^ 17 := by ring
      _ ≤ G * G ^ 17 := Nat.mul_le_mul_right _ (by omega)
      _ = G ^ 18 := by ring
  calc capB c m X N N * (c + c) + 1 ≤ G ^ 18 * (G + G) + G ^ 19 := by
        gcongr <;> first | omega | exact Nat.one_le_pow _ _ (by omega)
    _ = 3 * G ^ 19 := by ring
    _ ≤ G * G ^ 19 := Nat.mul_le_mul_right _ (by omega)
    _ = G ^ 20 := by ring
    _ ≤ G ^ 30 := p 20 30 (by norm_num)

open Classical in
/-- The children of a node are few. -/
theorem card_treeChildren (hh : 0 < h) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1)
    (q : Fin (AA + A')) :
    (univ.filter fun p => p ≠ Pl.pt none ∧ treePar R FL Pl hh n o p = q).card ≤
      (if q = Pl.pt none then Fintype.card (T.X J) else b) := by
  obtain ⟨ν, rfl⟩ := Pl.pt.surjective q
  have h1 : (univ.filter fun p => p ≠ Pl.pt none ∧ treePar R FL Pl hh n o p = Pl.pt ν).card ≤
      (univ.filter fun μ : Nd T => μ ≠ none ∧ ndPar hh (lev (load R ch FL N (nn n) (oo R FL Pl o))) μ = ν).card := by
    refine card_le_card_of_injOn Pl.pt.symm ?_ Pl.pt.symm.injective.injOn
    intro p hp
    obtain ⟨-, h1, h2⟩ := mem_filter.1 (mem_coe.1 hp)
    refine mem_coe.2 (mem_filter.2 ⟨mem_univ _, fun e => h1 ?_, Pl.pt.injective h2⟩)
    rw [← Equiv.apply_symm_apply Pl.pt p, e]
  by_cases hν : ν = none
  · subst hν
    rw [if_pos rfl]
    exact h1.trans (card_ndRoot _ _)
  · rw [if_neg fun e => hν (Pl.pt.injective e)]
    exact h1.trans (card_ndChildren _ _ hν)

open Classical in
/-- The units at one node. -/
theorem tree_node_le (hH : THypR FL ρ) {n : Fin AA → Fin AA → Fin (N + 1)}
    (hv : Valid N (nn n)) {o : (sys R FL Pl).N → Fin U1} (hg : ∀ x, (Tow.plan R FL Pl N N U1).good n o x)
    (hb : b ≤ c) (hX : Fintype.card (T.X J) ≤ c) (p : Fin (AA + A')) :
    ((cutUnits (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) id
      ((Tow.plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL)) \ deadU R FL Pl N o)).filter
      (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) p)).card ≤ (c + 1) * BhN FL Uu AA N ρ := by
  let S := (univ : Finset (Σ j : Fin (J + 1), T.X j)).filter fun s =>
    Pl.pt (some s) = p ∨ treePar R FL Pl hH.h_pos n o (Pl.pt (some s)) = p
  refine le_trans (card_le_card (t := S.biUnion (AsU R FL Pl N n o)) ?_) ?_
  · intro u hu
    obtain ⟨hu1, hu2⟩ := mem_filter.1 hu
    obtain ⟨hu1, hu4⟩ := mem_filter.1 hu1
    obtain ⟨hu1, hu3⟩ := mem_sdiff.1 hu1
    obtain ⟨s, hs1, hs2⟩ := cur_tree hH hv hg hu1 hu3 hu4
    refine mem_biUnion.2 ⟨s, mem_filter.2 ⟨mem_univ _, ?_⟩, hs1⟩
    have h2 : p ∈ s(Pl.pt (some s), treePar R FL Pl hH.h_pos n o (Pl.pt (some s))) := by
      rw [← hs2, Sym2.mem_iff]
      exact hu2
    rw [Sym2.mem_iff] at h2
    exact h2.imp Eq.symm Eq.symm
  refine card_biUnion_le.trans ((Finset.sum_le_sum fun s _ => (card_AsU hH.r_pos hH.b_pos hH.h_pos s).trans
    (fb_le hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.gain hH.two _ (Nat.le_of_lt_succ s.1.2) _)).trans ?_)
  rw [Finset.sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  calc S.card ≤ ({p} ∪ univ.filter fun v => v ≠ Pl.pt none ∧ treePar R FL Pl hH.h_pos n o v = p : Finset _).card := by
        refine card_le_card_of_injOn (fun s => Pl.pt (some s)) ?_ (fun s _ s' _ e => Option.some.inj (Pl.pt.injective e))
        intro s hs
        rcases (mem_filter.1 (mem_coe.1 hs)).2 with h3 | h3
        · exact mem_coe.2 (mem_union_left _ (mem_singleton.2 h3))
        · exact mem_coe.2 (mem_union_right _ (mem_filter.2
            ⟨mem_univ _, fun e => Option.some_ne_none s (Pl.pt.injective e), h3⟩))
    _ ≤ 1 + (univ.filter fun v => v ≠ Pl.pt none ∧ treePar R FL Pl hH.h_pos n o v = p).card :=
        (card_union_le _ _).trans (by simp)
    _ ≤ c + 1 := by
        have := card_treeChildren (R := R) (FL := FL) (Pl := Pl) hH.h_pos n o p
        split_ifs at this <;> omega

open Classical in
/-- All units of the tree. -/
theorem tree_total_le (hH : THypR FL ρ) {n : Fin AA → Fin AA → Fin (N + 1)}
    (hv : Valid N (nn n)) {o : (sys R FL Pl).N → Fin U1} (hg : ∀ x, (Tow.plan R FL Pl N N U1).good n o x) :
    (cutUnits (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) id
      ((Tow.plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL)) \ deadU R FL Pl N o)).card ≤
      YhN FL Uu AA N ρ := by
  refine le_trans (card_le_card (t := univ.biUnion (AsU R FL Pl N n o)) ?_) ?_
  · intro u hu
    obtain ⟨hu, hu4⟩ := mem_filter.1 hu
    obtain ⟨hu1, hu3⟩ := mem_sdiff.1 hu
    obtain ⟨s, hs1, -⟩ := cur_tree hH hv hg hu1 hu3 hu4
    exact mem_biUnion.2 ⟨s, mem_univ _, hs1⟩
  refine card_biUnion_le.trans ((Finset.sum_le_sum fun s _ => card_AsU hH.r_pos hH.b_pos hH.h_pos s).trans ?_)
  rw [Fintype.sum_sigma, Fin.sum_univ_eq_sum_range
    (fun j => ∑ x : T.X j, fb (lev (load R ch FL N (nn n) (oo R FL Pl o))) j x) (J + 1)]
  exact sum_fb_le hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.ρ_lt hH.gain hH.two

open Classical in
/-- The units between a party and its parent are at most the load at it. -/
theorem tree_between (hH : THypR FL ρ) {n : Fin AA → Fin AA → Fin (N + 1)} (hv : Valid N (nn n))
    {o : (sys R FL Pl).N → Fin U1} (hg : ∀ x, (Tow.plan R FL Pl N N U1).good n o x) {p : Fin (AA + A')}
    (hp : p ≠ Pl.pt none) :
    ((cutUnits (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) id
      ((Tow.plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL)) \ deadU R FL Pl N o)).filter
      (fun u => s(hold0 (sys R FL Pl).np u, hold1 (sys R FL Pl).np u) =
        s(p, treePar R FL Pl hH.h_pos n o p))).card ≤ treeUp R FL Pl n o p := by
  obtain ⟨ν, rfl⟩ := Pl.pt.surjective p
  rcases ν with _ | q
  · exact absurd rfl hp
  refine (card_le_card (t := AsU R FL Pl N n o q) fun u hu => ?_).trans ?_
  · obtain ⟨hu, hu2⟩ := mem_filter.1 hu
    obtain ⟨hu, hu4⟩ := mem_filter.1 hu
    obtain ⟨hu1, hu3⟩ := mem_sdiff.1 hu
    obtain ⟨s', hs1, hs2⟩ := cur_tree hH hv hg hu1 hu3 hu4
    have he := hs2.symm.trans hu2
    rcases Sym2.eq_iff.1 he with ⟨e1, -⟩ | ⟨e1, e2⟩
    · rwa [← Option.some.inj (Pl.pt.injective e1)]
    · exfalso
      simp only [treePar, Equiv.symm_apply_apply] at e1 e2
      have a1 := ndStage_par hH.h_pos (lev (load R ch FL N (nn n) (oo R FL Pl o))) (Option.some_ne_none q)
      have a2 := ndStage_par hH.h_pos (lev (load R ch FL N (nn n) (oo R FL Pl o))) (Option.some_ne_none s')
      rw [← Pl.pt.injective e1] at a1
      rw [Pl.pt.injective e2] at a2
      omega
  · refine (card_AsU hH.r_pos hH.b_pos hH.h_pos q).trans (le_of_eq ?_)
    simp only [treeUp, Equiv.symm_apply_apply]
    rfl

open Classical in
/-- The loads at one node. -/
theorem tree_up_node (hH : THypR FL ρ) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1)
    (hb : b ≤ c) (hX : Fintype.card (T.X J) ≤ c) (p : Fin (AA + A')) :
    treeUp R FL Pl n o p + ∑ q ∈ univ.filter (fun q => q ≠ Pl.pt none ∧ treePar R FL Pl hH.h_pos n o q = p),
      treeUp R FL Pl n o q ≤ (c + 1) * BhN FL Uu AA N ρ := by
  have h1 : ∀ q, treeUp R FL Pl n o q ≤ BhN FL Uu AA N ρ := fun q => by
    rcases nd_cases (Pl.pt.symm q) with e | ⟨j, hj, x, e⟩
    · simp [treeUp, e, onN]
    · simp only [treeUp, e, onN_nd]
      exact fb_le hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.gain hH.two j hj x
  rw [add_mul, one_mul, add_comm]
  refine Nat.add_le_add ((Finset.sum_le_sum fun q _ => h1 q).trans ?_) (h1 p)
  rw [Finset.sum_const, smul_eq_mul]
  refine Nat.mul_le_mul_right _ ?_
  have := card_treeChildren (R := R) (FL := FL) (Pl := Pl) hH.h_pos n o p
  split_ifs at this <;> omega

/-- All loads. -/
theorem tree_up_total (hH : THypR FL ρ) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1) :
    ∑ p, treeUp R FL Pl n o p ≤ YhN FL Uu AA N ρ := by
  rw [← Equiv.sum_comp Pl.pt]
  simp only [treeUp, Equiv.symm_apply_apply]
  rw [Fintype.sum_option]
  simp only [onN, Nat.zero_add]
  rw [Fintype.sum_sigma, Fin.sum_univ_eq_sum_range
    (fun j => ∑ x : T.X j, fb (lev (load R ch FL N (nn n) (oo R FL Pl o))) j x) (J + 1)]
  exact sum_fb_le hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.ρ_lt hH.gain hH.two

/-- The loads at a chamber and below its children are those at the party and its children. -/
theorem onN_le_up (hh : 0 < h) (n : Fin AA → Fin AA → Fin (N + 1)) (o : (sys R FL Pl).N → Fin U1) (P : Nd T) :
    onN (fun j x => 8 * fb (LfO R ch FL Pl N n o) j x + 3 * chF hh (LfO R ch FL Pl N n o) j x)
        (∑ e : T.Ed J, LfO R ch FL Pl N n o J e) P ≤
      8 * (treeUp R FL Pl n o (Pl.pt P) + ∑ q ∈ univ.filter (fun q => q ≠ Pl.pt none ∧
        treePar R FL Pl hh n o q = Pl.pt P), treeUp R FL Pl n o q) := by
  classical
  have kids : ∀ (j : ℕ) (hj : j ≤ J) (s : Finset (T.X j)),
      (∀ x ∈ s, parN hh (LfO R ch FL Pl N n o) j x = P) →
      ∑ x ∈ s, fb (LfO R ch FL Pl N n o) j x ≤ ∑ q ∈ univ.filter (fun q => q ≠ Pl.pt none ∧
        treePar R FL Pl hh n o q = Pl.pt P), treeUp R FL Pl n o q := by
    intro j hj s hs
    have e1 : ∀ x, treeUp R FL Pl n o (Pl.pt (nd T j hj x)) = fb (LfO R ch FL Pl N n o) j x := fun x => by
      simp only [treeUp, Equiv.symm_apply_apply, onN_nd]

    rw [← Finset.sum_congr rfl fun x _ => e1 x,
      ← Finset.sum_image (f := treeUp R FL Pl n o) (g := fun x => Pl.pt (nd T j hj x))
        (fun x _ x' _ e => nd_inj.1 (Pl.pt.injective e))]
    refine Finset.sum_le_sum_of_subset fun q hq => ?_
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hq
    refine mem_filter.2 ⟨mem_univ _, fun e => nd_ne_none (Pl.pt.injective e), ?_⟩
    simp only [treePar, Equiv.symm_apply_apply]
    exact congrArg Pl.pt (hs x hx)
  rcases nd_cases P with rfl | ⟨j, hj, x, rfl⟩
  · have h1 := kids J le_rfl univ fun x _ => by
      unfold parN
      rw [dif_neg (by omega)]
    have h2 := T.sum_bet (LfO R ch FL Pl N n o J)
    have h3 : ∑ x, fb (LfO R ch FL Pl N n o) J x = ∑ x, T.bet (LfO R ch FL Pl N n o J) x := rfl
    simp only [onN]
    omega
  · rw [onN_nd]
    have e1 : treeUp R FL Pl n o (Pl.pt (nd T j hj x)) = fb (LfO R ch FL Pl N n o) j x := by
      simp only [treeUp, Equiv.symm_apply_apply, onN_nd]

    rw [e1]
    rcases j with _ | j
    · simp only [chF]
      omega
    · have h1 : chF hh (LfO R ch FL Pl N n o) (j + 1) x ≤ _ :=
        le_trans (le_of_eq (by rw [chF, chs, Finset.sum_filter]))
          (kids j (by omega) (univ.filter fun y => hostj hh (LfO R ch FL Pl N n o) y = x) fun y hy => by
            unfold parN
            rw [dif_pos hj, (mem_filter.1 hy).2])
      omega

open Classical in
/-- **Paper: proof of Theorem thm:tree, Bounds.** The Lean form of "At no time does a node hold more than a constant times
the units that it has in the end ...": relays leave copies here, so what a node ever holds, zeros in slots included, is at
most a constant times the loads at it and its children, plus (1+8m)N at a given node (m bounds the words) and twice the
dead units at it. -/
theorem thm_tree_copies (hH : THypR FL ρ) {n : Fin AA → Fin AA → Fin (N + 1)}
    (hv : ∀ a, ∑ c, ((n a c).1 + (n c a).1) ≤ N) {o : (sys R FL Pl).N → Fin U1}
    (hg : ∀ x, (Tow.plan R FL Pl N N U1).good n o x) {Sm : ℕ} (hSm : ∀ d, Fintype.card (FL.L d).Sl ≤ Sm)
    (p : Fin (AA + A')) :
    ((Plan.seenAt n o (Fintype.card (Mv T R ch FL))).filter
        (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) p)).card +
        ∑ r' ∈ univ.filter (fun r' : (sys R FL Pl).R => (sys R FL Pl).rp r' = p),
          (1 + Fintype.card (((sys R FL Pl).kind r'.1).SlAt r'.2)) * (Tow.plan R FL Pl N N U1).num n o r'.1 ≤
      (4 + (2 * Fintype.card T.Nr * FL.G₁ + 1 + Sm) * Fintype.card FL.Di) * 8 * (treeUp R FL Pl n o p +
          ∑ q ∈ univ.filter (fun q => q ≠ Pl.pt none ∧ treePar R FL Pl hH.h_pos n o q = p), treeUp R FL Pl n o q) +
        (if (p : ℕ) < AA then (1 + 8 * m) * N else 0) +
        2 * ((deadU R FL Pl N o).filter (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) p)).card := by
  have hgd : ∀ mv, GoodMv R ch FL N (nn n) (oo R FL Pl o) mv := fun mv => by
    have h1 : GoodMv R ch FL N (nn n) (oo R FL Pl o) (eE R FL ((eE R FL).symm mv)) := hg ((eE R FL).symm mv)
    rwa [Equiv.apply_symm_apply] at h1
  obtain ⟨P, rfl⟩ := Pl.pt.surjective p
  have h0 := held_node_le (R := R) (Pl := Pl) (lhat := N) (n := n) (o := o) hH.h_pos hH.r_pos hH.b_pos
    (fun x ν => hgd (.inl x) ν) (fun l => hgd (.inr l)) hH.near hSm (ℓf := N) P (fun a _ => hv a)
  have h2 : isB ch P * (N + 8 * m * N) ≤ if ((Pl.pt P : Fin (AA + A')) : ℕ) < AA then (1 + 8 * m) * N else 0 := by
    unfold isB
    split_ifs with e1 e2 e2
    · exact le_of_eq (by ring)
    · obtain ⟨a, rfl⟩ := e1
      exact absurd (by rw [Pl.pt_base]; exact a.2) e2
    · simp
    · simp
  have h3 : chanN R FL Pl (Pl.pt P) ≤
      2 * ((deadU R FL Pl N o).filter (Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) (Pl.pt P))).card := by
    unfold deadU chanN
    rw [Finset.filter_image, card_image_of_injective _ (fun ν ν' e => (Uid.new.inj e).1), card_filter, Finset.mul_sum]
    refine Finset.sum_le_sum fun ν _ => ?_
    rw [Fintype.sum_bool]
    by_cases e : Holds (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) (Pl.pt P)
        (Uid.new ν (o ν) : Un R FL Pl N U1)
    · rw [if_pos e]
      split_ifs <;> omega
    · rw [if_neg e, if_neg fun h => e (Or.inr h.symm), if_neg fun h => e (Or.inl h.symm)]
      exact Nat.zero_le _
  have h4 := onN_le_up (R := R) (FL := FL) (Pl := Pl) hH.h_pos n o P
  rw [Finset.sum_filter]
  refine le_trans h0 ?_
  calc _ ≤ _ + _ + _ := Nat.add_le_add (Nat.add_le_add h2 h3) (Nat.mul_le_mul_left _ h4)
    _ = _ := by ring

open Classical in
/-- The network is the sum of the networks on trees. -/
theorem tree_value (hH : THypR FL ρ) (hℓ : 1 ≤ ℓ) {cap : ℕ} (hcap : capN FL N Uu AA N ≤ cap)
    (hlen : ∀ d, (FL.L d).Le c ∧ (FL.L d).lam ≤ c) (hc : 1 ≤ c) (hU1 : U1 = cap * (c + c) + 1)
    {n : Fin AA → Fin AA → Fin (N + 1)} (tab : ∀ a, NodeTable F (fun a c => (n a c).1) ℓ a) :
    netValue tab = ∑ o : (sys R FL Pl).N → Fin U1, if ∀ x, (Tow.plan R FL Pl N N U1).good n o x then
      ∑ w ∈ Common (none : UW ℓ) (cutUnits (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) id
        ((Tow.plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL)))), ∏ p,
        groupVal (hold0 (sys R FL Pl).np) (hold1 (sys R FL Pl).np) none
          (Plan.seenAt n o (Fintype.card (Mv T R ch FL)))
          ((Tow.plan R FL Pl N N U1).cur n o (Fintype.card (Mv T R ch FL))) id
          (fun a => partyTab (Tow.plan R FL Pl N N U1) n o (startTab (sys R FL Pl) U1 n tab a) a) p w
      else 0 := by
  have hok : (Tow.plan R FL Pl N N U1).Ok (capN FL N Uu AA N) :=
    plan_ok_cap hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.ρ_lt hH.gain hH.two
  have hgood : ∀ n o x, (Tow.plan R FL Pl N N U1).Poss n o ℓ x → (Tow.plan R FL Pl N N U1).good n o x :=
    fun n o x => thm_tree_poss_good hℓ n o x
  have hkl : ∀ x, ((sys R FL Pl).kind x).Le c ∧ ((sys R FL Pl).kind x).lam ≤ c := by
    intro x
    change (kindM R ch FL (eE R FL x)).Le c ∧ (kindM R ch FL (eE R FL x)).lam ≤ c
    rcases eE R FL x with y | l
    · exact ⟨⟨fun _ _ => hc⟩, Nat.zero_le _⟩
    · exact hlen _
  have hU1' : ∀ x, capN FL N Uu AA N * (c + ((sys R FL Pl).kind x).lam) + 1 ≤ U1 := by
    intro x
    rw [hU1]
    exact Nat.add_le_add_right (Nat.mul_le_mul hcap (Nat.add_le_add_left (hkl x).2 c)) 1
  have hU0' : 0 < U1 := by omega
  rw [← posVal_start (S := sys R FL Pl) (U1 := U1) tab,
    Paper.thm_tree_moves hok hℓ hgood (m := fun _ => c) (fun x => (hkl x).1) hU0' hU1' n
      (startTab (sys R FL Pl) U1 n tab) (fun a y y' h => startTab_congr tab a h) (fun a y h => startTab_ne_none tab a y h)]
  refine Finset.sum_congr rfl fun o _ => ?_
  by_cases hg : ∀ x, (Tow.plan R FL Pl N N U1).good n o x
  swap
  · rw [if_neg hg, if_neg hg]
  rw [if_pos hg, if_pos hg, posVal_groups _ _ _ _ _ id]

open Classical in
/-- The program that computes the trees. -/
theorem tree_computed (hH : THypR FL ρ) {V : ℕ} (hV : 3 ≤ V) (hm : m ≤ V) (hJ : J + 1 ≤ V) (hh : h ≤ V) (hr : r ≤ V)
    (hAA : AA ≤ V) (hX : Fintype.card (T.X 0) ≤ V) (hdd : Fintype.card FL.Di ≤ V) (hbV : b ≤ V)
    (hfl : Fintype.card (Sym2 T.Fl) ≤ V) (hS : ∀ d, Fintype.card (FL.L d).Sl ≤ V) (hN : N ≤ V) (hU1 : U1 ≤ V)
    (hD : 0 < D) :
    ∃ (steps : ℕ) (inp : (Fin AA × Fin AA) ⊕ (sys R FL Pl).N →
        (Fin AA → Fin AA → Fin (N + 1)) × ((sys R FL Pl).N → Fin U1) → Fin ((20 * V ^ 9) ^ 4))
      (H : Set ((Fin AA → Fin AA → Fin (N + 1)) × ((sys R FL Pl).N → Fin U1) → ℕ)),
      steps ≤ 3 * (20 * V ^ 9) ^ 16 ∧ Fintype.card (Nd T) ≤ 20 * V ^ 9 ∧ Fintype.card (Mv T R ch FL) ≤ 20 * V ^ 9 ∧
      Fintype.card (Un R FL Pl N U1) ≤ 20 * V ^ 9 ∧
      (∀ a c x, (inp (.inl (a, c)) x : ℕ) = x.1 a c) ∧ (∀ ν x, (inp (.inr ν) x : ℕ) = x.2 ν) ∧ SlpN inp steps H ∧
      (∀ p q, (ind fun x => treePar R FL Pl hH.h_pos x.1 x.2 p = q) ∈ H) ∧
      (∀ u, (ind fun x => u ∈ (Tow.plan R FL Pl N N U1).cur x.1 x.2 (Fintype.card (Mv T R ch FL))) ∈ H) ∧
      (∀ z u, (ind fun x => u ∈ (Tow.plan R FL Pl N N U1).cons x.1 x.2 z) ∈ H) ∧
      (∀ y, (fun x => (Tow.plan R FL Pl N N U1).num x.1 x.2 y) ∈ H) ∧
      (∀ p, (fun x => treeUp R FL Pl x.1 x.2 p) ∈ H) ∧
      ∀ y, (ind fun x => (Tow.plan R FL Pl N N U1).good x.1 x.2 y) ∈ H := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := cards_le (R := R) (ch := ch) (FL := FL) (Pl := Pl) (U0 := N) (U1 := U1) hD
    hH.b_pos (by omega : 1 ≤ V) hh hr hm (show J ≤ V by omega) hAA hX hdd hbV hS hN hU1
  have n7 := card_Tg_le (T := T) (m := m) (AA := AA) hD hH.b_pos (by omega : 1 ≤ V) hh hr hm (show J ≤ V by omega) hAA hX
    hfl
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 20 * V ^ 9 := ⟨_, rfl⟩
  rw [← hY]
  have pw : ∀ a, a ≤ 9 → V ^ a ≤ V ^ 9 := fun a ha => Nat.pow_le_pow_right (by omega) ha
  have p2 := pw 2 (by omega)
  have p5 := pw 5 (by omega)
  have p6 := pw 6 (by omega)
  have p7 := pw 7 (by omega)
  have p1 : V ≤ V ^ 9 := Nat.le_self_pow (by norm_num) V
  have hA : Alph (Y ^ 4) Y := ⟨by omega, le_rfl⟩
  have hNM : Fintype.card (NM R FL (ch := ch)) = Fintype.card (sys R FL Pl).N := Fintype.card_congr (eN R FL Pl).symm
  have hZM : Fintype.card (ZM R FL (ch := ch)) = Fintype.card (sys R FL Pl).Z := Fintype.card_congr (eZ R FL Pl).symm
  have hWb : Wb R ch FL N U1 = Fintype.card (Un R FL Pl N U1) := by
    rw [card_Un]
    unfold Wb
    rw [hNM]
  have hAA2 : AA * AA ≤ V ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul hAA hAA
  have hBd : Bnd R ch FL N U1 Y := {
    aa := by omega
    w := by rw [hWb]; omega
    nm := by rw [hNM]; omega
    mv := by omega
    tg := by omega
    nd := by omega
    fl := by omega
    di := by omega
    h := by omega
    j := by omega
    t := by unfold tend; omega
    tt := by
      rw [hWb]
      have h1 : b * Fintype.card (Sym2 T.Fl) * Fintype.card (Un R FL Pl N U1) ≤ V * V * (18 * V ^ 7) := by gcongr
      have h2 : V * V * (18 * V ^ 7) = 18 * V ^ 9 := by ring
      omega }
  have hB2 : Bnd2 R FL Pl N U1 Y 0 := {
    zm := by rw [hZM]; omega
    un := by omega
    tm := Nat.zero_le _ }
  have hYY : Y < Y ^ 4 := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ < Y ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  let inp : (Fin AA × Fin AA) ⊕ (sys R FL Pl).N →
      (Fin AA → Fin AA → Fin (N + 1)) × ((sys R FL Pl).N → Fin U1) → Fin (Y ^ 4) := fun i x => match i with
    | .inl q => ⟨(x.1 q.1 q.2).1, by have := (x.1 q.1 q.2).2; omega⟩
    | .inr ν => ⟨(x.2 ν).1, by have := (x.2 ν).2; omega⟩
  obtain ⟨H', s1, f1, g1, e1⟩ := tree_slp (R := R) (FL := FL) (Pl := Pl) hA hBd hB2 hH.h_pos hH.b_pos
    (SlpN.inputs hA.zero_lt inp) (nI := fun x => x.1) (oI := fun x => x.2) (fun a b => ⟨.inl (a, b), rfl⟩)
    (fun ν => ⟨.inr ν, rfl⟩) N
  have s2 := (s1.snoc (fun _ => ⟨0, hA.zero_lt⟩) (Or.inr (Or.inl ⟨_, rfl⟩))).snoc
    (fun _ => ⟨1, hA.one_lt⟩) (Or.inr (Or.inl ⟨_, rfl⟩))
  refine ⟨_, inp, _, ?_, by omega, by omega, by omega, fun _ _ _ => rfl, fun _ _ => rfl, s2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e0 : Fintype.card ((Fin AA × Fin AA) ⊕ (sys R FL Pl).N) = AA * AA + Fintype.card (sys R FL Pl).N := by
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [e0]
    have : Y ≤ Y ^ 16 := Nat.le_self_pow (by norm_num) _
    omega
  · intro p q
    have key := par_computed (R := R) (FL := FL) (Pl := Pl) (U0' := N) (H := H') (n' := fun x => x.1) (o' := fun x => x.2)
      hH.h_pos g1 p q
    rcases key with h | h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · exact fun u => Or.inr (Or.inr (f1.cur u))
  · exact fun z u => Or.inr (Or.inr (f1.cons (eZ R FL Pl z) u))
  · exact fun y => Or.inr (Or.inr (f1.num (eE R FL y)))
  · intro p
    unfold treeUp
    rcases nd_cases (Pl.pt.symm p) with e | ⟨j, hj, c, e⟩
    · simp only [e, onN]
      exact Or.inr (Or.inl rfl)
    · simp only [e, onN_nd]
      exact Or.inr (Or.inr (e1 j hj c))
  · exact fun y => Or.inr (Or.inr (f1.good (eE R FL y)))

/-- **Paper: Theorem thm:tree, Start.** "Hence every edge gets at most n₀ = 4L(N+M²) units." -/
theorem thm_tree_start_units {n : Fin AA → Fin AA → ℕ} {o : NM R FL (ch := ch) → ℕ} (hr : 0 < r) (hb : 0 < b)
    (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hAA : AA ≤ Fintype.card (T.X 0)) (e : T.Ed 0) :
    load R ch FL N n o (.edge 0 e) ≤ 4 * m * (N + Fintype.card (T.X 0) ^ 2) := by
  refine (thm_tree_start hr hb e).trans ((Nat.mul_le_mul hUu le_rfl).trans ?_)
  calc 2 * Fintype.card (T.X 0) * m * (N / Fintype.card (T.X 0) + 2 * AA) =
      2 * m * (N / Fintype.card (T.X 0) * Fintype.card (T.X 0)) + 4 * m * (Fintype.card (T.X 0) * AA) := by ring
    _ ≤ 2 * m * N + 4 * m * (Fintype.card (T.X 0) * Fintype.card (T.X 0)) := by
        gcongr
        exact Nat.div_mul_le_self _ _
    _ ≤ 4 * m * N + 4 * m * (Fintype.card (T.X 0) * Fintype.card (T.X 0)) := by gcongr; omega
    _ = _ := by ring

end Lemmas

section Towers

/-- More generous routes. -/
def _root_.Nc.Tow.Routes.mono {h b D J r m Uu m' Uu' : ℕ} {T : Tower h b D J r} (R : Routes T m Uu) (hm : m ≤ m')
    (hU : Uu ≤ Uu') : Routes T m' Uu' where
  rt := R.rt
  walk := R.walk
  len c c' := (R.len c c').trans hm
  use e := (R.use e).trans hU

/-- "Take the least n ≥ 1 with M ≤ |G_n|; so |G_n| = O(M)": towers of all sizes from Proposition prop:tower, whose
parts (c) and (d) give the size, the bottom and the words of the routes. -/
theorem tree_towers {A : Type} [CommRing A] {h : ℕ} [NeZero h]
    (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h3 : 3 ≤ h)
    (hgain : 1 + 8 * VL.C₁ ≤ (1 / 2 : ℝ) ^ 2 * h) (htwo : (2 : ℝ) ≤ 1 / 2 * ((2 ^ ee h : ℕ) : ℝ)) :
    ∃ c, ∀ y, 1 ≤ y → ∃ (J m Uu : ℕ) (T : Tower h (2 ^ ee h) (2 ^ ee h) J 1) (_ : Routes T m Uu) (FL : FlagLaws A T),
      FL.G₁ = VL.G₁ ∧ TCst FL ((univ : Finset VL.Di).toList.map VL.L) c (1 / 2) 1 (ee h) ∧
      y ≤ Fintype.card (T.X 0) ∧ Fintype.card (T.X 0) ≤ c * y ∧ 1 ≤ m ∧ m ≤ c * (J + 1) ^ 7 ∧
      Uu ≤ 2 * Fintype.card (T.X 0) * m := by
  classical
  have h2 : 2 ≤ h := by omega
  obtain ⟨C, hC⟩ := prop_tower h h3
  have hee2 : 2 ≤ ee h := by
    unfold Nc.Tower.ee
    have : 3 * 2 ≤ h * (h - 1) := Nat.mul_le_mul h3 (by omega)
    omega
  have heeh : ee h ≤ h ^ 2 - 1 := by
    unfold Nc.Tower.ee
    have h4 : h * (h - 1) ≤ h * h := Nat.mul_le_mul_left _ (by omega)
    have h5 : h ^ 2 = h * h := by ring
    have h6 : 9 ≤ h * h := Nat.mul_le_mul h3 h3
    omega
  let S : ℕ := Nat.card (SL2 h)
  let g : ℕ → ℕ := fun n => Nat.card (Nc.Tower.G h n)
  have hg0 : ∀ n, g (n + 1) = g n * 2 ^ (h ^ 2 - 1) := fun n => (hC n).2.2.2.2.2.1
  have hg1 : ∀ n, 0 < g n := fun n => Nat.card_pos
  have hS : 0 < S := Nat.card_pos
  obtain ⟨c, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15⟩ : ∃ c : ℕ, h ≤ c ∧ 2 ^ ee h ≤ c ∧ 3 ≤ c ∧
      Fintype.card (NN h) ≤ c ∧ VL.G₁ ≤ c ∧ Fintype.card VL.Di ≤ c ∧ Fintype.card (Sym2 (U h)) ≤ c ∧
      ∑ d, Fintype.card (VL.L d).Sl ≤ c ∧ ∑ d, ∑ i, ∑ ν, (VL.L d).len i ν ≤ c ∧ ∑ d, (VL.L d).lam ≤ c ∧
      ⌈√(h : ℝ) * ((1 : ℕ) : ℝ) + √VL.C₁ * VL.a₁⌉₊ ≤ c ∧ S * 2 ^ ee h ≤ c ∧ g 0 ≤ c ∧ 2 ^ (h ^ 2 - 1) ≤ c ∧ C + 1 ≤ c := by
    let l : List ℕ := [h, 2 ^ ee h, 3, Fintype.card (NN h), VL.G₁, Fintype.card VL.Di, Fintype.card (Sym2 (U h)),
      ∑ d, Fintype.card (VL.L d).Sl, ∑ d, ∑ i, ∑ ν, (VL.L d).len i ν, ∑ d, (VL.L d).lam,
      ⌈√(h : ℝ) * ((1 : ℕ) : ℝ) + √VL.C₁ * VL.a₁⌉₊, S * 2 ^ ee h, g 0, 2 ^ (h ^ 2 - 1), C + 1]
    have hl : ∀ a ∈ l, a ≤ l.sum := fun a ha => List.single_le_sum (fun _ _ => Nat.zero_le _) a ha
    refine ⟨l.sum, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_,
      hl _ ?_, hl _ ?_, hl _ ?_, hl _ ?_⟩ <;> simp only [l, List.mem_cons, true_or, or_true]
  refine ⟨c, fun y hy => ?_⟩
  -- the least size
  have hg2 : ∀ n, 2 ^ n ≤ g n := by
    intro n
    induction n with
    | zero => exact hg1 0
    | succ n ih =>
      rw [hg0, pow_succ]
      exact Nat.mul_le_mul ih (Nat.le_self_pow (by omega) 2)
  have hex : ∃ n, y ≤ g n := ⟨y, (Nat.lt_two_pow_self).le.trans (hg2 y)⟩
  let n := Nat.find hex
  have hn1 : y ≤ g n := Nat.find_spec hex
  have hn2 : g n ≤ c * y := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0]
      exact k13.trans (Nat.le_mul_of_pos_right _ hy)
    · obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have h4 : ¬ y ≤ g k := Nat.find_min hex (by
        show k < n
        omega)
      rw [hk, hg0, mul_comm c y]
      exact Nat.mul_le_mul (by omega) k14
  have hnJ : n ≤ JJ h n := by
    unfold Nc.Tower.JJ
    rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
    exact Nat.mul_le_mul_right _ heeh
  obtain ⟨hG0, -, -, -, hXJ, -, hword⟩ := hC n
  obtain ⟨R⟩ := Nc.Tower.exists_routes (h := h) (n := n) h2 hword
  have hX0 : Fintype.card ((tower h n h2).X 0) = g n := hG0
  have hX0' : Fintype.card (XX h n 0) = g n := hG0
  have hXJ0 : 0 < Fintype.card ((tower h n h2).X (JJ h n)) :=
    Fintype.card_pos_iff.2 ⟨((QuotientGroup.mk 1 : XX h n (JJ h n)))⟩
  refine ⟨JJ h n, (C + 1) * (n + 1) ^ 7, 2 * Fintype.card ((tower h n h2).X 0) * ((C + 1) * (n + 1) ^ 7),
    tower h n h2, R.mono (Nat.mul_le_mul_right _ (by omega)) ?_, towFlag VL h2 n, rfl, ?_, ?_, ?_, ?_, ?_, le_rfl⟩
  · rw [hX0, hX0', ← mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
  · have hlaw : ∀ d : VL.Di, VL.L d ∈ (univ : Finset VL.Di).toList.map VL.L := fun d =>
      List.mem_map.2 ⟨d, Finset.mem_toList.2 (mem_univ d), rfl⟩
    refine ⟨⟨one_pos, by positivity, by omega, by omega, by norm_num, by norm_num, hgain, htwo, ?_⟩, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, hXJ0, ?_, ?_, ?_, ?_, hlaw, ?_⟩
    · intro (f : U h)
      have h4 := npair_sym (⟨0, by omega⟩ : Fin (h - 1)) f
      rcases Sym2.eq_iff.1 h4 with ⟨e1, -⟩ | ⟨e1, -⟩
      · exact ⟨npair ⟨0, by omega⟩ f, Or.inl e1.symm⟩
      · exact ⟨npair ⟨0, by omega⟩ f, Or.inr e1.symm⟩
    · exact k1
    · exact k2
    · omega
    · refine (Fintype.card_congr (Equiv.refl _)).le.trans (?_ : Fintype.card (NN h) ≤ c)
      exact k4
    · exact k5
    · refine (Fintype.card_congr (Equiv.refl _)).le.trans (?_ : Fintype.card VL.Di ≤ c)
      exact k6
    · refine (Fintype.card_congr (Equiv.refl _)).le.trans (?_ : Fintype.card (Sym2 (U h)) ≤ c)
      exact k7
    · intro d
      have h4 : Fintype.card (VL.L d).Sl ≤ ∑ d, Fintype.card (VL.L d).Sl :=
        Finset.single_le_sum (f := fun d => Fintype.card (VL.L d).Sl) (fun _ _ => Nat.zero_le _) (mem_univ d)
      exact h4.trans k8
    · exact hXJ.le.trans k12
    · show √(h : ℝ) * ((1 : ℕ) : ℝ) + √VL.C₁ * VL.a₁ ≤ (c : ℝ)
      exact (Nat.le_ceil _).trans (Nat.cast_le.2 k11)
    · have h4 : (1 : ℝ) / (1 - 1 / 2) = ((2 : ℕ) : ℝ) := by norm_num
      rw [h4]
      exact Nat.cast_le.2 (by omega)
    · omega
    · have h4 : (1 / 2 : ℝ) ^ ee h * (((2 ^ ee h : ℕ) : ℝ)) ^ 1 = 1 := by
        push_cast
        rw [pow_one, ← mul_pow]
        norm_num
      exact h4.le
    · intro L hL
      rw [List.mem_map] at hL
      obtain ⟨d, -, rfl⟩ := hL
      refine ⟨⟨fun i ν => ?_⟩, ?_⟩
      · have h4 : (VL.L d).len i ν ≤ ∑ ν, (VL.L d).len i ν :=
          Finset.single_le_sum (f := fun ν => (VL.L d).len i ν) (fun _ _ => Nat.zero_le _) (mem_univ ν)
        have h5 : ∑ ν, (VL.L d).len i ν ≤ ∑ i, ∑ ν, (VL.L d).len i ν :=
          Finset.single_le_sum (f := fun i => ∑ ν, (VL.L d).len i ν) (fun _ _ => Nat.zero_le _) (mem_univ i)
        have h6 : ∑ i, ∑ ν, (VL.L d).len i ν ≤ ∑ d, ∑ i, ∑ ν, (VL.L d).len i ν :=
          Finset.single_le_sum (f := fun d => ∑ i, ∑ ν, (VL.L d).len i ν) (fun _ _ => Nat.zero_le _) (mem_univ d)
        exact h4.trans (h5.trans (h6.trans k9))
      · have h4 : (VL.L d).lam ≤ ∑ d, (VL.L d).lam :=
          Finset.single_le_sum (f := fun d => (VL.L d).lam) (fun _ _ => Nat.zero_le _) (mem_univ d)
        exact h4.trans k10
  · rw [hX0]; exact hn1
  · rw [hX0]; exact hn2
  · exact Nat.mul_pos (by omega) (by positivity)
  · exact Nat.mul_le_mul k15 (Nat.pow_le_pow_left (by omega) 7)

end Towers

section Thm

variable {F : Type} [CommRing F] {h b D J m Uu AA N M ℓ : ℕ} {T : Tower h b D J 1}

/-- The exponent of the trees of a tower with the constant c. -/
def cTree (c : ℕ) : ℕ := (c + 4) * 200000 + cKap c * (2 * c + 1) + 7 + (4 + (2 * c * c + 1 + c) * c) * 8 +
  (1 + 8 * (c * (2 * c + 1) ^ 7))

open Classical in
/-- The thin trees of one tower. -/
theorem exists_thinTrees (R : Routes T m Uu) (FL : FlagLaws F T) {laws : List (G.Law F)} {c q : ℕ} {ρ : ℝ}
    (hC : TCst FL laws c ρ 1 q) {C : ℕ} (hC0 : cTree c ≤ C) (hm1 : 1 ≤ m)
    (hm : m ≤ c * (J + 1) ^ 7) (hUu : Uu ≤ 2 * Fintype.card (T.X 0) * m) (hM : 2 ≤ M)
    (hX1 : M ≤ Fintype.card (T.X 0)) (hX2 : Fintype.card (T.X 0) ≤ c * M) (hAA : AA ≤ M) (hN : 1 ≤ N) (hℓ : 1 ≤ ℓ) :
    Nonempty (ThinTrees F laws AA N ℓ M b FL.G₁ C (1 / (q : ℝ))) := by
  classical
  obtain ⟨hCc, hC8, hC9⟩ : (c + 4) * 200000 + cKap c * (2 * c + 1) + 7 ≤ C ∧ (4 + (2 * c * c + 1 + c) * c) * 8 ≤ C ∧
      1 + 8 * (c * (2 * c + 1) ^ 7) + 7 ≤ C := by unfold cTree at hC0; omega
  have hH := hC.toTHypR
  have hc := hC.c_pos
  have hl := lg_two hM
  have hJX := two_pow_le (T := T) hC.D_two hC.bot_pos
  have hdep : J + 1 ≤ (2 * c + 1) * lg M := depth_le hJX (hX2.trans (Nat.mul_le_mul_left _ (by omega)))
  have hJ1 : J + 1 ≤ Fintype.card (T.X 0) := Nat.succ_le_of_lt ((Nat.lt_two_pow_self (n := J)).trans_le hJX)
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := tree_nums (N := N) hc hM hN hX2 hJ1 hm
  have hAX : AA ≤ Fintype.card (T.X 0) := hAA.trans hX1
  obtain ⟨ch⟩ := Function.Embedding.nonempty_of_card_le (α := Fin AA) (β := T.X 0) (by rwa [Fintype.card_fin])
  obtain ⟨Pl⟩ := exists_place T ch
  have hkap := kapB_tree (N := N) hX2 hm hdep
  obtain ⟨U1, hU1⟩ : ∃ U1, U1 = capB c m (Fintype.card (T.X 0)) N N * (c + c) + 1 := ⟨_, rfl⟩
  rw [← hU1] at a7
  obtain ⟨W, hW⟩ : ∃ W, W = ((c + 3) * M) ^ 9 := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, V = ((c + 3) * (M * N)) ^ 30 := ⟨_, rfl⟩
  rw [← hW] at a1 a2 a3 a4 a5
  rw [← hV] at a5 a6 a7
  have hcV : c ≤ V := a1.trans a5
  have hMN : 2 ≤ M * N := le_trans hM (Nat.le_mul_of_pos_right _ hN)
  -- loads
  have hq : 0 < q := by have := hC.pq; omega
  have hBh : (BhN FL Uu AA N ρ : ℝ) ≤ ((cKap c * lg M ^ 7 : ℕ) : ℝ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) *
      (N + (M : ℝ) ^ 2) := by
    refine (gain_rpow hq (by omega) hX1 (BhN_le (lh := N) hC hm1 hUu hAX)).trans ?_
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    calc ((2 * c * kapB c m (Fintype.card (T.X 0)) N : ℕ) : ℝ) * (M : ℝ) ^ (-(1 / (q : ℝ))) ≤
        ((cKap c * (lg M ^ 7 * M * (N + M ^ 2)) : ℕ) : ℝ) * (M : ℝ) ^ (-(1 / (q : ℝ))) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hkap) (Real.rpow_nonneg hM0.le _)
      _ = _ := by
          rw [sub_eq_add_neg, Real.rpow_add hM0, Real.rpow_one]
          push_cast
          ring
  have hnode : (((c + 1) * BhN FL Uu AA N ρ : ℕ) : ℝ) ≤
      (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * (N + (M : ℝ) ^ 2) := by
    have h3 : (c + 1) * (cKap c * lg M ^ 7) ≤ lg M ^ C := by
      rw [← mul_assoc]
      refine const_mul_pow_le hl ?_
      calc (c + 1) * cKap c + 7 ≤ (2 * c + 1) * cKap c + 7 := by gcongr; omega
        _ ≤ C := by rw [mul_comm (2 * c + 1)]; omega
    calc (((c + 1) * BhN FL Uu AA N ρ : ℕ) : ℝ) ≤
        ((c + 1 : ℕ) : ℝ) * (((cKap c * lg M ^ 7 : ℕ) : ℝ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * (N + (M : ℝ) ^ 2)) := by
          rw [Nat.cast_mul]
          exact mul_le_mul_of_nonneg_left hBh (Nat.cast_nonneg _)
      _ = (((c + 1) * (cKap c * lg M ^ 7) : ℕ) : ℝ) * (M : ℝ) ^ (1 - 1 / (q : ℝ)) * (N + (M : ℝ) ^ 2) := by
          push_cast; ring
      _ ≤ _ := by gcongr
  have htot : YhN FL Uu AA N ρ ≤ lg M ^ C * M * (N + M ^ 2) := by
    have h1 := YhN_le (lh := N) hC hm1 hUu hAX
    have h2 : cKap c * c * lg M ^ 7 ≤ lg M ^ C := const_mul_pow_le hl (by
      have : cKap c * c ≤ cKap c * (2 * c + 1) := Nat.mul_le_mul_left _ (by omega)
      omega)
    calc YhN FL Uu AA N ρ ≤ 2 * c * kapB c m (Fintype.card (T.X 0)) N * c := h1
      _ ≤ cKap c * (lg M ^ 7 * M * (N + M ^ 2)) * c := Nat.mul_le_mul_right _ hkap
      _ = cKap c * c * lg M ^ 7 * M * (N + M ^ 2) := by ring
      _ ≤ _ := by gcongr
  have hne : ∀ p, p ≠ Pl.pt none → Pl.pt.symm p ≠ none := fun p hp e => hp (by
    rw [← Equiv.apply_symm_apply Pl.pt p, e])
  have hV3 : 3 ≤ V := hV ▸ (le_trans (Nat.le_add_left 3 c)
    (Nat.le_mul_of_pos_right (c + 3) (show 0 < M * N by omega))).trans (Nat.le_self_pow (by norm_num) _)
  obtain ⟨steps, inp, H, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := tree_computed (R := R) (FL := FL)
    (Pl := Pl) (U1 := U1) (N := N) hH (V := V) hV3 (by omega) (by omega) (hC.h_le.trans hcV) (hC.r_le.trans hcV)
    (by omega) (by omega) (hC.di_le.trans hcV) (hC.b_le.trans hcV) (hC.fl_le.trans hcV)
    (fun d => (hC.sl_le d).trans hcV) a6 a7 (by have := hC.D_two; omega)
  refine ⟨{
    A' := extra T AA
    E := Fintype.card (Mv T R ch FL)
    U1 := U1
    sys := sys R FL Pl
    plan := Tow.plan R FL Pl N N U1
    stage := fun p => ndStage (Pl.pt.symm p)
    depth := J + 1
    root := Pl.pt none
    par := treePar R FL Pl hH.h_pos
    dead := deadU R FL Pl N
    isLaw := fun x => (eE R FL x).isRight
    depth_le := hdep.trans ((le_of_eq (by rw [pow_one])).trans (const_mul_pow_le hl (show 2 * c + 1 + 1 ≤ C by omega)))
    stage_le := fun p => ?_
    stage_given := fun a => by rw [← Pl.pt_base, Equiv.symm_apply_apply]; rfl
    stage_root := fun p => by rw [ndStage_eq_top, Equiv.symm_apply_eq]
    stage_par := fun n o p hp => by
      rw [treePar, Equiv.symm_apply_apply]
      exact ndStage_par _ _ (hne p hp)
    children_le := fun n o x hx => by
      have := card_treeChildren (R := R) (FL := FL) (Pl := Pl) hH.h_pos n o x
      rwa [if_neg hx] at this
    root_children_le := fun n o => by
      have := card_treeChildren (R := R) (FL := FL) (Pl := Pl) hH.h_pos n o (Pl.pt none)
      rw [if_pos rfl] at this
      exact this.trans (hC.bot.trans (by omega))
    dead_le := fun o => ?_
    kinds := fun x => ?_
    law_stage := fun r' hr' => ?_
    U1_pos := by rw [hU1]; exact Nat.succ_pos _
    cap := capN FL N Uu AA N
    ok := plan_ok_cap hH.r_pos hH.b_pos hH.h_pos hH.bD hH.ρ_pos hH.ρ_lt hH.gain hH.two
    up := treeUp R FL Pl
    good_iff := fun n o x => ?_
    poss_good := fun n o x hp => thm_tree_poss_good hℓ n o x hp
    edge := fun n hv o hg u hu => ?_
    node_le := fun n hv o hg p => ?_
    total_le := fun n hv o hg => ?_
    between_le := fun n hv o hg p hp => tree_between hH (valid_of n hv) hg hp
    up_node := fun n hv o hg p => ?_
    up_total := fun n hv o hg => ?_
    copies_le := fun n hv o hg p => ?_
    layers_le := fun n o hg p => layers_le_seen hH n o hg p
    value := fun n hv tab => tree_value hH hℓ (capN_capB hC hm1 hUu hAX) (fun d => hC.len _ (hC.mem d)) hc hU1 tab
    computed := ?_ }⟩
  · rcases Pl.pt.symm p with _ | ⟨j, x⟩
    · exact le_rfl
    · exact Nat.le_of_lt (show j.1 < J + 1 from j.2)
  · obtain ⟨n1', -⟩ := cards_le (R := R) (ch := ch) (FL := FL) (Pl := Pl) (U0 := 0) (U1 := 0)
      (show 0 < D by have := hC.D_two; omega) hC.b_pos (show 1 ≤ W by omega) (hC.h_le.trans a1) (hC.r_le.trans a1) a2
      (show J ≤ W by omega) (show AA ≤ W by omega) a3 (hC.di_le.trans a1) (hC.b_le.trans a1)
      (fun d => (hC.sl_le d).trans a1) (Nat.zero_le _) (Nat.zero_le _)
    refine (card_image_le.trans (le_of_eq card_univ)).trans (n1'.trans ?_)
    rw [hW, ← pow_mul]
    calc 17 * ((c + 3) * M) ^ (9 * 6) ≤ ((c + 3) * M) ^ 3 * ((c + 3) * M) ^ (9 * 6) := by
          refine Nat.mul_le_mul_right _ ?_
          have := Nat.pow_le_pow_left (le_trans (Nat.le_add_left 3 c) (Nat.le_mul_of_pos_right (c + 3) (show 0 < M by omega))) 3
          omega
      _ = ((c + 3) * M) ^ 57 := by rw [← pow_add]
      _ ≤ M ^ C := const_pow_le hM (by omega)
  · change if (eE R FL x).isRight = true then kindM R ch FL (eE R FL x) ∈ laws else kindM R ch FL (eE R FL x) = relay F
    rcases eE R FL x with y | l
    · simp [kindM]
    · simp only [Sum.isRight_inr, if_true]
      exact hC.mem _
  · change 0 < ndStage (Pl.pt.symm (Pl.pt (partM R ch FL (eE R FL r'.1) r'.2)))
    rw [Equiv.symm_apply_apply]
    have key : ∀ mv : Mv T R ch FL, mv.isRight = true → ∀ ro, 0 < ndStage (partM R ch FL mv ro) := by
      rintro (y | l) hl ro
      · simp at hl
      · exact Nat.succ_pos _
    exact key _ hr' _
  · have e : ∀ ν : (kindM R ch FL (eE R FL x)).Cn, oo R FL Pl o ⟨eE R FL x, ν⟩ = (o ⟨x, ν⟩ : ℕ) := fun ν => by
      unfold oo
      have h1 : (eN R FL Pl).symm ⟨eE R FL x, ν⟩ = ⟨x, ν⟩ := by
        rw [Equiv.symm_apply_eq]
        rfl
      rw [h1]
    change GoodMv R ch FL N (nn n) (oo R FL Pl o) (eE R FL x) ↔ if (eE R FL x).isRight = true then
      b * ∑ ν : (kindM R ch FL (eE R FL x)).Cn, (o ⟨x, ν⟩).val ^ 2 ≤
          FL.G₁ * num R ch FL N (nn n) (oo R FL Pl o) (eE R FL x) ^ 2 ∧
        ∀ ν : (kindM R ch FL (eE R FL x)).Cn, num R ch FL N (nn n) (oo R FL Pl o) (eE R FL x) ≤ (o ⟨x, ν⟩ : ℕ)
      else ∀ ν : (kindM R ch FL (eE R FL x)).Cn, (o ⟨x, ν⟩).val = num R ch FL N (nn n) (oo R FL Pl o) (eE R FL x)
    simp only [← e]
    clear e
    generalize eE R FL x = mv
    rcases mv with y | l
    · exact Iff.rfl
    · simp only [Sum.isRight_inr, if_true, GoodMv, GoodL, Nat.one_mul]
      rfl
  · obtain ⟨hu, hl'⟩ := mem_filter.1 hu
    obtain ⟨hu, hd⟩ := mem_sdiff.1 hu
    obtain ⟨s, -, hs⟩ := cur_tree hH (valid_of n hv) hg hu hd hl'
    exact ⟨_, fun e => Option.some_ne_none s (Pl.pt.injective e), hs⟩
  · -- the units at one node
    exact (Nat.cast_le.2 (tree_node_le (R := R) (FL := FL) (Pl := Pl) hH (valid_of n hv) hg hC.b_le hC.bot p)).trans hnode
  · -- all units
    exact (tree_total_le hH (valid_of n hv) hg).trans htot
  · exact (Nat.cast_le.2 (tree_up_node hH n o hC.b_le hC.bot p)).trans hnode
  · exact (tree_up_total hH n o).trans htot
  · -- copies
    refine (thm_tree_copies (R := R) (FL := FL) (Pl := Pl) hH hv hg hC.sl_le p).trans ?_
    refine Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_right _ ?_) ?_) (Nat.mul_le_mul_right _ (by omega))
    · refine le_trans ?_ hC8
      have a1 := hC.nr_le
      have a2 := hC.g_le
      have a3 := hC.di_le
      gcongr
    · split_ifs
      · refine Nat.mul_le_mul_right _ ?_
        have h1 : 1 ≤ lg M ^ 7 := Nat.one_le_pow _ _ (by omega)
        calc 1 + 8 * m ≤ lg M ^ 7 + 8 * (c * ((2 * c + 1) ^ 7 * lg M ^ 7)) :=
              Nat.add_le_add h1 (Nat.mul_le_mul_left _ (m_le hm hdep))
          _ = (1 + 8 * (c * (2 * c + 1) ^ 7)) * lg M ^ 7 := by ring
          _ ≤ lg M ^ C := const_mul_pow_le hl hC9
      · exact le_rfl
  · -- the program
    have hpow : ∀ e, e ≤ 200000 → ((c + 3) * (M * N)) ^ e ≤ (M * N) ^ C := fun e he =>
      const_pow_le hMN ((Nat.mul_le_mul_left _ he).trans (by omega))
    have hG3 : 3 ≤ (c + 3) * (M * N) :=
      le_trans (Nat.le_add_left 3 c) (Nat.le_mul_of_pos_right (c + 3) (show 0 < M * N by omega))
    obtain ⟨G, hG⟩ : ∃ G, G = (c + 3) * (M * N) := ⟨_, rfl⟩
    rw [← hG] at hV hpow hG3
    have hYG : 20 * V ^ 9 ≤ G ^ 273 := by
      rw [hV, ← pow_mul]
      calc 20 * G ^ (30 * 9) ≤ G ^ 3 * G ^ (30 * 9) := Nat.mul_le_mul_right _ (by
            have := Nat.pow_le_pow_left hG3 3; omega)
        _ = G ^ 273 := by rw [← pow_add]
    have hyp : 20 * V ^ 9 ≤ (M * N) ^ C := hYG.trans (hpow 273 (by norm_num))
    refine ⟨_, steps, inp, H, ?_, ?_, ?_, b2.trans hyp, ?_, b3.trans hyp, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩
    · refine (Nat.pow_le_pow_left hYG 4).trans ?_
      rw [← pow_mul]
      exact hpow _ (by norm_num)
    · refine b0.trans ?_
      calc 3 * (20 * V ^ 9) ^ 16 ≤ G * (G ^ 273) ^ 16 := Nat.mul_le_mul hG3 (Nat.pow_le_pow_left hYG 16)
        _ = G ^ 4369 := by rw [← pow_mul, ← pow_succ']
        _ ≤ _ := hpow _ (by norm_num)
    · rw [card_party Pl]
      exact b1.trans hyp
    · refine a7.trans (le_trans ?_ hyp)
      have : V ≤ V ^ 9 := Nat.le_self_pow (by norm_num) V
      omega

/-- **Paper: Theorem thm:tree.** "There is a constant C with the following property. Let M ≥ 2, let ℓ, N ≥ 1, and let a
network over an A-algebra have at most M nodes, no unit from a node to itself, and at most N units at each node. Its
value is the sum, over a set of choices o (sequences of good outcomes), of values of networks with the following
properties. Put Λ = (lg M)^C, where lg M = ⌊log M⌋+1, and γ = 1/log b. (a) The nodes form a rooted tree of depth at most
Λ, by stages: the given nodes are of stage 0, every node but the root has its parent in the next stage and at most b
children, and the root has at most C. (b) A set of at most M^C dead units may join any two nodes. All others join a node
and its parent; their number is at most ΛM^(1−γ)(N+M²) for one node, its children included, and ΛM(N+M²) in all. (c)
The table of a node is the given one (or 1) times the tables of the moves at it, summed over the units that they have
used up. At stage 0 these are tests only; elsewhere they are tests and table entries of laws, and the numbers of
layers of the law moves at a node add up to at most the number of bits of all units that it ever holds. (d) The parents,
the units present, the units and numbers of the moves, and which outcomes are good are computed from o and the given
numbers of units by a straight-line program with at most (MN)^C steps on numbers below (MN)^C. A step is an input, a
constant, or an arbitrary function of two earlier results, given by its table (a binary operation). The program does not
depend on the numbers of units, the outcomes or the tables." The tests are relays, and the laws are the fixed list, mapped to R. A move of num
units uses num·ℓ layers, so (c) is stated as num summed over the law moves at a node against the units ever seen at it
(seenAt). Units from a node to itself are also allowed: they stay, and their node sums over them (the printed formula is
the case without them, cutUnits_id_cur). The operations of (d) are those of a straight-line program that may depend on M, N and ℓ. -/
theorem thm_tree {A : Type} [CommRing A] {h : ℕ} [NeZero h]
    (VL : VLaws A (cNear (h := h)) (dNear (h := h)) 1 (2 ^ ee h)) (h3 : 3 ≤ h)
    (hgain : 1 + 8 * VL.C₁ ≤ (h : ℝ) / 4) :
    ∃ C : ℕ, ∀ (R : Type) [CommRing R] [Algebra A R] (M AA N ℓ : ℕ), 2 ≤ M → AA ≤ M → 1 ≤ N → 1 ≤ ℓ →
      Nonempty (ThinTrees R (((univ : Finset VL.Di).toList.map VL.L).map (lawMap (algebraMap A R))) AA N ℓ M
        (2 ^ ee h) (goodBound VL.C₁ VL.a₁) C (1 / Real.logb 2 ((2 ^ ee h : ℕ) : ℝ))) := by
  have he : 2 ≤ ee h := by
    unfold Nc.Tower.ee
    have : 3 * 2 ≤ h * (h - 1) := Nat.mul_le_mul h3 (by omega)
    omega
  have htwo : (2 : ℝ) ≤ 1 / 2 * ((2 ^ ee h : ℕ) : ℝ) := by
    have : (4 : ℝ) ≤ ((2 ^ ee h : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (show 0 < 2 by norm_num) he
    linarith
  obtain ⟨c, hc⟩ := tree_towers
    { VL with
      G₁ := goodBound VL.C₁ VL.a₁
      G₁_le := Nat.floor_le (by have := VL.C₁_nonneg; positivity)
      L2 := fun d i => (VL.L2 d i).trans (Nat.le_floor VL.G₁_le) } h3 (by linarith) htwo
  refine ⟨cTree c, fun R _ _ M AA N ℓ hM hAA hN hℓ => ?_⟩
  obtain ⟨J, m, Uu, T, Rt, FL, hG, hC, hX1, hX2, hm1, hm2, hUu⟩ := hc M (by omega)
  have e : Real.logb 2 ((2 ^ ee h : ℕ) : ℝ) = (ee h : ℝ) := by
    push_cast
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  simp only [] at hG
  rw [e, ← hG]
  exact exists_thinTrees Rt (flagMap (algebraMap A R) FL) (TCst_map _ hC) le_rfl hm1 hm2 hUu hM hX1 hX2 hAA hN hℓ

end Thm

end Paper
