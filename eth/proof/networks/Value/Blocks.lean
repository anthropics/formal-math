/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Value.Words
import all StepMachines.Prog.NetVal

/-! # The strings on the edges of the clique of the groups, block by block

Proof of Lemma 1, paragraph «The algorithm». This file proves four of the statements of
proof/networks/Value/Defs.lean:
* `stLayout`: «In this order, the pair {a, b} is assigned a block of c_{a,b} consecutive positions
  of {1, …, L}; the L − Y_{γ,γ'} positions after the last block hold the appended bits»;
* `stSameBlock`: «both W̃_γ and W̃_γ' read θ_{a,b} from the same block of this string, so θ_{a,b} =
  θ_{b,a}»;
* `stAppendedZero`: «the appended bits must be 0»;
* `stBlocks`: the strings of L bits on the edges whose appended bits are 0 are the choices of «one
  string θ_{a,b} ∈ {0,1}^{c_{a,b}} per pair {a,b} of nodes in different groups».
The last is proved edge by edge (`edge_unique`): the strings of L bits on one edge {γ, γ'} with
appended bits 0 are the choices of one block per pair (a, b), a ∈ G_γ, b ∈ G_γ' (`NetE.sum_mdec`:
cut the string into its blocks; back: write the blocks one after the other and append zeros).
`NetE.sum_mdec` is not public in proof/machines/StepMachines/Prog/NetVal.lean; the line
`import all StepMachines.Prog.NetVal` is there only to reach it. -/

public section

namespace Value

open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping

/-- «For each pair of groups {γ, γ'} choose an order of the pairs {a, b} … In this order, the pair
{a, b} is assigned a block of c_{a,b} consecutive positions of {1, …, L}; the L − Y_{γ,γ'} positions
after the last block hold the appended bits.» -/
theorem stLayout : StLayout := by
  intro C _ g K Np c hK0 x Θ a b hab
  have hmem : (a.val, b.val) ∈ prs K g x (Paper.grouping hK0 x a).val (Paper.grouping hK0 x b).val := by
    simp [prs, members, chi]
  have key : ∀ θ : List Bool, mdec K g Np.toPaperNetwork c x (Paper.grouping hK0 x a) (Paper.grouping hK0 x b) θ (a, b) =
      (θ.drop (((lbLens K g Np.toPaperNetwork c x (Paper.grouping hK0 x a).val (Paper.grouping hK0 x b).val).take ((prs K g x (Paper.grouping hK0 x a).val (Paper.grouping hK0 x b).val).idxOf (a.val, b.val))).sum)).take (Np.cap c a.val b.val) :=
    fun θ => getD_chunks_map (fun p : ℕ × ℕ => Np.cap c p.1 p.2) _ θ [] hmem
  refine ⟨?_, ?_, fun θ => ?_⟩
  · unfold thetaAt
    rw [min_eq_left hab.le, max_eq_right hab.le, if_pos hab]
    exact key _
  · unfold thetaAt
    rw [min_eq_right hab.le, max_eq_left hab.le, if_neg hab.not_gt]
    exact key _
  · unfold appendedBits
    rw [min_eq_left hab.le, max_eq_right hab.le]
    rfl

/-- «both W̃_γ and W̃_γ' read θ_{a,b} from the same block of this string, so θ_{a,b} = θ_{b,a}». -/
theorem stSameBlock : StSameBlock := by
  intro C _ g K Np c hK0 x Λ a b hne
  exact thetaAt_comm Np.toPaperNetwork c hK0 x _ _ hne (star_swap Λ _ _)

/-- «the appended bits must be 0»: otherwise the factor [all appended bits are 0] of one of the
tables is 0. -/
theorem stAppendedZero : StAppendedZero := by
  intro C _ g K Np c N hK0 x Λ h
  obtain ⟨γ, hγ⟩ := not_forall.1 h
  refine Finset.prod_eq_zero (Finset.mem_univ γ) ?_
  unfold display
  rw [if_neg hγ, zero_mul]

variable {C : Type} [HasSize C] {g K : ℕ}

/-- «so θ_{a,b} = θ_{b,a}»: whichever of the two tables reads it, the string that is read for the
nodes a, b in different groups is the one that `readBlocks` has at the pair {a, b}. -/
theorem thetaAt_eq_readBlocks (hSB : StSameBlock) (Np : Procs C) (c : C) (hK0 : 0 < K) (x : ℕ) (Λ : Fin K × Fin K → List Bool) {a b : Fin g}
    (hne : Paper.grouping hK0 x a ≠ Paper.grouping hK0 x b) :
    thetaAt Np.toPaperNetwork c hK0 x (star Λ (Paper.grouping hK0 x a)) a b = readBlocks Np c hK0 x Λ (pr a b) := by
  have hab : a ≠ b := fun e => hne (e ▸ rfl)
  rcases lt_or_gt_of_ne hab with h | h
  · rw [(pr_of_lt h).1]
    exact (if_pos ⟨h, hne⟩).symm
  · rw [(pr_of_lt h).2, hSB C g K Np c hK0 x Λ a b hne]
    exact (if_pos ⟨h, hne.symm⟩).symm

variable {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}

/-- «θ_{a,b} ∈ {0,1}^{c_{a,b}}»: what the tables read from one string of L bits per edge is a choice
of one string of c_{a,b} bits per pair {a, b} of nodes in different groups. -/
theorem readBlocks_mem (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (x L : ℕ) (hL : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L)
    {Λ : Fin K × Fin K → List Bool} (hΛ : Λ ∈ edgeStrings K L) : readBlocks Np c hK0 x Λ ∈ blockStrings N (Paper.grouping hK0 x) := by
  refine (mem_tuples _ _ _ _).2 fun p => ⟨fun hp => ?_, fun hp => if_neg hp⟩
  have hlen := length_thetaAt Np.toPaperNetwork hK0 (Table.isPaperNetwork h) x L (fun γ γ' hne => by
    rw [Groundwork.Network.merge_c]
    exact hL γ γ' hne) (star Λ (Paper.grouping hK0 x p.1)) hp.2 (mem_words.1 (((mem_tuples _ _ _ _).1 (star_mem hΛ _) _).1 hp.2.symm))
  rw [mem_words]
  exact (congrArg List.length (if_pos hp)).trans hlen

omit [HasSize C] in
/-- A string θ_{a,b} of a choice of blocks has as many bits as the procedures say, whichever of a, b
is the smaller. -/
theorem length_blockString (h : IsNetworkP Np c N P B τ S) {χ : Fin g → Fin K} {θ : Fin g × Fin g → List Bool} (hθ : θ ∈ blockStrings N χ) {a b : Fin g} (hne : χ a ≠ χ b) :
    (θ (pr a b)).length = Np.cap c a b := by
  have hab : a ≠ b := fun e => hne (e ▸ rfl)
  rw [h.given.cap_eq a b hab]
  rcases lt_or_gt_of_ne hab with h' | h'
  · rw [(pr_of_lt h').1]
    exact mem_words.1 (((mem_tuples _ _ _ _).1 hθ (a, b)).1 ⟨h', hne⟩)
  · rw [(pr_of_lt h').2, h.is.c_symm a b]
    exact mem_words.1 (((mem_tuples _ _ _ _).1 hθ (b, a)).1 ⟨h', hne.symm⟩)

omit [HasSize C] in
/-- The strings of L bits whose bits after the last block are 0. -/
theorem mem_mD_iff (Nq : PNet C) (c : C) (x L : ℕ) (G G' : Fin K) (w : List Bool) :
    w ∈ mD K g Nq c x L G G' ↔ w.length = L ∧ ∀ bit ∈ w.drop (lbLen K g Nq c x G G'), bit = false := by
  simp [mD]

omit [HasSize C] in
/-- One edge of the clique of the groups, given by the group indices G, G' (in either order): for
every choice of one string t(a, b) of c_{a,b} bits per pair (a, b), a in group G, b in group G',
exactly one string of L bits has these strings in its blocks and zeros after the last block. -/
theorem edge_unique (Nq : PNet C) (hK0 : 0 < K) (c : C) (x L : ℕ) (G G' : Fin K) (hle : lbLen K g Nq c x G G' ≤ L) (t : Fin g × Fin g → List Bool)
    (ht : ∀ q : Fin g × Fin g, Paper.grouping hK0 x q.1 = G ∧ Paper.grouping hK0 x q.2 = G' → (t q).length = Nq.cap c q.1 q.2) :
    ∃! w : List Bool, w ∈ mD K g Nq c x L G G' ∧ ∀ q : Fin g × Fin g, Paper.grouping hK0 x q.1 = G ∧ Paper.grouping hK0 x q.2 = G' → mdec K g Nq c x G G' w q = t q :=
  existsUnique_of_sum _ _ _ (sum_mdec Nq hK0 c x L G G' hle) (fun t' => ∀ q : Fin g × Fin g, Paper.grouping hK0 x q.1 = G ∧ Paper.grouping hK0 x q.2 = G' → t' q = t q)
    (existsUnique_tuple _ _ _ t fun q hq => mem_words.2 (ht q hq))

/-- What the choice θ of blocks asks of the string w at the place p = (γ, γ') of a choice of one
string per edge: for γ < γ', w has L bits, zeros after the last block, and θ_{a,b} in the block of
(a, b) for all a ∈ G_γ, b ∈ G_γ'; at all other places w is empty. -/
abbrev EdgeReads (Np : Procs C) (c : C) (hK0 : 0 < K) (x L : ℕ) (θ : Fin g × Fin g → List Bool) (p : Fin K × Fin K) (w : List Bool) : Prop :=
  (p.1 < p.2 → w ∈ mD K g Np.toPaperNetwork c x L p.1 p.2 ∧
    ∀ q : Fin g × Fin g, Paper.grouping hK0 x q.1 = p.1 ∧ Paper.grouping hK0 x q.2 = p.2 → mdec K g Np.toPaperNetwork c x p.1 p.2 w q = θ (pr q.1 q.2)) ∧ (¬ p.1 < p.2 → w = [])

/-- The three conditions on Λ (one string of L bits per edge; all appended bits are 0; the tables
read θ from Λ), said edge by edge. The hypothesis `hSB` says that the two tables at an edge read the
same block. -/
theorem blocks_iff (hSB : StSameBlock) (Np : Procs C) (c : C) (hK0 : 0 < K) (x L : ℕ) {θ : Fin g × Fin g → List Bool} (hθ : θ ∈ blockStrings N (Paper.grouping hK0 x)) (Λ : Fin K × Fin K → List Bool) :
    (Λ ∈ edgeStrings K L ∧ AppendedZero g Np c x Λ ∧ readBlocks Np c hK0 x Λ = θ) ↔ ∀ p, EdgeReads Np c hK0 x L θ p (Λ p) := by
  have hread : ∀ a b : Fin g, Paper.grouping hK0 x a < Paper.grouping hK0 x b →
      readBlocks Np c hK0 x Λ (pr a b) = mdec K g Np.toPaperNetwork c x (Paper.grouping hK0 x a) (Paper.grouping hK0 x b) (Λ (Paper.grouping hK0 x a, Paper.grouping hK0 x b)) (a, b) := by
    intro a b hab
    rw [← thetaAt_eq_readBlocks hSB Np c hK0 x Λ hab.ne]
    unfold thetaAt Groundwork.star pr
    rw [min_eq_left hab.le, max_eq_right hab.le, if_pos hab]
  constructor
  · rintro ⟨hΛ, hA, hR⟩ p
    refine ⟨fun hp => ⟨(mem_mD_iff _ _ _ _ _ _ _).2 ⟨mem_words.1 (((mem_tuples _ _ _ _).1 hΛ p).1 hp), ?_⟩, ?_⟩, fun hp => ((mem_tuples _ _ _ _).1 hΛ p).2 hp⟩
    · have h1 := hA p.1 p.2 hp.ne'
      unfold appendedBits Groundwork.star pr at h1
      rw [min_eq_left hp.le, max_eq_right hp.le] at h1
      exact h1
    · rintro q ⟨h1, h2⟩
      have h3 := hread q.1 q.2 (by rw [h1, h2]; exact hp)
      rw [h1, h2, hR] at h3
      exact h3.symm
  · intro H
    have HH : ∀ γ γ' : Fin K, γ < γ' → Λ (γ, γ') ∈ mD K g Np.toPaperNetwork c x L γ γ' ∧
        ∀ a b : Fin g, Paper.grouping hK0 x a = γ → Paper.grouping hK0 x b = γ' → mdec K g Np.toPaperNetwork c x γ γ' (Λ (γ, γ')) (a, b) = θ (pr a b) :=
      fun γ γ' h => ⟨((H (γ, γ')).1 h).1, fun a b h1 h2 => ((H (γ, γ')).1 h).2 (a, b) ⟨h1, h2⟩⟩
    refine ⟨(mem_tuples _ _ _ _).2 fun p => ⟨fun hp => mem_words.2 ((mem_mD_iff _ _ _ _ _ _ _).1 ((H p).1 hp).1).1, (H p).2⟩, ?_, ?_⟩
    · intro γ γ' hne
      exact ((mem_mD_iff _ _ _ _ _ _ _).1 (HH _ _ (min_lt_max.2 hne.symm)).1).2
    · funext q
      by_cases hq : Across (Paper.grouping hK0 x) q
      · rcases lt_or_gt_of_ne hq.2 with h | h
        · have h1 := (hread q.1 q.2 h).trans ((HH _ _ h).2 q.1 q.2 rfl rfl)
          rw [(pr_of_lt hq.1).1] at h1
          exact h1
        · have h1 := (hread q.2 q.1 h).trans ((HH _ _ h).2 q.2 q.1 rfl rfl)
          rw [(pr_of_lt hq.1).2] at h1
          exact h1
      · exact (if_neg hq).trans (((mem_tuples _ _ _ _).1 hθ q).2 hq).symm

/-- The choices of one string of L bits per edge {γ, γ'} with all appended bits 0 are the choices of
«one string θ_{a,b} ∈ {0,1}^{c_{a,b}} per pair {a,b} of nodes in different groups». -/
theorem stBlocks : StBlocks := by
  intro C _ g K hK0 Np c N P B τ S h x L hL
  refine ⟨fun Λ hΛ _ => readBlocks_mem h hK0 x L hL hΛ, fun θ hθ => ?_⟩
  refine (existsUnique_congr fun Λ => blocks_iff stSameBlock Np c hK0 x L hθ Λ).2 (existsUnique_pi _ fun p => ?_)
  by_cases hp : p.1 < p.2
  · obtain ⟨w, hw, hu⟩ := edge_unique Np.toPaperNetwork hK0 c x L p.1 p.2 (by
      rw [Table.lbLen_eq_Y h hK0 x hp.ne]
      exact hL _ _ hp.ne) (fun q => θ (pr q.1 q.2)) fun q hq => length_blockString h hθ (by
        rw [hq.1, hq.2]
        exact hp.ne)
    exact ⟨w, ⟨fun _ => hw, fun hn => absurd hp hn⟩, fun w' hw' => hu w' (hw'.1 hp)⟩
  · exact ⟨[], ⟨fun h' => absurd h' hp, fun _ => rfl⟩, fun w' hw' => hw'.2 hp⟩

end Value
