/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSat.Interfaces
public import SparsifyWidthK.ProgMain
public import SparsifyWidthK.SetAlg
public import SparsifyWidthK.Step
public import SparsifyWidthK.Thresholds
public import SparsifyWidthK.Refine
import Mathlib.Tactic.Ring

/-! # The sparsification lemma for counting, for the program on pairs

This file proves `StProgC`, one of the interface statements of
proof/consequences/CountKSat/Interfaces.lean. It is the sparsification lemma in the counting form of
Dell, Husfeldt, Marx,
Taslaman and Wahlén (arXiv 1206.1775, Appendix A), with the unit clauses {¬ω}, ω ∈ H, kept on a side
list as in Appendix C of the paper (H, called the heart here, is the set of literals on which a step
branches).
The side list starts with the n clauses xᵢ ∨ ¬xᵢ, so that every variable below n occurs in every
leaf. The tree of `stepC` below the root has few leaves, the formula of every leaf has few clauses
and contains
every variable below n, the counts of the leaves add up to the count of ψ, and the stack of the
depth-first walk stays small. The lemmas on trees of
proof/machines/StepMachines/Math/SparsifyTree.lean are applied to pairs (formula, side list). The
invariant is that of
proof/sparsification/SparsifyWidthK/ProgMain.lean for the formula, together with a bound on the side
list. The facts on finite sets, the thresholds and the refinement of the
program are those proved in proof/sparsification/SparsifyWidthK. That the counts of the two children
of a node add up (`StStepCount`), that the root has the count of ψ
(`StRootCount`) and that such a quantity is the sum over the leaves (`StSumLeaves`) are taken as
hypotheses; they are interface statements too.
The proof of `sparsifiesC_of` follows that of `sparsify_prog_of` in
proof/sparsification/SparsifyWidthK/ProgMain.lean. -/

@[expose] public section

namespace CountKSat

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog

namespace ProgC

/-! ### The invariant on pairs -/

variable {θ : ℕ → ℕ} {k D T q leafB : ℕ} {Ok : Finset (Finset PLit) → Prop}
  {Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop}

/-- What holds of the side list after p steps: at most n + k·p clauses, each of at most 2 literals
on variables below n, among them all xᵢ ∨ ¬xᵢ. -/
def SideOK (n k : ℕ) (X : PFml) (p : ℕ) : Prop :=
  X.length ≤ n + k * p ∧ (∀ C ∈ X, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ taut n, C ∈ X

/-- The invariant of the counting tree: the invariant of `WidthK.ProgMain` for the formula, and
`SideOK` for the side list. -/
def GC (Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop) (ψ : PFml) (n k : ℕ) (x : CNode) (p t : ℕ) : Prop :=
  ProgMain.G Node ψ x.1 p t ∧ SideOK n k x.2 p

/-- The clauses of the formula of a node have at most k literals, on variables below n. -/
theorem clause_of_G (hI : Iface θ k D T q leafB Ok Node) {n : ℕ} {ψ : PFml} (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n)
    {s : PFml} {p t : ℕ} (hG : ProgMain.G Node ψ s p t) : ∀ C ∈ s, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n := by
  intro C hC
  obtain ⟨X₀, hX₀, hsub⟩ := hI.clause _ _ _ _ hG.2 _ (ProgMain.mem_toFin.2 ⟨C, hC, rfl⟩)
  obtain ⟨C₀, hC₀, rfl⟩ := ProgMain.mem_toFin.1 hX₀
  refine ⟨?_, fun l hl => (hψ C₀ hC₀).2 l (List.mem_toFinset.1 (hsub (List.mem_toFinset.2 hl)))⟩
  rw [← List.toFinset_card_of_nodup (hG.1.1 C hC)]
  exact (card_le_card hsub).trans ((List.toFinset_card_le C₀).trans (hψ C₀ hC₀).1)

/-- A heart that the search finds has at most k literals, on variables below n. -/
theorem pick_spec (hθ : ∀ i, 1 ≤ θ i) (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {n : ℕ} {ψ : PFml}
    (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) {s : PFml} {p t : ℕ} (hG : ProgMain.G Node ψ s p t) {H : PCl} {P : PFml}
    (hp : pickK θ k s = some (H, P)) :
    H.length ≤ k ∧ ∀ l ∈ H, l.1 < n := by
  obtain ⟨j, hrule, -, -, hH⟩ := hR.some s H P hG.1 hp
  refine ⟨?_, ?_⟩
  · rw [← List.toFinset_card_of_nodup hH]
    exact (hrule.heart.2.1.le).trans hrule.le
  · intro l hl
    obtain ⟨X, hX⟩ := SetAlg.exists_over hθ hrule.heart
    obtain ⟨hXF, -, hsub⟩ := SetAlg.mem_over.1 hX
    obtain ⟨C, hC, rfl⟩ := ProgMain.mem_toFin.1 hXF
    exact (clause_of_G hI hψ hG C hC).2 l (List.mem_toFinset.1 (hsub (List.mem_toFinset.2 hl)))

/-- The two children of a step of the counting tree, written out. -/
theorem stepC_some {x l h : CNode} (hst : stepC θ k x = some (l, h)) :
    ∃ H P, pickK θ k x.1 = some (H, P) ∧ l = (addP [H] x.1, x.2) ∧ h = (addP P x.1, negU H ++ x.2) := by
  obtain ⟨⟨H, P⟩, hp, he⟩ := Option.map_eq_some_iff.1 hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  exact ⟨H, P, hp, rfl, rfl⟩

/-- Both children of a node satisfy `GC` with one more step (p + 1); the second child h, which gets
the shortened clauses P and, on its side list, the negations of the literals of H, also has its
counter t raised by q (t + q). -/
theorem GC_step (hθ : ∀ i, 1 ≤ θ i) (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {n : ℕ} (ψ : PFml)
    (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) (x : CNode) (p t : ℕ) (l h : CNode) (hG : GC Node ψ n k x p t)
    (hst : stepC θ k x = some (l, h)) : GC Node ψ n k l (p + 1) t ∧ GC Node ψ n k h (p + 1) (t + q) := by
  obtain ⟨H, P, hp, rfl, rfl⟩ := stepC_some hst
  obtain ⟨hHk, hHn⟩ := pick_spec hθ hI hR hψ hG.1 hp
  obtain ⟨g1, g2⟩ := ProgMain.G_step hI hR ψ x.1 p t (addP [H] x.1) (addP P x.1) hG.1 (by simp [stepK, hp])
  obtain ⟨s1, s2, s3⟩ := hG.2
  refine ⟨⟨g1, ?_, s2, s3⟩, ⟨g2, ?_, ?_, ?_⟩⟩
  · show x.2.length ≤ n + k * (p + 1)
    rw [Nat.mul_succ]; omega
  · show (negU H ++ x.2).length ≤ n + k * (p + 1)
    rw [List.length_append, negU, List.length_map, Nat.mul_succ]; omega
  · intro C hC
    rcases List.mem_append.1 hC with hC | hC
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hC
      refine ⟨by simp, fun b hb => ?_⟩
      obtain rfl : b = (a.1, !a.2) := by simpa using hb
      exact hHn a ha
    · exact s2 C hC
  · exact fun C hC => List.mem_append_right _ (s3 C hC)

/-- There are n clauses xᵢ ∨ ¬xᵢ. -/
theorem length_taut (n : ℕ) : (taut n).length = n := by simp [taut]

/-- The members of `taut n`. -/
theorem mem_taut {n : ℕ} {C : PCl} : C ∈ taut n ↔ ∃ i < n, C = [(i, true), (i, false)] := by
  simp only [taut, List.mem_map, List.mem_range]
  exact ⟨fun ⟨i, hi, e⟩ => ⟨i, hi, e.symm⟩, fun ⟨i, hi, e⟩ => ⟨i, hi, e.symm⟩⟩

/-- The side list of the root satisfies `SideOK` with no step done. -/
theorem sideOK_taut (n k : ℕ) : SideOK n k (taut n) 0 := by
  refine ⟨by rw [length_taut]; omega, fun C hC => ?_, fun C hC => hC⟩
  obtain ⟨i, hi, rfl⟩ := mem_taut.1 hC
  refine ⟨by simp, fun l hl => ?_⟩
  rcases List.mem_cons.1 hl with rfl | hl
  · exact hi
  · obtain rfl : l = (i, false) := by simpa using hl
    exact hi

/-- The sparsification lemma for counting, for one n, any thresholds θ and any bounds D, T, q, leafB
for which the facts on finite sets (`Iface`) and the
refinement (`Refines`) hold. hv bounds the number of steps on a path that go to the second child. -/
theorem sparsifiesC_of (hSC : StStepCount) (hRC : StRootCount) (hSL : StSumLeaves) (hθ : ∀ i, 1 ≤ θ i) {n : ℕ} (hI : Iface θ k D T q leafB Ok Node) (hR : Refines θ k) {hv : ℕ}
    (hT : T < (hv + 1) * q) (ψ : PFml) (hOk : Ok (toFin ψ)) (hψ : ∀ C ∈ ψ, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) :
    (leaves (stepC θ k) D (rootP ψ, taut n)).length ≤ ∑ j ∈ range (hv + 1), D.choose j ∧
    (∀ x ∈ leaves (stepC θ k) D (rootP ψ, taut n), stepC θ k x = none ∧ (leafF x).length ≤ leafB + (n + k * D) ∧
      (∀ C ∈ leafF x, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ i < n, ∃ C ∈ leafF x, ∃ l ∈ C, l.1 = i) ∧
    cntN n ψ = ((leaves (stepC θ k) D (rootP ψ, taut n)).map fun x => cntN n (leafF x)).sum ∧
    ∀ i, ((Sparsify.round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1.length ≤ D + 1 ∧
      ∀ x ∈ ((Sparsify.round (stepC θ k))^[i] ([(rootP ψ, taut n)], [])).1, (leafF x).length ≤ ψ.length * 2 ^ k + (n + k * D) ∧
        ∀ C ∈ leafF x, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n := by
  have hb : ∀ s p t, GC Node ψ n k s p t → p ≤ D ∧ t ≤ T := fun s p t h => hI.bound _ _ _ _ h.1.2
  have hs := GC_step hθ hI hR ψ hψ
  have hr : GC Node ψ n k (rootP ψ, taut n) 0 0 :=
    ⟨⟨hR.nf_root ψ, by rw [hR.toFin_root]; exact hI.root _ hOk⟩, sideOK_taut n k⟩
  have hnone := step_eq_none_of_mem_leaves hb hs D (rootP ψ, taut n) 0 0 hr (by omega)
  have hk0 : ∀ C ∈ toFin ψ, C.card ≤ k := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := ProgMain.mem_toFin.1 hX
    exact (List.toFinset_card_le C).trans (hψ C hC).1
  have hcl : ∀ x p t, GC Node ψ n k x p t → ∀ C ∈ leafF x, C.length ≤ max k 2 ∧ ∀ l ∈ C, l.1 < n := by
    intro x p t hx C hC
    rcases List.mem_append.1 hC with hC | hC
    · exact ⟨(hx.2.2.1 C hC).1.trans (le_max_right _ _), (hx.2.2.1 C hC).2⟩
    · have := clause_of_G hI hψ hx.1 C hC
      exact ⟨this.1.trans (le_max_left _ _), this.2⟩
  have hside : ∀ x p t, GC Node ψ n k x p t → x.2.length ≤ n + k * D := by
    intro x p t hx
    exact hx.2.1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (hb x p t hx).1) _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact length_leaves_le hb hs _ _ _ _ 0 0 hr (by omega) (by omega)
  · intro x hx
    obtain ⟨p', t', hx'⟩ := exists_of_mem_leaves hs _ _ 0 0 hr x hx
    refine ⟨hnone x hx, ?_, hcl x p' t' hx', fun i hi => ?_⟩
    · have h1 : x.1.length ≤ leafB := by
        rw [ProgMain.nf_length_eq hx'.1.1]
        refine hI.leaf _ _ _ _ hx'.1.2 (hR.none x.1 hx'.1.1 ?_)
        have := hnone x hx
        simpa [stepC] using this
      have h2 := hside x p' t' hx'
      rw [leafF, List.length_append]
      omega
    · exact ⟨[(i, true), (i, false)], List.mem_append_left _ (hx'.2.2.2 _ (mem_taut.2 ⟨i, hi, rfl⟩)), (i, true), by simp, rfl⟩
  · have e : rootC (List.replicate n (), ψ) = (rootP ψ, taut n) := by simp [rootC]
    rw [← hRC n ψ, e]
    exact hSL _ _ _ _ hs (fun x => cntN n (leafF x)) (fun s _ _ l h _ hst => hSC θ k n s l h hst) D (rootP ψ, taut n) 0 0 hr
  · intro i
    obtain ⟨h1, h2⟩ := stack_bound hb hs (rootP ψ, taut n) 0 0 hr i
    refine ⟨h1, fun x hx => ?_⟩
    obtain ⟨p', t', hx'⟩ := h2 x hx
    refine ⟨?_, hcl x p' t' hx'⟩
    have h3 : x.1.length ≤ ψ.length * 2 ^ k := by
      rw [ProgMain.nf_length_eq hx'.1.1]
      refine (ProgMain.card_le_of_clause hk0 (hI.clause _ _ _ _ hx'.1.2)).trans (Nat.mul_le_mul_right _ ?_)
      rw [toFin]
      exact (List.toFinset_card_le _).trans (by simp)
    have h4 := hside x p' t' hx'
    rw [leafF, List.length_append]
    omega

end ProgC

/-- The sparsification lemma for counting, for the thresholds `theta τ`, from the three interface
statements on counts. -/
theorem stProgC (hSC : StStepCount) (hRC : StRootCount) (hSL : StSumLeaves) : StProgC := by
  intro τ k ε hτ hε n ψ hψ
  have hθ : ∀ i, 1 ≤ theta τ i := (stThr τ hτ).pos
  have hI := ProgMain.iface stNodeRoot stNodeStep stNodeBound stLeafCard stLightEq stHeavyEq stSatIff stThr stBetaSum hτ k n
  have hOk : ProgMain.Ok k n (toFin ψ) := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := ProgMain.mem_toFin.1 hX
    obtain ⟨a, b, c⟩ := hψ C hC
    refine ⟨fun l hl => ?_, (List.toFinset_nonempty_iff C).2 a, (List.toFinset_card_le C).trans b⟩
    rw [ProgMain.litsBelow, Finset.mem_product, Finset.mem_range]
    exact ⟨c l (List.mem_toFinset.1 hl), Finset.mem_univ _⟩
  have hT : k * n < (k * n / τ + 1) * τ := by
    calc k * n < τ * (k * n / τ + 1) := Nat.lt_mul_div_succ (k * n) (by omega : 0 < τ)
      _ = (k * n / τ + 1) * τ := Nat.mul_comm _ _
  obtain ⟨c1, c2, c3, c4⟩ := ProgC.sparsifiesC_of hSC hRC hSL hθ hI (Refine.stRefines _ k hθ) hT ψ hOk fun C hC => (hψ C hC).2
  have er : rootC (List.replicate n (), ψ) = (rootP ψ, taut n) := by simp [rootC]
  rw [er]
  refine ⟨?_, fun x hx => ?_, c3, fun i => ⟨(c4 i).1, fun x hx => ?_⟩⟩
  · exact (by exact_mod_cast c1 : ((leaves (stepC (theta τ) k) (bsum τ k * n) (rootP ψ, taut n)).length : ℝ) ≤
      ((∑ j ∈ range (k * n / τ + 1), (bsum τ k * n).choose j : ℕ) : ℝ)).trans (stLeafCount k τ ε hτ hε n)
  · obtain ⟨d1, d2, d3, d4⟩ := c2 x hx
    refine ⟨d1, d2.trans (le_of_eq ?_), d3, d4⟩
    ring
  · obtain ⟨d1, d2⟩ := (c4 i).2 x hx
    refine ⟨d1.trans ?_, d2⟩
    have e : (ψ.length + n) * (2 ^ k + k * bsum τ k + 1) =
        ψ.length * 2 ^ k + (n + k * (bsum τ k * n)) + (ψ.length * (k * bsum τ k + 1) + n * 2 ^ k) := by ring
    rw [e]
    exact Nat.le_add_right _ _

end CountKSat

