/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.FrontFacts
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.GridContracts
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Nodes

/-!
# The reduction from 3SUM to Convolution-3SUM: one splitting

round(β, β', b, nd, val, bt, Λ, A, n, f, cx, fr) handles the splitting `(β, β', v)` of the set of
the distinct values, where `b` is 1 for `v = true` and 0 for `v = false` (for Theorem 21(a), after
[CH20, Theorem 5.1]).  The first set of the splitting holds the values whose label x + V has the
binary digit β equal to v; the second and the third hold those whose digit β differs from v and
whose digit β' is 0 and 1 (`splitA`, `splitB`).  The routine selects the three sets by their binary
digits, writes them to `A`, `A + n` and `A + 2n` (`roundSets_ends`), and calls the recursive
procedure on them (`round_spec`).

What the memory holds while the splittings are run through (`FrontMem`) does not depend on the 3n
cells from `A` (`FrontMem.keptBut`).  So each of the three calls of pick finds what it needs
(`FrontMem.pick_meets`), and afterwards the three sets and the rest form the memory of a node
(`FrontMem.nodeMem`).  The time is `le_tRound`, with `ChRound.treeCalls_le_pow` for the number of
calls of the recursive procedure.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

variable {lim : Limits} {P : Program} {d : ℕ}

namespace RoundLocals

/-- The local variables of round: the arguments β, β', b, nd, val, bt, Λ, A, n, f, cx, fr; then
1 - b, A + n, A + 2n, and the sizes of the three sets. -/
abbrev BETA : ℕ := 0
@[inherit_doc BETA] abbrev BETA' : ℕ := 1
@[inherit_doc BETA] abbrev BIT : ℕ := 2
@[inherit_doc BETA] abbrev NVALUES : ℕ := 3
@[inherit_doc BETA] abbrev VAL : ℕ := 4
@[inherit_doc BETA] abbrev BITS : ℕ := 5
@[inherit_doc BETA] abbrev LAM : ℕ := 6
@[inherit_doc BETA] abbrev OUT0 : ℕ := 7
@[inherit_doc BETA] abbrev NMAX : ℕ := 8
@[inherit_doc BETA] abbrev LEVELS : ℕ := 9
@[inherit_doc BETA] abbrev CTX : ℕ := 10
@[inherit_doc BETA] abbrev FREE : ℕ := 11
@[inherit_doc BETA] abbrev NBIT : ℕ := 12
@[inherit_doc BETA] abbrev OUT1 : ℕ := 13
@[inherit_doc BETA] abbrev OUT2 : ℕ := 14
@[inherit_doc BETA] abbrev SIZE0 : ℕ := 15
@[inherit_doc BETA] abbrev SIZE1 : ℕ := 16
@[inherit_doc BETA] abbrev SIZE2 : ℕ := 17

end RoundLocals

open RoundLocals in
/-- The three sets of the splitting are written to A, A + n and A + 2n. -/
def roundSets (pPick : ℕ) : Stmt :=
  .set NBIT (k 1 -' v BIT) ;;
  .set OUT1 (v OUT0 +' v NMAX) ;;
  .set OUT2 (v OUT1 +' v NMAX) ;;
  .call pPick [v NVALUES, v VAL, v BITS, v LAM, v BETA, v BIT, v BETA', k 0, k 0, v OUT0] SIZE0 ;;
  .call pPick [v NVALUES, v VAL, v BITS, v LAM, v BETA, v NBIT, v BETA', k 0, k 1, v OUT1] SIZE1 ;;
  .call pPick [v NVALUES, v VAL, v BITS, v LAM, v BETA, v NBIT, v BETA', k 1, k 1, v OUT2] SIZE2

open RoundLocals in
/-- round(β, β', b, nd, val, bt, Λ, A, n, f, cx, fr), over the procedures number pPick and pNodes:
the three sets are written, and the recursive procedure is called on them. -/
def roundBody (pPick pNodes : ℕ) : Stmt :=
  roundSets pPick ;;
  .call pNodes [v LEVELS, v OUT0, v SIZE0, v OUT1, v SIZE1, v OUT2, v SIZE2, v CTX, v FREE] 0

/-- The recursive procedure makes at most `2 · 3^f` calls. -/
theorem ChRound.treeCalls_le_pow (Q : Finset ℕ) (Λ f : ℕ) (S₁ S₂ S₃ : Finset ℤ) :
    treeCalls Q Λ f S₁ S₂ S₃ ≤ 2 * 3 ^ f := by
  have hcalls := treeCalls_le Q Λ f S₁ S₂ S₃
  have hnodes := length_nodes_le Q Λ f S₁ S₂ S₃
  omega

section front

variable {μ μ' : ℕ → ℤ} {a : FrontArgs}

/-- What the memory holds while the splittings are run through is kept if, below the free pointer,
only the 3n cells from A change. -/
theorem FrontMem.keptBut (h : FrontMem μ a)
    (hk : KeptBut μ μ' a.fr a.A (3 * a.n)) : FrontMem μ' a := by
  have keep : ∀ s len : ℕ, s + len ≤ a.fr → Apart a.A (3 * a.n) s len →
      ∀ i < len, μ' (s + i) = μ (s + i) := fun s len hb hap i hi =>
    hk _ ⟨by omega, by omega⟩
  exact { h with
    segVal := h.segVal.congr fun i hi => keep a.val a.nd h.belowVal h.apartVal i (h.lenD ▸ hi)
    segBt := h.segBt.congr fun i hi => keep a.bt (a.nd * a.Λ) h.belowBt h.apartBt i
      (by rw [← h.lenD, ← length_bitTable a.V]; exact hi)
    ctx := Seg.congr h.ctx fun i hi => keep a.cx 6 h.belowCx h.apartCx i (by simpa using hi)
    primes := ⟨h.primes.1, h.primes.2.congr fun i hi =>
      keep a.pr a.np h.belowPr h.apartPr i (by rw [h.primes.1]; simpa using hi)⟩
    zero := fun i hi => (keep a.cnt (a.m * a.m) h.belowCnt h.apartCnt i hi).trans (h.zero i hi) }

/-- The same if only the 3n cells from A change at all. -/
theorem FrontMem.of_sameOutside (h : FrontMem μ a)
    (hs : SameOutside μ μ' a.A (3 * a.n)) : FrontMem μ' a :=
  h.keptBut (SameOn.mono hs fun _ hb => hb.2)

/-- pick, called for the distinct values, with the output in one of the three parts of the 3n
cells from A. -/
theorem FrontMem.pick_meets (h : FrontMem μ a) {pPick : ℕ}
    (hPick : PickSpec lim P pPick) {β β' o : ℕ} (hβ : β < a.Λ) (hβ' : β' < a.Λ) (x x' two : ℤ)
    (ho : o + a.n ≤ 3 * a.n) (hfr : a.fr ≤ lim.space) (hw : (lim.space : ℤ) ≤ lim.word)
    (hword : (8 : ℤ) ≤ lim.word) :
    Meets lim P pPick d [a.nd, a.val, a.bt, a.Λ, β, x, β', x', two, (a.A + o : ℕ)] μ (tPick a.nd)
      fun r μ' =>
      r = ((pickList a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)).length : ℤ) ∧
        Seg μ' (a.A + o) (pickList a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)) ∧
        SameOutside μ μ' (a.A + o) a.nd := by
  light_facts h
  have hrows : a.D.length * a.Λ = a.nd * a.Λ := by rw [h.lenD]
  rw [← h.lenD]
  exact hPick d a.val a.bt (a.A + o) a.Λ β β' x x' two a.D _ μ {
    lenTable := length_bitTable a.V a.Λ a.D
    posA := hβ
    posB := hβ'
    segSrc := h.segVal
    segTable := h.segBt
    apartSrc := by omega
    apartTable := by omega
    spaceSrc := by omega
    spaceTable := by omega
    spaceOut := by omega
    space_le := hw
    word := hword }

/-- Three subsets of the distinct values in the three parts of the 3n cells from A, with the rest of
the memory, are the memory of a node. -/
theorem FrontMem.nodeMem (h : FrontMem μ a)
    {k₁ k₂ k₃ : ℕ} {S₁ S₂ S₃ : Finset ℤ} (h₁ : SetAt μ a.A k₁ S₁) (h₂ : SetAt μ (a.A + a.n) k₂ S₂)
    (h₃ : SetAt μ (a.A + a.n + a.n) k₃ S₃) (hk₁ : k₁ ≤ a.n) (hk₂ : k₂ ≤ a.n) (hk₃ : k₃ ≤ a.n)
    (hS₁ : S₁ ⊆ a.D.toFinset) (hS₂ : S₂ ⊆ a.D.toFinset) (hS₃ : S₃ ⊆ a.D.toFinset) :
    NodeMem μ ⟨a.toEnv, ⟨a.A, k₁, S₁⟩, ⟨a.A + a.n, k₂, S₂⟩, ⟨a.A + a.n + a.n, k₃, S₃⟩⟩ := by
  light_facts h
  exact
    { envOk := ⟨h.primes, h.zero, h.belowPr, h.belowCnt, h.cntPr⟩
      set₁ := ⟨h₁, hk₁, h.bdd.mono hS₁, by dsimp only; omega, by dsimp only; omega⟩
      set₂ := ⟨h₂, hk₂, h.bdd.mono hS₂, by dsimp only; omega, by dsimp only; omega⟩
      set₃ := ⟨h₃, hk₃, h.bdd.mono hS₃, by dsimp only; omega, by dsimp only; omega⟩ }

/-- **The three sets of the splitting** are written, and with the rest of the memory they are the
memory of a node. -/
theorem roundSets_ends (hF : FrontMem μ a) {pPick : ℕ}
    (hPick : PickSpec lim P pPick) {β β' f : ℕ} (hβ : β < a.Λ) (hβ' : β' < a.Λ) (v : Bool)
    (hfr : a.fr ≤ lim.space) (hw : (lim.space : ℤ) ≤ lim.word) (hword : (8 : ℤ) ≤ lim.word)
    (hd : d < lim.depth) :
    Ends lim P d (roundSets pPick)
      ⟨frame [β, β', if v then 1 else 0, a.nd, a.val, a.bt, a.Λ, a.A, a.n, f, a.cx, a.fr], μ⟩
        (48 + 3 * tPick a.nd)
      fun σ' => ∃ (k₁ k₂ k₃ : ℕ) (μ' : ℕ → ℤ), SameOutside μ μ' a.A (3 * a.n) ∧
        NodeMem μ' ⟨a.toEnv, ⟨a.A, k₁, splitA a.V β v a.D.toFinset⟩,
          ⟨a.A + a.n, k₂, splitB a.V β β' v false a.D.toFinset⟩,
          ⟨a.A + a.n + a.n, k₃, splitB a.V β β' v true a.D.toFinset⟩⟩ ∧
        σ' = ⟨frame [β, β', if v then 1 else 0, a.nd, a.val, a.bt, a.Λ, a.A, a.n, f, a.cx, a.fr,
          if !v then 1 else 0, (a.A + a.n : ℕ), (a.A + a.n + a.n : ℕ), k₁, k₂, k₃], μ'⟩ := by
  have hA := hF.belowA
  have hndn := hF.nd_le
  have hlen : ∀ x x' two, (pickList a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)).length ≤ a.n :=
    fun x x' two => (length_pickList_le a.Λ β β' x x' two a.D (bitTable a.V a.Λ a.D)).trans
      (hF.lenD ▸ hndn)
  -- b' := 1 - b; A₁ := A + n; A₂ := A₁ + n
  refine Ends.setToThen (if !v then 1 else 0) ?_ (by cases v <;> simp <;> omega)
  light_set (a.A + a.n : ℕ)
  light_set (a.A + a.n + a.n : ℕ)
  -- n₀ := pick(nd, val, bt, Λ, β, b, β', 0, 0, A)
  light_call (hF.pick_meets (o := 0) hPick hβ hβ' (if v then 1 else 0) 0 0
    (by omega) hfr hw hword) with _ μ₁ ⟨rfl, seg₁, same₁⟩
  have out₁ : SameOutside μ μ₁ a.A (3 * a.n) := same₁.mono (by omega) (by omega)
  have hF₁ := hF.of_sameOutside out₁
  -- n₁ := pick(nd, val, bt, Λ, β, b', β', 0, 1, A₁)
  light_call (hF₁.pick_meets (o := a.n) hPick hβ hβ' (if !v then 1 else 0) 0 1
    (by omega) hfr hw hword) with _ μ₂ ⟨rfl, seg₂, same₂⟩
  have out₂ : SameOutside μ₁ μ₂ a.A (3 * a.n) := same₂.mono (by omega) (by omega)
  have hF₂ := hF₁.of_sameOutside out₂
  -- n₂ := pick(nd, val, bt, Λ, β, b', β', 1, 1, A₂)
  light_call (hF₂.pick_meets (o := a.n + a.n) hPick hβ hβ' (if !v then 1 else 0) 1 1
    (by omega) hfr hw hword) with _ μ₃ ⟨rfl, seg₃, same₃⟩
  have out₃ : SameOutside μ₂ μ₃ a.A (3 * a.n) := same₃.mono (by omega) (by omega)
  -- The three lists are the three sets of the splitting.  (For the first set pick looks at one
  -- digit only, and the 0 stands for the value of the other digit, which it ignores.)
  obtain ⟨nodup₁, set₁⟩ := pick_splitA a.V a.Λ hβ hβ' v 0 hF.nodup
  obtain ⟨nodup₂, set₂⟩ := pick_splitB a.V a.Λ hβ hβ' v false hF.nodup
  obtain ⟨nodup₃, set₃⟩ := pick_splitB a.V a.Λ hβ hβ' v true hF.nodup
  have hlen₁ := hlen (if v then 1 else 0) 0 0
  have hlen₂ := hlen (if !v then 1 else 0) 0 1
  exact ⟨_, _, _, μ₃, out₁.trans (out₂.trans out₃),
    (hF₂.of_sameOutside out₃).nodeMem
      ⟨_, rfl, (seg₁.of_sameOutside same₂ (by omega)).of_sameOutside same₃ (by omega), nodup₁, set₁⟩
      ⟨_, rfl, seg₂.of_sameOutside same₃ (by omega), nodup₂, set₂⟩
      ⟨_, rfl, Nat.add_assoc a.A a.n a.n ▸ seg₃, nodup₃, set₃⟩ hlen₁ hlen₂ (hlen _ _ _)
      (Finset.filter_subset _ _) (Finset.filter_subset _ _) (Finset.filter_subset _ _), rfl⟩

end front

/-- The time of round covers three calls of pick and the recursion tree: 48 steps and the three
calls for roundSets, 11 steps and the tree for the last call. -/
theorem le_tRound (T : ℕ → ℕ → ℕ) {n nd : ℕ} (hnd : nd ≤ n) (V m np Λ f : ℕ)
    (S₁ S₂ S₃ : Finset ℤ) :
    59 + 3 * tPick nd + tNodes T n V m np (treeCalls (Nat.primesLE m) Λ f S₁ S₂ S₃)
      ≤ tRound T n V m np f := by
  have hpick : tPick nd ≤ tPick n := by simp only [tPick]; omega
  have htree := Nat.mul_le_mul_right (tNode T n V m np + 60)
    (ChRound.treeCalls_le_pow (Nat.primesLE m) Λ f S₁ S₂ S₃)
  simp only [tRound, tTree, tNodes] at htree ⊢
  omega

/-- **round meets its specification**, in every program that holds its body and meets the
specifications of the two routines that it calls. -/
theorem round_spec {p pPick pNodes : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (hP : P[p]? = some (roundBody pPick pNodes)) (hPick : PickSpec lim P pPick)
    (hN : NodesSpec lim P pNodes T r) : RoundSpec lim P p T r := by
  intro a f β β' v μ hF hβ hβ' d H
  refine .of_body hP ?_
  have hw := H.ok.space
  have hcells := H.ok.cells
  have hword := H.ok.word
  have hdepth := H.ok.depth
  simp only [gridNeed] at hcells hword hdepth
  push_cast at hword
  have htime := le_tRound T hF.nd_le a.V a.m a.np a.Λ f (splitA a.V β v a.D.toFinset)
    (splitB a.V β β' v false a.D.toFinset) (splitB a.V β β' v true a.D.toFinset)
  -- the three sets
  light_piece (roundSets_ends hF hPick hβ hβ' v (by omega) hw (by omega)
    (by omega)) with _ ⟨k₁, k₂, k₃, μ₁, out, hmem, rfl⟩
  -- return nodes(f, A, n₀, A₁, n₁, A₂, n₂, cx, fr)
  light_call (hN f _ a.Λ a.cx μ₁ (d + 1)
    { mem := hmem
      ctx := (hF.of_sameOutside out).ctx
      belowCtx := hF.belowCx
      apartCtx := hF.cntCx
      V_pos := H.V_pos
      m_pos := H.m_pos
      lam := H.lam
      primes := H.primes
      ok := { word := by dsimp only; omega, cells := hcells, space := hw,
              depth := by dsimp only; omega } })
    using NodeArgs.calls with _ μ₂ ⟨rfl, kept⟩
  exact ⟨by simp [SplitYes, TreeYes], out.then kept fun b hb => ⟨hb.2, hb.1⟩⟩

end Light.Sec3.ChanHe
