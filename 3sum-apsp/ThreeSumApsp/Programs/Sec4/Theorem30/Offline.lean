/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.Theorem30.Memory

/-!
# Theorem 30, the offline form (9): preprocess, then one query for each wanted position

Theorem 30: "In particular, for every set W of positions of an N × N matrix, the entries (XY)[I, J],
(I, J) ∈ W, can be computed deterministically in time
O(L |W| ∑_{d=0}^{t} α_d + L m ρ^t/(1 - ρ) N² + N · 10^L/(√K N₀))."

wantedCore is relocatable: it receives the addresses of the matrices, of the two lists of indices,
of the output and of the free block. It meets its specification `WantedCoreSpec` in every program
that meets those of preCore and queryAt (`wantedCore_spec`): one call of preCore, then a loop whose
round asks one query and stores the answer (`wantedAsk_ends`), with the invariant `Answered`.
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## One query for each wanted position: the invariant -/

section
variable {Ready : (ℕ → ℤ) → Prop} {Kept Quiet : ℕ → Prop} {out i : ℕ} {ans : List ℤ}
  {μ μ' μ'' : ℕ → ℤ}

/-- The invariant of a loop that asks one query after the other and stores the answers ans from the
address out on, before query i.  The memory is Ready for a query, the first i answers are in place,
and the cells in Kept outside these i cells are as in the memory μ at the start. -/
structure Answered (Ready : (ℕ → ℤ) → Prop) (Kept : ℕ → Prop) (out : ℕ) (ans : List ℤ) (μ : ℕ → ℤ)
    (i : ℕ) (μ' : ℕ → ℤ) : Prop where
  ready : Ready μ'
  answers : Seg μ' out (ans.take i)
  same : SameOn (fun a => Outside out i a ∧ Kept a) μ μ'

/-- One round: a query that leaves the cells in Quiet alone, among them the output and the cells in
Kept, and the store of its answer behind the answers that are there. -/
theorem Answered.step (h : Answered Ready Kept out ans μ i μ') (hi : i < ans.length)
    (hquery : SameOn Quiet μ' μ'') (hout : ∀ j < i, Quiet (out + j)) (hkept : ∀ a, Kept a → Quiet a)
    (hready : Ready (Function.update μ'' (out + i) ans[i])) :
    Answered Ready Kept out ans μ (i + 1) (Function.update μ'' (out + i) ans[i]) := by
  have hlen : (ans.take i).length = i := by rw [List.length_take, Nat.min_eq_left hi.le]
  refine ⟨hready, ?_, ?_⟩
  · have hsnoc := (h.answers.of_sameOn hquery fun j hj => hout j (hlen ▸ hj)).snoc ans[i]
    rw [hlen] at hsnoc
    rwa [List.take_add_one, List.getElem?_eq_getElem hi]
  · exact ((h.same.mono fun a ha => ⟨by have := ha.1; omega, ha.2⟩).then hquery
      fun a ha => ⟨ha, hkept a ha.2⟩).write (by omega) _

/-- A cell of a list that stood in the memory at the start, away from the answers and in Kept, still
holds its entry. -/
theorem Answered.read (h : Answered Ready Kept out ans μ i μ') {a j : ℕ} {l : List ℤ}
    (hl : Seg μ a l) (hj : j < l.length) (hoff : Outside out i (a + j)) (hkept : Kept (a + j)) :
    μ' (a + j) = l[j] :=
  (h.same _ ⟨hoff, hkept⟩).trans (hl.get hj)

/-- After the last round all answers are in place. -/
theorem Answered.all (h : Answered Ready Kept out ans μ ans.length μ') : Seg μ' out ans := by
  simpa using h.answers

end

/-! ## The routine -/

abbrev Proc.wantedCore : ℕ := 56

namespace WantedCore

/-- The locals of wantedCore. The first twelve are its arguments: L, m, t, N, D, the addresses of X,
of Y, of the rows and of the columns of the wanted positions, the number of positions, and the
addresses of the output and of the free block. Then come the number of the current position and the
result of a call. -/
abbrev Levels : ℕ := 0
@[inherit_doc Levels] abbrev Inner : ℕ := 1
@[inherit_doc Levels] abbrev Switch : ℕ := 2
@[inherit_doc Levels] abbrev Size : ℕ := 3
@[inherit_doc Levels] abbrev Dim : ℕ := 4
@[inherit_doc Levels] abbrev MatX : ℕ := 5
@[inherit_doc Levels] abbrev MatY : ℕ := 6
@[inherit_doc Levels] abbrev Rows : ℕ := 7
@[inherit_doc Levels] abbrev Cols : ℕ := 8
@[inherit_doc Levels] abbrev Count : ℕ := 9
@[inherit_doc Levels] abbrev Out : ℕ := 10
@[inherit_doc Levels] abbrev Block : ℕ := 11
@[inherit_doc Levels] abbrev Pos : ℕ := 12
@[inherit_doc Levels] abbrev Res : ℕ := 13

end WantedCore

open WantedCore in
/-- One round of wantedCore: ask the query for the current position and store its answer. -/
def wantedAsk : Stmt :=
  .call Proc.queryAt [M (v Rows +' v Pos), M (v Cols +' v Pos), v Block] Res ;;
  .store (v Out +' v Pos) (v Res)

open WantedCore in
/-- wantedCore(L, m, t, N, D, aX, aY, aI, aJ, w, out, b0): preprocess, then ask one query for each
wanted position and store its answer. -/
def wantedCoreBody : Stmt :=
  .call Proc.preCore [v Levels, v Inner, v Switch, v Size, v Dim, v MatX, v MatY, v Block] Res ;;
  .for Pos (v Count) wantedAsk

/-- The time of wantedCore. -/
def tWantedCore (c : ℕ) (p : Sec2.Par) (t w : ℕ) : ℕ :=
  tPreCore c p t + w * (tQueryAt p.L p.m t + 24) + 16

section
variable {p : Sec2.Par} {t : ℕ} {hmL : p.m ≤ p.L} {aX aY aI aJ out b0 : ℕ}
  {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ} {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ}
  {W : List (Fin p.N × Fin p.N)} {μ μ' μ'' : ℕ → ℤ}

/-- Where the input of wantedCore stands: the two matrices, the rows and the columns of the wanted
positions and the output all lie below the free block, and the output does not meet the two lists.
-/
structure WantedInput (p : Sec2.Par) (aX aY aI aJ out b0 : ℕ) (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ)
    (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (W : List (Fin p.N × Fin p.N)) (μ : ℕ → ℤ) : Prop where
  matX : MatAt μ aX X
  matY : MatAt μ aY Y
  rows : Seg μ aI (W.map fun q => ((q.1 : ℕ) : ℤ))
  cols : Seg μ aJ (W.map fun q => ((q.2 : ℕ) : ℤ))
  matX_le : aX + p.N * p.D ≤ b0
  matY_le : aY + p.D * p.N ≤ b0
  rows_le : aI + W.length ≤ b0
  cols_le : aJ + W.length ≤ b0
  out_le : out + W.length ≤ b0
  out_rows : Apart out W.length aI W.length
  out_cols : Apart out W.length aJ W.length

end

/-- wantedCore writes the wanted entries of XY to out.  It changes only the output and the block
from b0 on, about whose content nothing is assumed. -/
def WantedCoreSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Sec2.Par) (t : ℕ) (_hmL : p.m ≤ p.L) (aX aY aI aJ out b0 : ℕ)
    (X : Matrix (Fin p.N) (Fin (D p.m)) ℤ) (Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ) (U : ℤ)
    (μ : ℕ → ℤ) (W : List (Fin p.N × Fin p.N)), t ≤ p.m → Lim30 lim p t b0 U →
    (∀ i j, |X i j| ≤ U) → (∀ i j, |Y i j| ≤ U) → WantedInput p aX aY aI aJ out b0 X Y W μ →
    ∀ d, d + (p.L + 7) ≤ lim.depth → Meets lim P Proc.wantedCore d
      [p.L, p.m, t, p.N, p.D, aX, aY, aI, aJ, W.length, out, b0] μ (tWantedCore c p t W.length)
      fun _ μ' => Seg μ' out (W.map fun q => (X * Y) q.1 q.2) ∧
        SameOn (fun a => Outside out W.length a ∧ Outside b0 (top p t b0 - b0) a) μ μ'

/-- **One round**: the answer for position i joins the answers that are there. -/
theorem wantedAsk_ends {lim : Limits} {P : Program} (hq : QueryAtSpec lim P) {p : Sec2.Par}
    {t d : ℕ} {hmL : p.m ≤ p.L} {aX aY aI aJ out b0 : ℕ} {X : Matrix (Fin p.N) (Fin (D p.m)) ℤ}
    {Y : Matrix (Fin (D p.m)) (Fin p.N) ℤ} {U : ℤ} {μ μ' : ℕ → ℤ} {W : List (Fin p.N × Fin p.N)}
    (ht : t ≤ p.m) (hlim : Lim30 lim p t b0 U) (hX : ∀ i j, |X i j| ≤ U) (hY : ∀ i j, |Y i j| ≤ U)
    (hin : WantedInput p aX aY aI aJ out b0 X Y W μ) (hd : d + 3 ≤ lim.depth) {i : ℕ}
    (hi : i < W.length) (r : ℤ)
    (hinv : Answered (DSReady p t hmL aX aY b0 X Y) (Outside b0 (top p t b0 - b0)) out
      (W.map fun q => (X * Y) q.1 q.2) μ i μ') :
    Ends lim P d wantedAsk
      ⟨frame [p.L, p.m, t, p.N, p.D, aX, aY, aI, aJ, W.length, out, b0, i, r], μ'⟩
      (tQueryAt p.L p.m t + 16) fun σ' => ∃ (r' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame [p.L, p.m, t, p.N, p.D, aX, aY, aI, aJ, W.length, out, b0, i, r'], μ''⟩ ∧
        Answered (DSReady p t hmL aX aY b0 X Y) (Outside b0 (top p t b0 - b0)) out
          (W.map fun q => (X * Y) q.1 q.2) μ (i + 1) μ'' := by
  light_facts hlim hlim.std
  have htop := base_le_top p t b0
  have hscratch := scratch_in_block p t b0
  light_facts hin
  -- the two indices are still in place
  have hrow : μ' (aI + i) = ((W[i].1 : ℕ) : ℤ) :=
    (hinv.read hin.rows (j := i) (by simpa using hi)
      (by rcases hin.out_rows with h | h <;> omega) (by omega)).trans (List.getElem_map _)
  have hcol : μ' (aJ + i) = ((W[i].2 : ℕ) : ℤ) :=
    (hinv.read hin.cols (j := i) (by simpa using hi)
      (by rcases hin.out_cols with h | h <;> omega) (by omega)).trans (List.getElem_map _)
  -- Res := queryAt(mem[Rows + Pos], mem[Cols + Pos], b0)
  refine Ends.callToThen (hq p t hmL aX aY b0 X Y U μ' W[i].1 W[i].2 ht hlim hX hY
    hinv.ready _ (by omega)) ?_ (ha := by light_side [hrow, hcol])
  rintro _ μ₂ ⟨rfl, hready, hquery⟩
  -- mem[Out + Pos] := Res
  light_store (out + i) ((X * Y) W[i].1 W[i].2)
  have hstep := hinv.step (by simpa using hi) hquery (fun j hj => Or.inl (by omega))
    (fun a ha => by omega) (dsReady_congr hready fun a ha => Function.update_of_ne (by omega) _ _)
  rw [List.getElem_map] at hstep
  exact ⟨_, _, rfl, hstep⟩

/-- **wantedCore** meets its specification. -/
theorem wantedCore_spec {lim : Limits} {P : Program} {c : ℕ}
    (hP : P[Proc.wantedCore]? = some wantedCoreBody) (hpre : PreCoreSpec lim P c)
    (hq : QueryAtSpec lim P) : WantedCoreSpec lim P c := by
  intro p t hmL aX aY aI aJ out b0 X Y U μ W ht hlim hX hY hin
  refine fun d hd => ⟨wantedCoreBody, hP, ?_⟩
  light_facts hlim hlim.std
  have htop := base_le_top p t b0
  have hout := hin.out_le
  -- Res := preCore(L, m, t, N, D, aX, aY, b0)
  refine Ends.callToThen (hpre p t hmL aX aY b0 X Y U μ ht hlim hX hY hin.matX hin.matY
    hin.matX_le hin.matY_le _ (by omega)) ?_ (hT := by simp [tWantedCore]; omega)
  rintro r μ₁ ⟨hready, hblock⟩
  -- for Pos < Count: wantedAsk
  refine Ends.for (fun i σ => ∃ (r : ℤ) (μ' : ℕ → ℤ),
      σ = ⟨frame [p.L, p.m, t, p.N, p.D, aX, aY, aI, aJ, W.length, out, b0, i, r], μ'⟩ ∧
      Answered (DSReady p t hmL aX aY b0 X Y) (Outside b0 (top p t b0 - b0)) out
        (W.map fun q => (X * Y) q.1 q.2) μ i μ')
    W.length (tQueryAt p.L p.m t + 16) ?start ?round ?done ?bound
    (hT := by simp [tWantedCore]; ring_nf; omega)
  case start =>
    exact ⟨r, μ₁, by rw [update_frame_setLocal]; rfl, hready, Seg.nil,
      SameOn.mono hblock fun a ha => ha.2⟩
  case bound =>
    rintro i _ - - ⟨r, μ', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨r, μ', rfl, hinv⟩
    rw [← List.length_map (as := W) fun q => (X * Y) q.1 q.2] at hinv
    exact ⟨hinv.all, by simpa using hinv.same⟩
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, hinv⟩
    refine (wantedAsk_ends hq ht hlim hX hY hin (by omega) hi r hinv).mono le_rfl ?_
    rintro _ ⟨r', μ'', rfl, hinv'⟩
    exact ⟨by simp, r', μ'', by rw [update_frame_setLocal]; rfl, hinv'⟩

end Light.Sec4
