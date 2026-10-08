/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Parameters
public import ThreeSumApsp.Programs.Sec4.Theorem30.Areas
public import ThreeSumApsp.Programs.Sec4.Theorem30.Offline

/-!
# Section 4.4, the offline form: preprocess, then one query for each wanted position

Corollary 26: "Hence, for every set W of positions of an N × N matrix, the entries (XY)[I, J], (I,
J) ∈ W, can be computed deterministically in O(|W| D^{0.437} + N²/D^{0.063}) time". Its proof: "The
bound for a set W follows by asking |W| queries." Proof of Theorem 25: "ask one query for each
position of W"; for Corollary 32 the paper uses "the same argument", "With Corollary 31 in place of
Theorem 24".

offline32(N, D, w, U, x, y, wi, wj, out, fr) preprocesses the matrices at x and y (pre31, which uses
the cells from the free pointer fr on) and then asks one query for each of the w positions, whose
rows are at wi and whose columns are at wj; the answers go to out. The arguments are those of the
task `thinTask`. The text `offline32Body`, with the round `offlineAsk32` of its loop, serves all
rational parameters c and θ: they are in the body of the procedure pre31 (`pre31Body`).

A round adds one answer (`offlineAsk32_ends`), with the invariant `Answered` that the offline form
of Theorem 30 uses too, and the routine meets its specification `OfflineSpec32` for all parameters G
(`offline32_meets`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {G : RatParams} {N D₀ : ℕ} {X : Matrix (Fin N) (Fin D₀) ℤ}
  {Y : Matrix (Fin D₀) (Fin N) ℤ} {aX aY fr : ℕ} {U : ℤ} {μ μ' : ℕ → ℤ}

/-! ## The text -/

/-- The entry (XY)[I, J] for natural numbers I, J (0 outside the matrix). -/
def entryN {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ) (I J : ℕ) :
    ℤ :=
  if h : I < N ∧ J < N then (X * Y) ⟨I, h.1⟩ ⟨J, h.2⟩ else 0

namespace Offline32

/-- The locals of offline32. The first ten are its arguments: N, D, the number of positions, a bound
that is not used, the addresses of X, of Y, of the rows and of the columns of the wanted positions
and of the output, and the free pointer. Then come the number of the current position and the result
of a call. -/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Dim : ℕ := 1
@[inherit_doc Size] abbrev Count : ℕ := 2
@[inherit_doc Size] abbrev MatX : ℕ := 4
@[inherit_doc Size] abbrev MatY : ℕ := 5
@[inherit_doc Size] abbrev Rows : ℕ := 6
@[inherit_doc Size] abbrev Cols : ℕ := 7
@[inherit_doc Size] abbrev Out : ℕ := 8
@[inherit_doc Size] abbrev Free : ℕ := 9
@[inherit_doc Size] abbrev Pos : ℕ := 10
@[inherit_doc Size] abbrev Res : ℕ := 11

end Offline32

open Offline32 in
/-- One round of offline32: ask the query for the current position and store its answer. -/
def offlineAsk32 : Stmt :=
  .call Proc.query31 [M (v Rows +' v Pos), M (v Cols +' v Pos), v Size, v Dim, v MatX, v MatY,
    v Free] Res ;;
  .store (v Out +' v Pos) (v Res)

open Offline32 in
/-- offline32(N, D, w, U, x, y, wi, wj, out, fr): preprocess, then ask one query for each wanted
position and store its answer. -/
def offline32Body : Stmt :=
  .call Proc.pre31 [v Size, v Dim, v MatX, v MatY, v Free] Res ;;
  .for Pos (v Count) offlineAsk32

/-! ## What it does -/

/-- What a query needs depends only on the cells of X, of Y, and on the cells from fr on. -/
theorem ready31_congr (h : Ready31 G X Y aX aY fr μ)
    (hX : ∀ a, aX ≤ a → a < aX + N * D₀ → μ' a = μ a)
    (hY : ∀ a, aY ≤ a → a < aY + D₀ * N → μ' a = μ a) (hfr : ∀ a, fr ≤ a → μ' a = μ a) :
    Ready31 G X Y aX aY fr μ' := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun hs => ?_, fun hl => ?_⟩
  · rw [hX _ (by omega) ?_]
    · exact h.matX i j
    · have := Nat.mul_add_le_mul i.isLt (le_refl D₀)
      have := j.isLt
      omega
  · rw [hY _ (by omega) ?_]
    · exact h.matY i j
    · have := Nat.mul_add_le_mul i.isLt (le_refl N)
      have := j.isLt
      omega
  · rw [hfr _ le_rfl]
    exact h.small hs
  · obtain ⟨h1, h2, h3⟩ := h.large hl
    refine ⟨by rw [hfr _ le_rfl]; exact h1, by rw [hfr _ (by omega)]; exact h2,
      dsReady_congr h3 fun a ha => hfr a ?_⟩
    unfold blockAt at ha
    omega

/-- The time of offline32: the preprocessing, and for each wanted position a query, the reading of
the position and the storing of the answer. -/
def tOffline32 (c : ℕ) (G : RatParams) (N D₀ w : ℕ) : ℕ :=
  tPre31 c G N D₀ + w * (tQuery31 G D₀ + 30) + 20

/-- **Where the input of offline32 stands**, beyond what `Input31` says: the matrices at aX and aY;
the two lists of indices, which are below N, and the output, all below the free pointer; and the
output meets neither the matrices nor the lists. -/
structure OfflineInput32 {N D₀ : ℕ} (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ)
    (aX aY aI aJ out fr : ℕ) (WI WJ : List ℕ) (μ : ℕ → ℤ) : Prop where
  matX : MatAt μ aX X
  matY : MatAt μ aY Y
  rows : SegN μ aI WI
  cols : SegN μ aJ WJ
  length_eq : WJ.length = WI.length
  rows_lt : ∀ I ∈ WI, I < N
  cols_lt : ∀ J ∈ WJ, J < N
  rows_le : aI + WI.length ≤ fr
  cols_le : aJ + WI.length ≤ fr
  out_le : out + WI.length ≤ fr
  out_matX : Apart out WI.length aX (N * D₀)
  out_matY : Apart out WI.length aY (D₀ * N)
  out_rows : Apart out WI.length aI WI.length
  out_cols : Apart out WI.length aJ WI.length

/-- offline32 writes the wanted entries of XY to out. Below fr it changes only the output; nothing
is assumed about the cells from fr on. -/
def OfflineSpec32 (lim : Limits) (P : Program) (c : ℕ) (G : RatParams) : Prop :=
  ∀ (N D₀ aX aY aI aJ out fr : ℕ) (X : Matrix (Fin N) (Fin D₀) ℤ) (Y : Matrix (Fin D₀) (Fin N) ℤ)
    (U : ℤ) (u : ℤ) (μ : ℕ → ℤ) (WI WJ : List ℕ),
    Input31 lim G X Y aX aY fr U → OfflineInput32 X Y aX aY aI aJ out fr WI WJ μ →
    ∀ d, d + (G.L (logFour D₀) + 8) ≤ lim.depth → Meets lim P Proc.offline32 d
      [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr] μ (tOffline32 c G N D₀ WI.length)
      fun _ μ' => Seg μ' out ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) ∧
        ∀ a < fr, (a < out ∨ out + WI.length ≤ a) → μ' a = μ a

/-- The specification holds for the program with more procedures appended. -/
theorem OfflineSpec32.append {c : ℕ} (h : OfflineSpec32 lim P c G) (R : Program) :
    OfflineSpec32 lim (P ++ R) c G :=
  fun N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin d hd =>
    (h N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin d hd).append R

/-- **One round**: the answer for position i joins the answers that are there. -/
theorem offlineAsk32_ends (hq : QuerySpec31 lim P G) {aI aJ out d : ℕ}
    {u : ℤ} {WI WJ : List ℕ} (hg : Input31 lim G X Y aX aY fr U)
    (hin : OfflineInput32 X Y aX aY aI aJ out fr WI WJ μ) (hd : d + 4 ≤ lim.depth) {i : ℕ}
    (hi : i < WI.length) (r : ℤ)
    (hinv : Answered (Ready31 G X Y aX aY fr) (· < fr) out
      ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ i μ') :
    Ends lim P d offlineAsk32 ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r], μ'⟩
      (tQuery31 G D₀ + 20) fun σ' => ∃ (r' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r'], μ''⟩ ∧
        Answered (Ready31 G X Y aX aY fr) (· < fr) out
          ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ (i + 1) μ'' := by
  have hw := hg.lim.std.space_le
  have hspace := hg.lim.space
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hlen := hin.length_eq
  have hrows := hin.rows_le
  have hcols := hin.cols_le
  have hout := hin.out_le
  have hiJ : i < WJ.length := by omega
  have hIN : WI[i] < N := hin.rows_lt _ (List.getElem_mem hi)
  have hJN : WJ[i] < N := hin.cols_lt _ (List.getElem_mem hiJ)
  -- the two indices are still in place
  have hrow : μ' (aI + i) = ((WI[i] : ℕ) : ℤ) :=
    (hinv.read hin.rows (j := i) (by simpa using hi)
      (by rcases hin.out_rows with h | h <;> omega) (by omega)).trans (List.getElem_map _)
  have hcol : μ' (aJ + i) = ((WJ[i] : ℕ) : ℤ) :=
    (hinv.read hin.cols (j := i) (by simpa using hiJ)
      (by rcases hin.out_cols with h | h <;> omega) (by omega)).trans (List.getElem_map _)
  -- Res := query31(mem[Rows + Pos], mem[Cols + Pos], N, D, x, y, fr)
  refine Ends.callToThen (hq N D₀ aX aY fr X Y U μ' ⟨WI[i], hIN⟩ ⟨WJ[i], hJN⟩ hg hinv.ready _
    (by omega)) ?_
    (ha := by light_side [hrow, hcol])
  rintro _ μ₂ ⟨rfl, hready, hquery⟩
  -- mem[Out + Pos] := Res
  light_store (out + i) ((X * Y) ⟨WI[i], hIN⟩ ⟨WJ[i], hJN⟩)
  have hstep := hinv.step (by simpa [hlen] using hi) hquery (fun j hj => Or.inl (by omega))
    (fun a ha => Or.inl (by omega)) (ready31_congr hready
      (fun a h1 h2 => Function.update_of_ne (by rcases hin.out_matX with h | h <;> omega) _ _)
      (fun a h1 h2 => Function.update_of_ne (by rcases hin.out_matY with h | h <;> omega) _ _)
      fun a ha => Function.update_of_ne (by omega) _ _)
  rw [List.getElem_map, List.getElem_zip, entryN, dif_pos ⟨hIN, hJN⟩] at hstep
  exact ⟨_, _, rfl, hstep⟩

theorem offline32_meets {c : ℕ} (hP : P[Proc.offline32]? = some offline32Body)
    (hpre : PreSpec31 lim P c G) (hq : QuerySpec31 lim P G) : OfflineSpec32 lim P c G := by
  intro N D₀ aX aY aI aJ out fr X Y U u μ WI WJ hg hin
  refine fun d hd => ⟨offline32Body, hP, ?_⟩
  have hw := hg.lim.std.space_le
  have hspace := hg.lim.space
  have hfr3 := add_three_le_structEnd G N D₀ fr
  have hlen := hin.length_eq
  have hout := hin.out_le
  have hzip : (WI.zip WJ).length = WI.length := by simp [hlen]
  -- Res := pre31(N, D, x, y, fr)
  refine Ends.callToThen (hpre N D₀ aX aY fr X Y U μ hg hin.matX hin.matY _ (by omega)) ?_
    (hT := by simp [tOffline32]; omega)
  rintro r μ₁ ⟨hready, hblock⟩
  -- for Pos < Count: offlineAsk32
  refine Ends.for (fun i σ => ∃ (r : ℤ) (μ' : ℕ → ℤ),
      σ = ⟨frame [N, D₀, WI.length, u, aX, aY, aI, aJ, out, fr, i, r], μ'⟩ ∧
      Answered (Ready31 G X Y aX aY fr) (· < fr) out ((WI.zip WJ).map fun q => entryN X Y q.1 q.2) μ
        i μ')
    WI.length (tQuery31 G D₀ + 20) ?start ?round ?done ?bound
    (hT := by simp [tOffline32]; ring_nf; omega)
  case start =>
    exact ⟨r, μ₁, by rw [update_frame_setLocal]; rfl, hready, Seg.nil,
      SameOn.mono hblock fun a ha => Or.inl ha.2⟩
  case bound =>
    rintro i _ - - ⟨r, μ', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨r, μ', rfl, hinv⟩
    rw [← hzip, ← List.length_map (as := WI.zip WJ) fun q => entryN X Y q.1 q.2] at hinv
    refine ⟨hinv.all, fun a ha hoff => hinv.same a ⟨?_, ha⟩⟩
    simpa [hlen] using hoff
  case round =>
    rintro i _ hi - ⟨r, μ', rfl, hinv⟩
    refine (offlineAsk32_ends hq hg hin (by omega) hi r hinv).mono le_rfl ?_
    rintro _ ⟨r', μ'', rfl, hinv'⟩
    exact ⟨by simp, r', μ'', by rw [update_frame_setLocal]; rfl, hinv'⟩

end Light.Sec4
