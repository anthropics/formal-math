/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Corollary15_16.CountAndDetect
public import ThreeSumApsp.Spec.Sec3.Theorem17.Parameters
public import ThreeSumApsp.TimeClaims.Sec3.Arithmetic

/-!
# Corollary 15: splitting the set of query pairs

Corollary 15: "splitting W into sets of at most n²/√D query pairs".  In full:
if #Lop-AE-SparseTri is solved in time T(n, D, w), then it is solved in time
⌈w/s⌉ (T(n, D, s) + O(n D + 1)) + O(w + 1), where s = max(1, ⌊n²/√D⌋) is `splitCap n D`.  This is
`Claim.LopSplit`, with "the problem is solved in time T" read as `LopSolvedIn lopCountTask T`
(`claim_lopSplit`).

The host computes c = max(1, min(⌊n²/√D⌋, w)) and calls the solver on the pieces of c query pairs
(the last piece may be shorter).  A piece is a segment of the arrays of query pairs and of answers,
so nothing is copied, and the two matrices stay where they are.  The number ⌊n²/√D⌋ is the greatest
c with c² D ≤ n⁴; it is found by counting up, and the counting stops at w, because the claim allows
only O(w + 1) steps outside the calls.  If w is smaller than ⌊n²/√D⌋, all query pairs form a single
piece, whether the length of a piece is ⌊n²/√D⌋ as in the claim or min(⌊n²/√D⌋, w) as computed here.

* `lopSplitCount_spec`, `lopSplitCap_spec`: the counting finds c.
* `lopSplitPiece_spec`: one call.  A piece of an instance is an instance (`piece_pre`), and its
  answers are a piece of the answers (`thinOut_piece`).
* `split_spec`: the loop over the pieces.
* `ceilDiv_capW_le`: there are at most as many pieces as in the claim; `polyNeedN_split`: the need
  stays polynomial.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {d : ℕ}

/-! ## The procedure -/

namespace LopSplit

/-- The local variables of split beside the ten arguments: the length c of the pieces; N⁴; first the
bound of the counting, then the number lo of query pairs that are done; the length len of the
piece; the result of the call. -/
abbrev C : ℕ := 10
@[inherit_doc C] abbrev N4 : ℕ := 11
@[inherit_doc C] abbrev LO : ℕ := 12
@[inherit_doc C] abbrev LEN : ℕ := 13
@[inherit_doc C] abbrev RES : ℕ := 14

end LopSplit

open LopArgs LopSplit in
/-- c counts up as long as c < lo and (c + 1)² D ≤ N⁴. -/
def lopSplitCount : Stmt :=
  .while (v C <' v LO) (
    .ite ((v C +' k 1) *' (v C +' k 1) *' v DD ≤' v N4) (.set C (v C +' k 1)) (.set LO (v C)))

open LopArgs LopSplit in
/-- c := max(1, min(⌊N²/√D⌋, w)). -/
def lopSplitCap : Stmt :=
  .set C (k 1) ;; .set N4 (v N *' v N *' v N *' v N) ;; .set LO (v W) ;; lopSplitCount

open LopArgs LopSplit in
/-- The solver is called on the piece of len = min(c, w - lo) query pairs from number lo on. -/
def lopSplitPiece (pCount : ℕ) : Stmt :=
  .set LEN (v C) ;;
  .ite (v W -' v LO <' v C) (.set LEN (v W -' v LO)) .skip ;;
  .call pCount [v N, v DD, v LEN, v U, v X, v Y, v WI +' v LO, v WJ +' v LO, v OUT +' v LO, v FR]
    RES ;;
  .set LO (v LO +' v LEN)

open LopArgs LopSplit in
/-- split(N, D, w, U, x, y, wi, wj, out, fr). -/
def lopSplitBody (pCount : ℕ) : Stmt :=
  lopSplitCap ;; .set LO (k 0) ;; .while (v LO <' v W) (lopSplitPiece pCount)

/-- The length of the pieces: max(1, min(⌊n²/√D⌋, w)). -/
def lopCapW (n D w : ℕ) : ℕ := max 1 (min (queryCapNat n D) w)

/-- The number of steps of split, if the solver takes Tn: one call for each piece. -/
def lopSplitTime (Tn : List ℕ → ℕ) : List ℕ → ℕ
  | [n, D, w] =>
    (∑ i ∈ Finset.range (w ⌈/⌉ lopCapW n D w),
      (Tn [n, D, min (lopCapW n D w) (w - i * lopCapW n D w)] + 38)) + 22 * w + 22
  | _ => 0

/-- What split needs: words for n⁴ and w² D, one more level of calls, and what the solver needs for
any number of query pairs up to w. -/
def lopSplitNeed (need : List ℕ → Need) : List ℕ → Need
  | [n, D, w] =>
    ⟨n ^ 4 + w * w * D + 2 + (Finset.range (w + 1)).sup fun l => (need [n, D, l]).word,
      (Finset.range (w + 1)).sup fun l => (need [n, D, l]).cells,
      1 + (Finset.range (w + 1)).sup fun l => (need [n, D, l]).depth⟩
  | _ => ⟨0, 0, 0⟩

namespace LopSplitHost

/-! ## Pieces -/

theorem one_le_capW (n D w : ℕ) : 1 ≤ lopCapW n D w := le_max_left _ _

theorem splitCap_eq (n : ℕ) {D : ℕ} (hD : 1 ≤ D) : splitCap n D = max 1 (queryCapNat n D) := by
  rw [splitCap, ← queryCapNat_eq n hD]

theorem capW_le_splitCap (n : ℕ) {D : ℕ} (hD : 1 ≤ D) (w : ℕ) : lopCapW n D w ≤ splitCap n D := by
  rw [splitCap_eq n hD]
  unfold lopCapW
  omega

/-- The number of pieces for w query pairs is at most the number of pieces of the claim,
⌈w'/splitCap n D⌉, for every w' ≥ w. -/
theorem ceilDiv_capW_le (n : ℕ) {D : ℕ} (hD : 1 ≤ D) {w w' : ℕ} (hw : w ≤ w') :
    w ⌈/⌉ lopCapW n D w ≤ ⌈(w' : ℝ) / (splitCap n D : ℝ)⌉₊ := by
  generalize hm : ⌈(w' : ℝ) / (splitCap n D : ℝ)⌉₊ = m
  have hS : 1 ≤ splitCap n D := le_max_left _ _
  have hSpos : (0 : ℝ) < (splitCap n D : ℝ) := by exact_mod_cast hS
  have hceil : (w' : ℝ) / (splitCap n D : ℝ) ≤ m := hm ▸ Nat.le_ceil _
  rw [div_le_iff₀ hSpos] at hceil
  have hcover : w' ≤ m * splitCap n D := by exact_mod_cast hceil
  -- If m pieces of the computed length did not cover w, then m pieces of the claim's length would
  -- not cover w' either.
  by_contra hcon
  have hshort : m * lopCapW n D w < w :=
    (Nat.lt_ceilDiv_iff (one_le_capW n D w)).1 (show m < w ⌈/⌉ lopCapW n D w by omega)
  rw [splitCap_eq n hD] at hcover
  by_cases hcw : queryCapNat n D ≤ w
  · have : lopCapW n D w = max 1 (queryCapNat n D) := by unfold lopCapW; omega
    rw [this] at hshort
    omega
  · have e : lopCapW n D w = max 1 w := by unfold lopCapW; omega
    rw [e] at hshort
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simp at hcover
      omega
    · have : max 1 w ≤ m * max 1 w := Nat.le_mul_of_pos_left _ hmpos
      omega

/-- The piece of len query pairs from the query pair number lo on. -/
def piece (x : ThinInst) (lo len : ℕ) : ThinInst :=
  { x with
    w := len, wi := x.wi + lo, wj := x.wj + lo, out := x.out + lo
    WI := (x.WI.drop lo).take len, WJ := (x.WJ.drop lo).take len }

/-- The pairs of a piece are a piece of the list of the pairs. -/
theorem zip_piece (A B : List ℕ) (lo len : ℕ) :
    ((A.drop lo).take len).zip ((B.drop lo).take len) = ((A.zip B).drop lo).take len := by
  simp only [List.zip, List.take_zipWith, List.drop_zipWith]

/-- The answers for a piece are a piece of the list of the answers. -/
theorem thinOut_piece (N D : ℕ) (X Y : List ℤ) (WI WJ : List ℕ) (lo len : ℕ) :
    thinOut N D X Y ((WI.drop lo).take len) ((WJ.drop lo).take len) =
      ((thinOut N D X Y WI WJ).drop lo).take len := by
  unfold thinOut
  rw [zip_piece, List.map_take, List.map_drop]

/-- A piece of an instance is an instance: the matrices are the same, and its query pairs and its
answers lie within those of the instance. -/
theorem piece_pre {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr) {lo len : ℕ}
    (hl : lo + len ≤ x.w) : (piece x lo len).Pre μ fr := by
  light_facts h
  exact
    { h with
      lenWI := by simp only [piece, List.length_take, List.length_drop]; omega
      lenWJ := by simp only [piece, List.length_take, List.length_drop]; omega
      segWI := by
        have := (Seg.drop h.segWI lo).take len
        simpa only [SegN, piece, List.map_take, List.map_drop] using this
      segWJ := by
        have := (Seg.drop h.segWJ lo).take len
        simpa only [SegN, piece, List.map_take, List.map_drop] using this
      ltWI := fun i hi => h.ltWI i (List.mem_of_mem_drop (List.mem_of_mem_take hi))
      ltWJ := fun i hi => h.ltWJ i (List.mem_of_mem_drop (List.mem_of_mem_take hi))
      nodup := by
        simp only [piece, zip_piece]
        exact List.Nodup.sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _)) h.nodup
      belowWI := by simp only [piece]; omega
      belowWJ := by simp only [piece]; omega
      belowOut := by simp only [piece]; omega
      apartX := by simp only [piece]; omega
      apartY := by simp only [piece]; omega
      apartWI := by simp only [piece]; omega
      apartWJ := by simp only [piece]; omega }

/-- An instance stays where it is if no cell below the free pointer changes, except the answers. -/
theorem pre_keptBut {x : ThinInst} {μ μ' : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr)
    (hk : KeptBut μ μ' fr x.out x.w) : x.Pre μ' fr := by
  have keep : ∀ (a len : ℕ), a + len ≤ fr → Apart x.out x.w a len →
      ∀ i < len, μ' (a + i) = μ (a + i) := by
    intro a len hb hap i hi
    refine hk _ ⟨by omega, ?_⟩
    rcases hap with h1 | h1 <;> omega
  exact
    { h with
      segX := h.segX.congr fun i hi => keep _ _ h.belowX h.apartX i (by rw [← h.lenX]; exact hi)
      segY := h.segY.congr fun i hi => keep _ _ h.belowY h.apartY i (by rw [← h.lenY]; exact hi)
      segWI := Seg.congr h.segWI fun i hi => keep _ _ h.belowWI h.apartWI i
        (by rw [← h.lenWI]; simpa using hi)
      segWJ := Seg.congr h.segWJ fun i hi => keep _ _ h.belowWJ h.apartWJ i
        (by rw [← h.lenWJ]; simpa using hi) }

/-! ## The host -/

/-- What split needs covers what the solver needs for a piece. -/
theorem ok_piece {need : List ℕ → Need} {n D w fr l : ℕ}
    (hok : (lopSplitNeed need [n, D, w]).Ok lim fr d) (hl : l ≤ w) :
    (need [n, D, l]).Ok lim fr (d + 1) := by
  have hm : l ∈ Finset.range (w + 1) := Finset.mem_range.2 (by omega)
  have h1 := Finset.le_sup (f := fun l => (need [n, D, l]).word) hm
  have h2 := Finset.le_sup (f := fun l => (need [n, D, l]).cells) hm
  have h3 := Finset.le_sup (f := fun l => (need [n, D, l]).depth) hm
  refine hok.mono ?_ ?_ ?_ <;> simp only [lopSplitNeed] <;> omega

/-- The local variables of split, as a list. -/
abbrev locals (x : ThinInst) (fr : ℕ) (c n4 lo len res : ℤ) : List ℤ :=
  [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr, c, n4, lo, len, res]

open LopArgs LopSplit in
/-- **The counting**: from c = 1 and lo = w it ends with c = max(1, min(⌊N²/√D⌋, w)). -/
theorem lopSplitCount_spec {P : Program} (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) {N₄ w2 : ℕ}
    (hD : 1 ≤ x.D) (hn4 : x.N ^ 4 = N₄) (hw2 : x.w * x.w * x.D = w2)
    (hword : ((N₄ + w2 + 2 : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d lopSplitCount ⟨frame (locals x fr (1 : ℕ) N₄ x.w 0 0), μ⟩ (22 * x.w + 4) fun σ' =>
      ∃ lo : ℤ, σ' = ⟨frame (locals x fr (lopCapW x.N x.D x.w : ℕ) N₄ lo 0 0), μ⟩ := by
  -- while c < lo; the counting has reached a, and it goes on (lo = w) or has ended (lo = a = c)
  refine Ends.whileVariant
    (fun σ => ∃ a l : ℕ, σ = ⟨frame (locals x fr a N₄ l 0 0), μ⟩ ∧ 1 ≤ a ∧
      a ≤ lopCapW x.N x.D x.w ∧ (l = x.w ∨ (l = a ∧ a = lopCapW x.N x.D x.w)))
    (fun σ => (σ.loc LO - σ.loc C).toNat) 18 ?start (fun _ _ => ⟨trivial, trivial⟩) ?round ?done
    (by simp; omega)
  case start => exact ⟨1, x.w, rfl, le_rfl, one_le_capW _ _ _, Or.inl rfl⟩
  case done =>
    rintro _ ⟨a, l, rfl, ha1, hac, hl⟩ hlt
    have hle : l ≤ a := by simp at hlt; omega
    obtain rfl : a = lopCapW x.N x.D x.w := by
      unfold lopCapW at hac hl ⊢
      omega
    exact ⟨l, rfl⟩
  case round =>
    rintro _ ⟨a, l, rfl, ha1, hac, hl⟩ hlt
    have hal : a < l := by simp at hlt; omega
    obtain rfl : l = x.w := by omega
    -- The numbers that the test forms are at most w² D.
    have m1 : (a + 1) * (a + 1) ≤ x.w * x.w := Nat.mul_le_mul hal hal
    have m2 : ((a : ℤ) + 1) * ((a : ℤ) + 1) * x.D ≤ w2 := by
      exact_mod_cast hw2 ▸ Nat.mul_le_mul_right x.D m1
    have m3 : ((a : ℤ) + 1) * ((a : ℤ) + 1) ≤ ((a : ℤ) + 1) * ((a : ℤ) + 1) * x.D := by
      exact_mod_cast Nat.le_mul_of_pos_right ((a + 1) * (a + 1)) hD
    have m4 : (a : ℤ) + 1 ≤ ((a : ℤ) + 1) * ((a : ℤ) + 1) := by
      exact_mod_cast Nat.le_mul_of_pos_right (a + 1) (show 0 < a + 1 by omega)
    have hiff := queryCapNat_succ_le_iff (n := x.N) hD a
    rw [hn4] at hiff
    -- if (c + 1)² D ≤ n4 then c := c + 1 else lo := c
    refine Ends.iteLast (fun hcond => ?_) (fun hcond => ?_) (by light_side)
    · have hcap : a + 1 ≤ queryCapNat x.N x.D := hiff.2 (by
        have h := Cond.holds_le.1 hcond
        simp at h
        exact_mod_cast h)
      refine Ends.setTo (a + 1 : ℕ) ⟨⟨a + 1, x.w, rfl, by omega, ?_, Or.inl rfl⟩, by simp; omega⟩
      unfold lopCapW
      omega
    · have hcap : ¬ a + 1 ≤ queryCapNat x.N x.D := fun h => hcond (Cond.holds_le.2 (by
        have h := hiff.1 h
        simp
        exact_mod_cast h))
      refine Ends.setTo (a : ℕ) ⟨⟨a, a, rfl, ha1, hac, Or.inr ⟨rfl, ?_⟩⟩, by simp; omega⟩
      unfold lopCapW at hac ⊢
      omega

open LopArgs LopSplit in
/-- **The length of the pieces.** -/
theorem lopSplitCap_spec {P : Program} (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (hN : 1 ≤ x.N)
    (hD : 1 ≤ x.D) (hword : ((x.N ^ 4 + x.w * x.w * x.D + 2 : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d lopSplitCap
      ⟨frame [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out, fr], μ⟩ (22 * x.w + 16) fun σ' =>
        ∃ lo : ℤ, σ' = ⟨frame (locals x fr (lopCapW x.N x.D x.w : ℕ) (x.N ^ 4 : ℕ) lo 0 0), μ⟩ := by
  have n2 : (x.N : ℤ) * x.N ≤ (x.N ^ 4 : ℕ) := by
    have h : x.N ^ 2 ≤ x.N ^ 4 := Nat.pow_le_pow_right hN (by norm_num)
    rw [sq] at h
    exact_mod_cast h
  have n3 : (x.N : ℤ) * x.N * x.N ≤ (x.N ^ 4 : ℕ) := by
    have h : x.N ^ 3 ≤ x.N ^ 4 := Nat.pow_le_pow_right hN (by norm_num)
    rw [pow_succ, sq] at h
    exact_mod_cast h
  have n4 : (x.N : ℤ) * x.N * x.N * x.N = (x.N ^ 4 : ℕ) := by
    push_cast
    ring
  have p2 : (0 : ℤ) ≤ (x.N : ℤ) * x.N := by positivity
  have p3 : (0 : ℤ) ≤ (x.N : ℤ) * x.N * x.N := by positivity
  generalize hn4 : x.N ^ 4 = N₄ at *
  generalize hw2 : x.w * x.w * x.D = w2 at hword
  -- c := 1; n4 := N N N N; lo := w
  light_set (1 : ℕ)
  light_set (N₄ : ℕ)
  light_set (x.w : ℕ)
  rw [← frame_append_zeros _ 2]
  light_piece (lopSplitCount_spec x μ fr hD hn4 hw2 hword)

open LopArgs LopSplit in
/-- **One piece**: the solver answers the query pairs lo, …, lo + len - 1, where
len = min(c, w - lo). -/
theorem lopSplitPiece_spec {P₀ R : Program} {p : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    (hsol : SolvesN lopCountTask P₀ p Tn need) {x : ThinInst} {μ μ' : ℕ → ℤ} {fr : ℕ}
    (hpre : lopCountTask.Pre x μ fr) (hok : (lopSplitNeed need [x.N, x.D, x.w]).Ok lim fr d)
    {c lo : ℕ} (n4 len₀ res₀ : ℤ) (hlo : lo < x.w)
    (hseg : Seg μ' x.out ((thinOut x.N x.D x.X x.Y x.WI x.WJ).take lo))
    (hk : KeptBut μ μ' fr x.out x.w) :
    Ends lim (P₀ ++ R) d (lopSplitPiece p) ⟨frame (locals x fr c n4 lo len₀ res₀), μ'⟩
      (Tn [x.N, x.D, min c (x.w - lo)] + 34) fun σ' => ∃ (res : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame (locals x fr c n4 (lo + min c (x.w - lo) : ℕ) (min c (x.w - lo) : ℕ) res),
          μ''⟩ ∧
        Seg μ'' x.out ((thinOut x.N x.D x.X x.Y x.WI x.WJ).take (lo + min c (x.w - lo))) ∧
        KeptBut μ μ'' fr x.out x.w := by
  obtain ⟨hp1, hzo, hU⟩ := hpre
  have hw := hok.space
  have hcells := hok.cells
  have hdep : d < lim.depth := by
    have := hok.depth
    simp only [lopSplitNeed] at this
    omega
  light_facts hp1
  have hlen := LopHosts.length_thinOut x.N x.D x.X x.Y hp1.lenWI hp1.lenWJ
  generalize hl : min c (x.w - lo) = len
  -- res := solver(N, D, len, U, x, y, wi + lo, wj + lo, out + lo, fr); lo := lo + len
  have fin : Ends lim (P₀ ++ R) d
      (.call p [v N, v DD, v LEN, v U, v X, v Y, v WI +' v LO, v WJ +' v LO, v OUT +' v LO, v FR]
        RES ;; .set LO (v LO +' v LEN)) ⟨frame (locals x fr c n4 lo len res₀), μ'⟩
      (Tn [x.N, x.D, len] + 22) fun σ' => ∃ (res : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame (locals x fr c n4 (lo + len : ℕ) len res), μ''⟩ ∧
        Seg μ'' x.out ((thinOut x.N x.D x.X x.Y x.WI x.WJ).take (lo + len)) ∧
        KeptBut μ μ'' fr x.out x.w := by
    have hm : Meets lim (P₀ ++ R) p (d + 1)
        [x.N, x.D, len, x.U, x.x, x.y, (x.wi + lo : ℕ), (x.wj + lo : ℕ), (x.out + lo : ℕ), fr] μ'
        (Tn [x.N, x.D, len]) fun _ μ'' =>
          Seg μ'' (x.out + lo)
            (thinOut x.N x.D x.X x.Y ((x.WI.drop lo).take len) ((x.WJ.drop lo).take len)) ∧
          KeptBut μ' μ'' fr (x.out + lo) len :=
      hsol.meets R (piece x lo len) ⟨piece_pre (pre_keptBut hp1 hk) (by omega), hzo, hU⟩
        (ok_piece (l := len) hok (by omega))
    refine Ends.callToThen hm fun r μ'' ⟨hseg3, hk3⟩ => ?_
    rw [thinOut_piece] at hseg3
    refine Ends.setTo (lo + len : ℕ) ⟨r, μ'', rfl, ?_, fun b hb => ?_⟩
    · rw [List.take_add, seg_append, List.length_take, hlen, Nat.min_eq_left hlo.le]
      exact ⟨hseg.congr fun j hj => hk3 _ (by simp [hlen] at hj; omega), hseg3⟩
    · rw [hk3 b (by omega)]
      exact hk b hb
  -- len := c
  light_set (c : ℕ)
  -- if w - lo < c then len := w - lo
  refine Ends.next 10 (Ends.iteLast (fun h => ?_) (fun h => ?_))
  · obtain rfl : len = x.w - lo := by simp at h; omega
    exact Ends.setTo (x.w - lo : ℕ) fin
  · obtain rfl : len = c := by simp at h; omega
    exact Ends.skip fin

open LopArgs LopSplit in
/-- **split** solves #Lop-AE-SparseTri. -/
theorem split_spec {P₀ R : Program} {p : ℕ} {Tn : List ℕ → ℕ} {need : List ℕ → Need}
    (hsol : SolvesN lopCountTask P₀ p Tn need) {x : ThinInst} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : lopCountTask.Pre x μ fr) (hok : (lopSplitNeed need [x.N, x.D, x.w]).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (lopSplitBody p) ⟨frame (lopCountTask.args x ++ [(fr : ℤ)]), μ⟩
      (lopSplitTime Tn [x.N, x.D, x.w]) fun σ' => lopCountTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  have hp1 := hpre.1
  have hcells := hok.cells
  light_facts hok hp1
  have hword : ((x.N ^ 4 + x.w * x.w * x.D + 2 : ℕ) : ℤ) ≤ lim.word :=
    le_trans (by simp only [lopSplitNeed]; exact_mod_cast (by omega)) hok.word
  have hlen := LopHosts.length_thinOut x.N x.D x.X x.Y hp1.lenWI hp1.lenWJ
  simp only [lopSplitTime]
  generalize hc : lopCapW x.N x.D x.w = c
  have hc1 : 1 ≤ c := hc ▸ one_le_capW _ _ _
  -- c := the length of the pieces
  light_piece (lopSplitCap_spec x μ fr hp1.N_pos hp1.D_pos hword) with _ ⟨lo, rfl⟩
  rw [hc]
  -- lo := 0
  light_set (0 : ℕ)
  -- while lo < w; before round i the first i pieces are answered
  refine (Ends.while (fun i σ => ∃ (len res : ℤ) (μ' : ℕ → ℤ),
      σ = ⟨frame (locals x fr c (x.N ^ 4 : ℕ) (min (i * c) x.w : ℕ) len res), μ'⟩ ∧
      Seg μ' x.out ((thinOut x.N x.D x.X x.Y x.WI x.WJ).take (min (i * c) x.w)) ∧
      KeptBut μ μ' fr x.out x.w)
    (x.w ⌈/⌉ c) (fun i => Tn [x.N, x.D, min c (x.w - i * c)] + 34) ?start ?round ?done).mono
    ?time fun _ h => h
  case time =>
    rw [Finset.sum_congr rfl fun i _ =>
      show (v LO <' v W).cost + 1 + (Tn [x.N, x.D, min c (x.w - i * c)] + 34)
        = Tn [x.N, x.D, min c (x.w - i * c)] + 38 by simp only [Cond.cost, Expr.cost]; omega]
    simp only [Cond.cost, Expr.cost]
    omega
  case start =>
    exact ⟨0, 0, μ, by rw [Nat.zero_mul, Nat.zero_min]; rfl, by simp, fun _ _ => rfl⟩
  case done =>
    rintro _ ⟨len, res, μ', rfl, hseg, hk⟩
    have hcover : x.w ≤ x.w ⌈/⌉ c * c := Nat.le_ceilDiv_mul hc1
    rw [Nat.min_eq_right hcover] at hseg ⊢
    refine ⟨by light_side, by light_side, ?_, hk⟩
    rwa [← hlen, List.take_length] at hseg
  case round =>
    rintro i _ hi ⟨len, res, μ', rfl, hseg, hk⟩
    have hilt : i * c < x.w := (Nat.lt_ceilDiv_iff hc1).1 hi
    have hnext : min ((i + 1) * c) x.w = i * c + min c (x.w - i * c) := by
      have : (i + 1) * c = i * c + c := by ring
      omega
    rw [Nat.min_eq_left hilt.le] at hseg ⊢
    rw [hnext]
    refine ⟨by light_side, by light_side,
      (lopSplitPiece_spec hsol hpre hok _ len res hilt hseg hk).mono le_rfl ?_⟩
    rintro _ ⟨res', μ'', rfl, hseg', hk'⟩
    exact ⟨_, res', μ'', rfl, hseg', hk'⟩

/-! ## The need stays polynomial -/

/-- The numbers that the host itself forms: each parameter is at most X = (n + 1) (D + 1) (w + 1),
so n⁴ + w² D + 2 ≤ X⁴ + X³ + 2 ≤ 4 X⁴. -/
private theorem own_le_polyBound (n D w : ℕ) :
    n ^ 4 + w * w * D + 2 ≤ polyBound 2 4 [n, D, w] := by
  rw [show polyBound 2 4 [n, D, w] = 4 * ((n + 1) * ((D + 1) * (w + 1))) ^ 4 by simp [polyBound]]
  have hn : n + 1 ≤ (n + 1) * ((D + 1) * (w + 1)) := Nat.le_mul_of_pos_right _ (by positivity)
  have hDw : (D + 1) * (w + 1) ≤ (n + 1) * ((D + 1) * (w + 1)) :=
    Nat.le_mul_of_pos_left _ n.succ_pos
  have hD : D + 1 ≤ (D + 1) * (w + 1) := Nat.le_mul_of_pos_right _ w.succ_pos
  have hw : w + 1 ≤ (D + 1) * (w + 1) := Nat.le_mul_of_pos_left _ D.succ_pos
  generalize (n + 1) * ((D + 1) * (w + 1)) = X at *
  have hn' : n ≤ X := by omega
  have hD' : D ≤ X := by omega
  have hw' : w ≤ X := by omega
  have h1 : 1 ≤ X ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h4 : n ^ 4 ≤ X ^ 4 := by gcongr
  have h3 : w * w * D ≤ X ^ 4 :=
    calc w * w * D ≤ X * X * X := by gcongr
      _ = X ^ 3 := by ring
      _ ≤ X ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

/-- What the solver needs on the pieces, which have at most w query pairs. -/
private theorem sup_le_polyBound {f : List ℕ → ℕ} {s e : ℕ} (hf : ∀ ps, f ps ≤ polyBound s e ps)
    (n D w : ℕ) : ((Finset.range (w + 1)).sup fun l => f [n, D, l]) ≤ polyBound s e [n, D, w] := by
  refine Finset.sup_le fun l hl => (hf _).trans ?_
  have hl' : l ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hl)
  simp only [polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  gcongr

/-- The need of the host is polynomially bounded if that of the solver is. -/
theorem polyNeedN_split {need : List ℕ → Need} (h : PolyNeedN need) :
    PolyNeedN (lopSplitNeed need) := by
  obtain ⟨s, e, h⟩ := h
  refine ⟨1 + (2 + s), 4 + e, fun ps => ?_⟩
  match ps with
  | [n, D, w] =>
    have own := own_le_polyBound n D w
    exact ⟨add_le_polyBound own (sup_le_polyBound (fun ps => (h ps).1) n D w),
      (sup_le_polyBound (fun ps => (h ps).2.1) n D w).trans
        (polyBound_mono (by omega) (by omega) _),
      add_le_polyBound (le_trans (by omega) own) (sup_le_polyBound (fun ps => (h ps).2.2) n D w)⟩
  | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ =>
    exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

end LopSplitHost

open LopSplitHost

/-- **Corollary 15, the general case**: a solver for the instances
of #Lop-AE-SparseTri(n, D) with at most n²/√D query pairs gives one for every set W of query pairs.
"For larger W, apply the theorem [Theorem 5] to each of at most ⌈|W|√D/n²⌉ + 1 pieces." -/
theorem claim_lopSplit : Claim.LopSplit lightModel := by
  refine ⟨38, fun T hT => ?_⟩
  obtain ⟨P, p, Tn, need, hneed, hsol, htime⟩ := hT
  refine ⟨P ++ [lopSplitBody p], P.length, lopSplitTime Tn, lopSplitNeed need, polyNeedN_split
    hneed, ?_, fun n D w w' hn hD hw => ?_⟩
  · refine ⟨lopSplitBody p, by simp, fun R lim d x μ fr hpre hok => ?_⟩
    rw [List.append_assoc]
    exact split_spec hsol hpre hok
  · beta_reduce
    generalize hS : splitCap n D = S
    have hTS : ∀ l ≤ S, (Tn [n, D, l] : ℝ) ≤ T n D S := fun l hl => htime n D l S hn hD hl
    have hT0 : (0 : ℝ) ≤ T n D S := le_trans (by positivity) (hTS 0 (Nat.zero_le _))
    have hR : ((w ⌈/⌉ lopCapW n D w : ℕ) : ℝ) ≤ (⌈(w' : ℝ) / (S : ℝ)⌉₊ : ℝ) := by
      rw [← hS]
      exact_mod_cast ceilDiv_capW_le n hD hw
    have hsum : ((∑ i ∈ Finset.range (w ⌈/⌉ lopCapW n D w),
      (Tn [n, D, min (lopCapW n D w) (w - i * lopCapW n D w)] + 38) : ℕ) : ℝ) ≤
        ((w ⌈/⌉ lopCapW n D w : ℕ) : ℝ) * (T n D S + 38) := by
      push_cast
      calc ∑ i ∈ Finset.range (w ⌈/⌉ lopCapW n D w),
        ((Tn [n, D, min (lopCapW n D w) (w - i * lopCapW n D w)] : ℝ) + 38)
          ≤ ∑ _i ∈ Finset.range (w ⌈/⌉ lopCapW n D w), (T n D S + 38) :=
            Finset.sum_le_sum fun i _ => by
              have := hTS (min (lopCapW n D w) (w - i * lopCapW n D w))
                ((Nat.min_le_left _ _).trans (hS ▸ capW_le_splitCap n hD w))
              linarith
        _ = ((w ⌈/⌉ lopCapW n D w : ℕ) : ℝ) * (T n D S + 38) := by simp; ring
    have hnD : (0 : ℝ) ≤ (n : ℝ) * (D : ℝ) := by positivity
    have h1 : ((w ⌈/⌉ lopCapW n D w : ℕ) : ℝ) * (T n D S + 38) ≤ (⌈(w' : ℝ) / (S : ℝ)⌉₊ : ℝ) *
      (T n D S + 38 * ((n : ℝ) * (D : ℝ) + 1)) :=
      mul_le_mul hR (by linarith) (by linarith) (by positivity)
    have h2 : (w : ℝ) ≤ w' := by exact_mod_cast hw
    simp only [lopSplitTime]
    push_cast at hsum ⊢
    linarith

end Light.Sec3
