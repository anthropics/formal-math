/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.Scan

/-!
# Reading the answers of one instance and scanning for witnesses

Proof of Theorem 17: "For every query pair that the oracle accepts, scan the piece C_k of its
instance for a c with S(a,b,c) = 0 [...].  We stop as soon as a zero triangle is found."

scanPairs(out, qa, qb, w, f, ab, bc, ac, n, c0, len): for every query pair number `i < w` whose
answer `out[i]` is not 0, scan the piece `{c0, …, c0 + len - 1}` for a zero triangle through the
pair `(qa[i], qb[i])`, as long as none has been found (`f = 0`).  The result is the new value of `f`
(`scanPairs_spec`).  No scan is made after the first successful one, so the number of scans is at
most the number of failed scans plus one (`execsUpto_le`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The pure side -/

/-- Whether a zero triangle has been found before the pair number i; acc j: the answer for the pair
j is not 0; hit j: its scan succeeds. -/
def foundAt (acc hit : ℕ → Bool) (f : Bool) (i : ℕ) : Bool :=
  f || (List.range i).any fun j => acc j && hit j

/-- Whether the pair number i is scanned. -/
def execAt (acc hit : ℕ → Bool) (f : Bool) (i : ℕ) : Bool := acc i && !foundAt acc hit f i

/-- The number of scans among the first w pairs. -/
def execsUpto (acc hit : ℕ → Bool) (f : Bool) (w : ℕ) : ℕ :=
  ((List.range w).filter (execAt acc hit f)).length

/-- The number of accepted pairs among the first w whose scan would fail. -/
def failsUpto (acc hit : ℕ → Bool) (w : ℕ) : ℕ :=
  ((List.range w).filter fun i => acc i && !hit i).length

theorem foundAt_zero (acc hit : ℕ → Bool) (f : Bool) : foundAt acc hit f 0 = f := by simp [foundAt]

theorem foundAt_succ (acc hit : ℕ → Bool) (f : Bool) (i : ℕ) :
    foundAt acc hit f (i + 1) = (foundAt acc hit f i || (acc i && hit i)) := by
  simp [foundAt, List.range_succ, Bool.or_assoc]

theorem execsUpto_succ (acc hit : ℕ → Bool) (f : Bool) (w : ℕ) :
    execsUpto acc hit f (w + 1) =
      execsUpto acc hit f w + (if execAt acc hit f w then 1 else 0) := by
  simp only [execsUpto, List.range_succ, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  split_ifs <;> rfl

theorem failsUpto_succ (acc hit : ℕ → Bool) (w : ℕ) :
    failsUpto acc hit (w + 1) = failsUpto acc hit w + (if acc w && !hit w then 1 else 0) := by
  simp only [failsUpto, List.range_succ, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  split_ifs <;> rfl

/-- **All scans but one fail.** -/
theorem execsUpto_le (acc hit : ℕ → Bool) (f : Bool) (w : ℕ) :
    execsUpto acc hit f w + f.toNat ≤ failsUpto acc hit w + (foundAt acc hit f w).toNat := by
  induction w with
  | zero => simp [execsUpto, failsUpto, foundAt_zero]
  | succ w ih =>
    rw [execsUpto_succ, failsUpto_succ, foundAt_succ, execAt]
    rcases ha : acc w <;> rcases hh : hit w <;> rcases hf : foundAt acc hit f w <;>
      simp [hf] at ih ⊢ <;> omega

/-! ## The routine -/

namespace ScanPairs

/-- The locals of `scanPairs`.  The arguments: the addresses of the answers and of the rows and the
columns of the query pairs, their number `w`, the flag `f`, the addresses of the three arrays of
weights, `n`, and the first vertex and the number of vertices of the piece.  Then the counter. -/
abbrev Out : ℕ := 0
@[inherit_doc Out] abbrev Rows : ℕ := 1
@[inherit_doc Out] abbrev Cols : ℕ := 2
@[inherit_doc Out] abbrev Num : ℕ := 3
@[inherit_doc Out] abbrev Found : ℕ := 4
@[inherit_doc Out] abbrev AdrAB : ℕ := 5
@[inherit_doc Out] abbrev AdrBC : ℕ := 6
@[inherit_doc Out] abbrev AdrAC : ℕ := 7
@[inherit_doc Out] abbrev Size : ℕ := 8
@[inherit_doc Out] abbrev First : ℕ := 9
@[inherit_doc Out] abbrev Len : ℕ := 10
@[inherit_doc Out] abbrev Cnt : ℕ := 11

end ScanPairs

open ScanPairs in
/-- One query pair: if out[i] ≠ 0 and f = 0 then f := scan(ab, bc, ac, n, qa[i], qb[i], c0, len). -/
def scanPairsStep (pScan : ℕ) : Stmt :=
  .ite (M (v Out +' v Cnt) =' k 0) .skip
    (.ite (v Found =' k 0)
      (.call pScan [v AdrAB, v AdrBC, v AdrAC, v Size, M (v Rows +' v Cnt), M (v Cols +' v Cnt),
        v First, v Len] Found) .skip)

open ScanPairs in
/-- scanPairs(out, qa, qb, w, f, ab, bc, ac, n, c0, len); the parameter is the procedure number of
`scan`. -/
def scanPairsBody (pScan : ℕ) : Stmt :=
  .set Cnt (k 0) ;;
  .while (v Cnt <' v Num) (scanPairsStep pScan ;; .set Cnt (v Cnt +' k 1)) ;;
  .set 0 (v Found)

/-- The time for reading w answers. -/
def tAnswers (w : ℕ) : ℕ := 19 * w + 8

/-- The time of one scan of a piece of len vertices, with its call. -/
def tScanCall (len : ℕ) : ℕ := tScan len + 16

/-- The time of scanPairs, given the number of scans. -/
def tScanPairs (w len execs : ℕ) : ℕ := tAnswers w + tScanCall len * execs

/-- What `scanPairs` assumes about the answers of the solver and the `w` query pairs of an instance:
three arrays in the memory, and the query pairs are pairs of vertices. -/
structure Answers (lim : Limits) (μ : ℕ → ℤ) (out qa qb w n : ℕ) (OUT : List ℤ) (QA QB : List ℕ) :
    Prop where
  arrOUT : ListAt μ out OUT w lim.space
  arrQA : IndexAt μ qa QA w n lim.space
  arrQB : IndexAt μ qb QB w n lim.space
  w_lt : w < lim.space

section

variable {pScan : ℕ} {μ : ℕ → ℤ} {out qa qb w ab bc ac n c0 len U : ℕ} {OUT AB BC AC : List ℤ}
  {QA QB : List ℕ} {f : Bool}

/-- The answer for the query pair number `i` is not 0. -/
abbrev accOf (OUT : List ℤ) (i : ℕ) : Bool := decide (OUT.getD i 0 ≠ 0)

/-- The scan for the query pair number `i` succeeds. -/
abbrev hitOf (n : ℕ) (AB BC AC : List ℤ) (QA QB : List ℕ) (c0 len i : ℕ) : Bool :=
  scanHit n AB BC AC (QA.getD i 0) (QB.getD i 0) c0 len

/-- The state of `scanPairs` when `i` query pairs have been treated and the counter is `j`. -/
def scanPairsState (μ : ℕ → ℤ) (out qa qb w ab bc ac n c0 len : ℕ) (OUT AB BC AC : List ℤ)
    (QA QB : List ℕ) (f : Bool) (i j : ℕ) : State :=
  ⟨frame [out, qa, qb, w, bit (foundAt (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f i), ab, bc, ac,
    n, c0, len, j], μ⟩

/-- One query pair: a scan is made if the pair is accepted and nothing has been found yet. -/
theorem scanPairsStep_spec (hp : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (A : Answers lim μ out qa qb w n OUT QA QB)
    (hd : d < lim.depth) (hc : c0 + len ≤ n) {i : ℕ} (hi : i < w) :
    Ends lim P d (scanPairsStep pScan)
      (scanPairsState μ out qa qb w ab bc ac n c0 len OUT AB BC AC QA QB f i i)
      (11 + if execAt (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f i then tScanCall len else 0)
      (· = scanPairsState μ out qa qb w ab bc ac n c0 len OUT AB BC AC QA QB f (i + 1) i) := by
  light_facts C C.arrAB C.arrBC C.arrAC
  light_facts A A.arrOUT A.arrQA A.arrQB
  have hreadOUT := A.arrOUT.read hi
  have hreadQA := A.arrQA.read hi
  have hreadQB := A.arrQB.read hi
  have ha := A.arrQA.getD_lt hi
  have hb := A.arrQB.getD_lt hi
  unfold scanPairsStep scanPairsState
  rw [foundAt_succ, execAt, accOf, hitOf]
  -- The answer, the pair, and whether a zero triangle has been found before.
  generalize foundAt (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f i = found
  generalize OUT.getD i 0 = answer at hreadOUT ⊢
  generalize QA.getD i 0 = a at hreadQA ha ⊢
  generalize QB.getD i 0 = b at hreadQB hb ⊢
  -- if out[i] = 0
  by_cases hz : answer = 0
  · exact Ends.iteLast (fun _ => Ends.skip (by simp [hz]))
      (fun h => absurd (by simp [hreadOUT, hz]) h) (by light_side)
  refine Ends.iteLast (fun h => absurd h (by simp [hreadOUT, hz])) (fun _ => ?_)
    (by light_side)
  -- if f = 0
  cases found
  · refine Ends.iteLast (fun _ => ?_) fun h => absurd (by simp [bit]) h
    -- f := scan(ab, bc, ac, n, qa[i], qb[i], c0, len)
    refine Ends.callTo (scan_meets hp C ha hb hc) ?_
      (by light_side [hreadQA, hreadQB])
      (hT := by simp [hz, tScanCall]; omega)
    rintro _ _ ⟨rfl, rfl⟩
    simp [hz, flag_eq_bit]
  · exact Ends.iteLast (fun h => absurd h (by simp [bit])) fun _ => Ends.skip (by simp)

/-- The time of the rounds, added up: 19 steps for each query pair, and the scans. -/
theorem sum_scanPairs_rounds (acc hit : ℕ → Bool) (f : Bool) (len w : ℕ) :
    ∑ i ∈ Finset.range w, (4 + (15 + if execAt acc hit f i then tScanCall len else 0))
      = 19 * w + tScanCall len * execsUpto acc hit f w := by
  induction w with
  | zero => simp [execsUpto]
  | succ w ih =>
    rw [Finset.sum_range_succ, ih, execsUpto_succ]
    split_ifs <;> ring

/-- **scanPairs** returns the new value of `f`; no cell changes; the time depends on the number of
scans that are made. -/
theorem scanPairs_spec (hp : P[pScan]? = some scanBody) (C : Weights lim μ ab bc ac n U AB BC AC)
    (A : Answers lim μ out qa qb w n OUT QA QB) (hd : d < lim.depth) (hc : c0 + len ≤ n) :
    Ends lim P d (scanPairsBody pScan) ⟨frame [out, qa, qb, w, bit f, ab, bc, ac, n, c0, len], μ⟩
      (tScanPairs w len (execsUpto (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f w)) fun σ' =>
      σ'.loc 0 = bit (foundAt (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f w) ∧ σ'.mem = μ := by
  light_facts C C.arrAB C.arrBC C.arrAC
  light_facts A A.arrOUT A.arrQA A.arrQB
  have hsum := sum_scanPairs_rounds (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f len w
  unfold tScanPairs tAnswers
  -- i := 0
  light_set (0 : ℕ)
  -- while i < w
  refine Ends.next _ (Ends.while
    (fun i σ => σ = scanPairsState μ out qa qb w ab bc ac n c0 len OUT AB BC AC QA QB f i i) w
    (fun i => 15 + if execAt (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f i then tScanCall len
      else 0) ?start ?round ?done) (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)
  case start => simp [scanPairsState, foundAt_zero]
  case round =>
    rintro i _ hi rfl
    refine ⟨by simp, by simp [scanPairsState]; omega, ?_⟩
    -- the query pair number i; then i := i + 1
    refine Ends.next _ ((scanPairsStep_spec hp C A hd hc hi).mono le_rfl ?_) (by omega)
    rintro _ rfl
    light_set (i + 1 : ℕ)
    exact by simp [scanPairsState]
  case done =>
    rintro _ rfl
    -- return f
    exact ⟨by simp, by simp [scanPairsState],
      Ends.setTo (bit (foundAt (accOf OUT) (hitOf n AB BC AC QA QB c0 len) f w)) ⟨rfl, rfl⟩
        (by simp) (by simp only [Cond.cost, Expr.cost, Nat.reduceAdd]; omega)⟩

end

end Light.Sec3
