/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Odometer
public import ThreeSumApsp.Programs.Tasks

/-!
# Corollary 39 in the light language: filling a weight matrix of H

Corollary 39: a clique on k vertices of a k-partite graph G is a triangle of a graph H.
The vertices of the first t = k - 3⌊k/3⌋ parts are fixed, and the other parts form three groups.
With gw = ⌊k/3⌋, a vertex of H is a choice of one vertex in each of the gw parts of a group, so a
part of H has N = n^gw vertices; the chosen vertices are the digits of its number in base n, lowest
first.
The weight between a vertex of H in group i and one in group i + 1 is the sum of the weights of G
over a list L of pairs of parts: the pairs between the two groups, the pairs inside group i, the
pairs of a fixed part and a part of group i, and, for one of the three matrices, the pairs of fixed
parts.  This file writes one N × N weight matrix of H, for any list L.

The weights of G stand at g: the weight between vertex u of part p and vertex v of part q in cell
g + ((p k + q) n + u) n + v.  The current choice of one vertex in each part stands in the k cells at
vt.  The weights lie below these cells and below the matrix.  `sumPairs` adds up the weights over L.
`fillMat` runs through all pairs (row, column) of vertices of H by two odometers inside vt and
writes the sums, row by row.

The proof goes from the inside to the outside: the address of a weight (`wAddr_gives`), the sum
(`sumPairs_spec`), one step of an odometer (`inc_spec`, and `incCol_spec` for the column odometer),
and then one invariant, `FillInv`, "before column c of row r all earlier entries are written", which
an entry (`fillEntry_spec`), a row (`fillRow_spec`) and the step to the next row (`nextRow_spec`)
take to its next value; `fillMat_spec` puts them together.
-/

@[expose] public section

namespace Light.Sec5

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The local variables

The local variables 0 to 16 of the hosts for k-Clique, except local 3, which each host uses in its
own way.  `fillMat` and its parts read `Size`, `Weights`, `Side` and `Choice` and assign `Row`,
`Col`, `Place` and `Entry`. -/

namespace KC

/-- n, the number of vertices of a part. -/
abbrev Size : ℕ := 0
/-- U, the bound on the weights. -/
abbrev Bound : ℕ := 1
/-- g, the address of the weights. -/
abbrev Weights : ℕ := 2
/-- N = n^⌊k/3⌋, the side of a matrix of H. -/
abbrev Side : ℕ := 4
/-- n^t, the number of choices of the fixed vertices. -/
abbrev Rounds : ℕ := 5
/-- The address of the k cells of the chosen vertices. -/
abbrev Choice : ℕ := 6
/-- The address of the matrix of H between the groups 0 and 1. -/
abbrev MatAB : ℕ := 7
/-- The address of the matrix of H between the groups 1 and 2. -/
abbrev MatBC : ℕ := 8
/-- The address of the matrix of H between the groups 0 and 2. -/
abbrev MatAC : ℕ := 9
/-- The address of the first cell behind the three matrices. -/
abbrev Behind : ℕ := 10
/-- The number of the current choice of the fixed vertices. -/
abbrev Round : ℕ := 11
/-- The row of the entry that `fillMat` writes next. -/
abbrev Row : ℕ := 12
/-- The column of the entry that `fillMat` writes next. -/
abbrev Col : ℕ := 13
/-- The address of the entry that `fillMat` writes next. -/
abbrev Place : ℕ := 14
/-- The sum for the entry that `fillMat` writes next. -/
abbrev Entry : ℕ := 15
/-- The result of the call of the solver. -/
abbrev Answer : ℕ := 16

end KC

open KC

/-- Four local variables that fillMat and its parts only read.  (fillMat also reads the local that
holds the address of the matrix.) -/
structure FillLocals (loc : ℕ → ℤ) (n g N vt : ℕ) : Prop where
  size : loc Size = n
  weights : loc Weights = g
  side : loc Side = N
  choice : loc Choice = vt

/-- `FillLocals` survives an assignment to `Row`, `Col`, `Place` or `Entry`. -/
theorem FillLocals.update {loc : ℕ → ℤ} {n g N vt : ℕ} (h : FillLocals loc n g N vt) {y : ℕ}
    (hy : y ∈ [Row, Col, Place, Entry]) (z : ℤ) :
    FillLocals (Function.update loc y z) n g N vt := by
  have hne : Size ≠ y ∧ Weights ≠ y ∧ Side ≠ y ∧ Choice ≠ y := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> decide
  exact ⟨(Function.update_of_ne hne.1 _ _).trans h.size,
    (Function.update_of_ne hne.2.1 _ _).trans h.weights,
    (Function.update_of_ne hne.2.2.1 _ _).trans h.side,
    (Function.update_of_ne hne.2.2.2 _ _).trans h.choice⟩

/-! ## The sum of the weights over a list of pairs of parts -/

/-- The place of the weight between vertex u of part p and vertex v of part q. -/
def widx (kk n p u q v : ℕ) : ℕ := ((p * kk + q) * n + u) * n + v

theorem widx_lt {kk n p u q v : ℕ} (hp : p < kk) (hq : q < kk) (hu : u < n) (hv : v < n) :
    widx kk n p u q v < kk * kk * n * n :=
  Nat.mul_add_lt_mul (Nat.mul_add_lt_mul (Nat.mul_add_lt_mul hp hq) hu) hv

/-- The address of the weight between the chosen vertices of the parts p and q. -/
def wAddr (kk p q : ℕ) : Expr :=
  v Weights +' ((k (p * kk + q) *' v Size +' M (v Choice +' k p)) *' v Size +' M (v Choice +' k q))

@[simp] theorem wAddr_cost (kk p q : ℕ) : (wAddr kk p q).cost = 17 := rfl

/-- Add to Entry the weights between the chosen vertices, over a list of pairs of parts. -/
def sumPairs (kk : ℕ) : List (ℕ × ℕ) → Stmt
  | [] => .skip
  | pq :: L => .set Entry (v Entry +' M (wAddr kk pq.1 pq.2)) ;; sumPairs kk L

/-- The cells at vt hold the choice vf: vertex vf p of part p. -/
def ChoiceIs (μ : ℕ → ℤ) (vt kk : ℕ) (vf : ℕ → ℕ) : Prop := ∀ p < kk, μ (vt + p) = (vf p : ℤ)

/-- The total weight between the chosen vertices vf, over the pairs of parts in L. -/
def memSum (μ : ℕ → ℤ) (g kk n : ℕ) (vf : ℕ → ℕ) (L : List (ℕ × ℕ)) : ℤ :=
  (L.map fun pq => μ (g + widx kk n pq.1 (vf pq.1) pq.2 (vf pq.2))).sum

/-- Where things lie, and how large the weights are: the weights and the chosen vertices lie within
the memory, and the weights between parts p < q have absolute value at most U. -/
structure FillCtx (lim : Limits) (μ : ℕ → ℤ) (kk n g vt U : ℕ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  gB : g + kk * kk * n * n ≤ lim.space
  vtB : vt + kk ≤ lim.space
  wle : ∀ p q u v, p < kk → q < kk → p < q → u < n → v < n → |μ (g + widx kk n p u q v)| ≤ (U : ℤ)

section sum

variable {μ μ' loc : ℕ → ℤ} {kk n g N vt U : ℕ} {vf : ℕ → ℕ}

/-- The context only looks at the cells up to the end of the weights. -/
theorem FillCtx.of_kept (C : FillCtx lim μ kk n g vt U) (h : Kept μ μ' (g + kk * kk * n * n)) :
    FillCtx lim μ' kk n g vt U := by
  refine { C with wle := fun p q u v hp hq hpq hu hv => ?_ }
  rw [h _ (by have := widx_lt hp hq hu hv; omega)]
  exact C.wle p q u v hp hq hpq hu hv

/-- The sum only looks at the cells up to the end of the weights. -/
theorem memSum_congr (h : Kept μ μ' (g + kk * kk * n * n)) (hvf : ∀ p < kk, vf p < n)
    {L : List (ℕ × ℕ)} (hL : ∀ pq ∈ L, pq.1 < kk ∧ pq.2 < kk ∧ pq.1 < pq.2) :
    memSum μ' g kk n vf L = memSum μ g kk n vf L := by
  unfold memSum
  refine congrArg List.sum (List.map_congr_left fun pq hpq => ?_)
  obtain ⟨hp, hq, -⟩ := hL pq hpq
  exact h _ (by have := widx_lt hp hq (hvf _ hp) (hvf _ hq); omega)

/-- The address is safe, and its value is g plus the place of the weight. -/
theorem wAddr_gives (C : FillCtx lim μ kk n g vt U) (hloc : FillLocals loc n g N vt)
    (hvt : ChoiceIs μ vt kk vf) (hvf : ∀ p < kk, vf p < n) {p q : ℕ} (hp : p < kk) (hq : q < kk) :
    (wAddr kk p q).Gives lim ⟨loc, μ⟩ (g + widx kk n p (vf p) q (vf q) : ℕ) := by
  have hw := C.hw
  have hweights := C.gB
  have hcells := C.vtB
  have hidx := widx_lt hp hq (hvf p hp) (hvf q hq)
  have hn : 0 < n := Nat.zero_lt_of_lt (hvf p hp)
  -- The numbers that the address is built from grow from step to step, up to the place.
  have hsteps : (0 : ℤ) ≤ (p : ℤ) * kk + q ∧ (p : ℤ) * kk + q ≤ ((p : ℤ) * kk + q) * n ∧
      ((p : ℤ) * kk + q) * n + vf p ≤ (((p : ℤ) * kk + q) * n + vf p) * n ∧
      (((p : ℤ) * kk + q) * n + vf p) * n + vf q < ((kk * kk * n * n : ℕ) : ℤ) := by
    refine ⟨by positivity, ?_, ?_, ?_⟩
    · exact_mod_cast Nat.le_mul_of_pos_right (p * kk + q) hn
    · exact_mod_cast Nat.le_mul_of_pos_right ((p * kk + q) * n + vf p) hn
    · exact_mod_cast hidx
  simp [wAddr, widx, Limits.Addr, abs_le, -abs_mul, hloc.size, hloc.weights, hloc.choice, hvt p hp,
    hvt q hq, toNat_natCast_add_natCast]
  omega

/-- **sumPairs** adds the weights over the list to Entry and changes nothing else; 21 steps for each
pair.  B bounds what Entry holds before. -/
theorem sumPairs_spec (C : FillCtx lim μ kk n g vt U) (hvt : ChoiceIs μ vt kk vf)
    (hvf : ∀ p < kk, vf p < n) {L : List (ℕ × ℕ)}
    (hL : ∀ pq ∈ L, pq.1 < kk ∧ pq.2 < kk ∧ pq.1 < pq.2) (hloc : FillLocals loc n g N vt) {B : ℕ}
    (hB : |loc Entry| ≤ B) (hword : ((B + L.length * U : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d (sumPairs kk L) ⟨loc, μ⟩ (21 * L.length) fun σ' =>
      σ' = ⟨Function.update loc Entry (loc Entry + memSum μ g kk n vf L), μ⟩ := by
  induction L generalizing loc B with
  | nil => exact Ends.skip (by simp [memSum])
  | cons pq L ih =>
    obtain ⟨hp, hq, hpq⟩ := hL pq (by simp)
    obtain ⟨hsafe, hval⟩ := wAddr_gives C hloc hvt hvf hp hq
    have hidx := widx_lt hp hq (hvf _ hp) (hvf _ hq)
    have hweight := abs_le.1 (C.wle pq.1 pq.2 _ _ hp hq hpq (hvf _ hp) (hvf _ hq))
    have hweights := C.gB
    have hw := C.hw
    rw [abs_le] at hB
    simp only [List.length_cons, Nat.add_mul, one_mul] at hword
    push_cast at hword
    have hrest : (0 : ℤ) ≤ (L.length : ℤ) * U := by positivity
    unfold sumPairs
    -- entry := entry + mem[the address of the weight]
    refine Ends.setThen ?_ (by simp [hsafe, hval, Limits.Addr, abs_le]; omega) (by simp)
    refine (ih (fun x hx => hL x (by simp [hx])) (hloc.update (by decide) _) (B := B + U)
      (by simp [hval, abs_le]; omega) (by push_cast; omega)).mono (by simp; omega) ?_
    rintro _ rfl
    simp [memSum, hval, add_assoc]

end sum

/-! ## The odometers -/

section odometer

variable {μ loc : ℕ → ℤ} {vf vf0 : ℕ → ℕ} {kk n vt off gw ro co r c : ℕ}

/-- The choice vf, with the vertices of the gw parts from off on replaced by the digits of c in base
n, lowest first: what an odometer on these cells shows after c steps. -/
def withDigits (vf : ℕ → ℕ) (n off gw c p : ℕ) : ℕ :=
  if off ≤ p ∧ p < off + gw then c / n ^ (p - off) % n else vf p

/-- The choice of vertices when the row odometer (gw cells from ro) shows r and the column odometer
(gw cells from co) shows c. -/
def choiceAt (vf0 : ℕ → ℕ) (n gw ro co r c : ℕ) : ℕ → ℕ :=
  withDigits (withDigits vf0 n co gw c) n ro gw r

/-- The column odometer on top of the row odometer: the two do not meet. -/
private theorem choiceAt_eq_col (vf0 : ℕ → ℕ) (n r c : ℕ) (hdis : ro + gw ≤ co ∨ co + gw ≤ ro) :
    choiceAt vf0 n gw ro co r c = withDigits (withDigits vf0 n ro gw r) n co gw c := by
  funext p
  unfold choiceAt withDigits
  split_ifs <;> first | rfl | omega

/-- The digits are vertices of their parts. -/
private theorem withDigits_lt (hn : 0 < n) (h : ∀ p < kk, vf p < n) (off gw c : ℕ) :
    ∀ p < kk, withDigits vf n off gw c p < n := by
  intro p hp
  unfold withDigits
  split_ifs
  · exact Nat.mod_lt _ hn
  · exact h p hp

/-- The chosen vertices are vertices of their parts. -/
theorem choiceAt_lt (hn : 0 < n) (h0 : ∀ p < kk, vf0 p < n) (gw ro co r c : ℕ) :
    ∀ p < kk, choiceAt vf0 n gw ro co r c p < n :=
  withDigits_lt hn (withDigits_lt hn h0 co gw c) ro gw r

private theorem pow_div_pow_mod {j : ℕ} (hn : 0 < n) (hj : j < gw) : n ^ gw / n ^ j % n = 0 := by
  obtain ⟨e, rfl⟩ : ∃ e, gw = j + (e + 1) := ⟨gw - j - 1, by omega⟩
  rw [pow_add, Nat.mul_div_cancel_left _ (by positivity), pow_succ]
  exact Nat.mul_mod_left _ _

/-- After n^gw steps an odometer shows 0 again. -/
theorem withDigits_pow (vf : ℕ → ℕ) (hn : 0 < n) (off gw : ℕ) :
    withDigits vf n off gw (n ^ gw) = withDigits vf n off gw 0 := by
  funext p
  unfold withDigits
  split_ifs with h
  · rw [pow_div_pow_mod hn (by omega)]
    simp
  · rfl

/-- The cells hold the digits of c as a list exactly if each holds its digit. -/
theorem seg_digits_iff {a : ℕ} :
    SegN μ a (ThreeSumApsp.digitsLE n gw c) ↔
      ∀ j < gw, μ (a + j) = ((c / n ^ j % n : ℕ) : ℤ) := by
  constructor
  · intro h j hj
    simpa [ThreeSumApsp.digitsLE] using h j (by simpa [ThreeSumApsp.digitsLE] using hj)
  · intro h j hj
    simpa [ThreeSumApsp.digitsLE] using h j (by simpa [ThreeSumApsp.digitsLE] using hj)

/-- What a step of an odometer needs of the limits: an address fits in a word, n fits in a word, and
the kk cells of the chosen vertices lie within the memory. -/
structure OdometerOk (lim : Limits) (n vt kk : ℕ) : Prop where
  space : (lim.space : ℤ) ≤ lim.word
  size : (n : ℤ) ≤ lim.word
  cells : vt + kk ≤ lim.space

/-- **One step of an odometer** on the gw cells from vt + off: it shows c + 1 instead of c, and
nothing else changes. -/
theorem inc_spec (hlim : OdometerOk lim n vt kk)
    (hn : 0 < n) (hoff : off + gw ≤ kk) (hsize : loc Size = n) (hchoice : loc Choice = vt)
    (hvt : ChoiceIs μ vt kk (withDigits vf n off gw c)) :
    Ends lim P d (incStmt Choice Size off gw) ⟨loc, μ⟩ (14 * gw + 5) fun σ' =>
      σ'.loc = loc ∧ ChoiceIs σ'.mem vt kk (withDigits vf n off gw (c + 1)) ∧
        SameOutside μ σ'.mem (vt + off) gw := by
  obtain ⟨hw, hnw, hspace⟩ := hlim
  have hdigits : SegN μ (vt + off) (ThreeSumApsp.digitsLE n gw c) :=
    seg_digits_iff.2 fun j hj => by
      rw [Nat.add_assoc, hvt (off + j) (by omega), withDigits, if_pos (by omega),
        Nat.add_sub_cancel_left]
  have hstep := incStmt_ends (P := P) (d := d) hw hnw hchoice hsize (by simp; omega)
    (fun _ => ThreeSumApsp.lt_of_mem_digitsLE hn) hdigits
  rw [ThreeSumApsp.length_digitsLE, ThreeSumApsp.incDigits_digitsLE hn] at hstep
  refine hstep.mono le_rfl ?_
  rintro σ' ⟨hl, hnew, hrest⟩
  refine ⟨hl, fun p hp => ?_, hrest⟩
  unfold withDigits
  split_ifs with hin
  · -- a cell of the odometer
    have hcell := seg_digits_iff.1 hnew (p - off) (by omega)
    rwa [show vt + off + (p - off) = vt + p by omega] at hcell
  · -- another cell
    rw [hrest _ (by omega), hvt p hp, withDigits, if_neg hin]

/-- One step of the column odometer. -/
theorem incCol_spec (hlim : OdometerOk lim n vt kk)
    (hn : 0 < n) (hco : co + gw ≤ kk) (hdis : ro + gw ≤ co ∨ co + gw ≤ ro) {g N : ℕ}
    (hloc : FillLocals loc n g N vt) (hvt : ChoiceIs μ vt kk (choiceAt vf0 n gw ro co r c)) :
    Ends lim P d (incStmt Choice Size co gw) ⟨loc, μ⟩ (14 * gw + 5) fun σ' =>
      σ'.loc = loc ∧ ChoiceIs σ'.mem vt kk (choiceAt vf0 n gw ro co r (c + 1)) ∧
        SameOutside μ σ'.mem (vt + co) gw := by
  rw [choiceAt_eq_col vf0 n r c hdis] at hvt
  rw [choiceAt_eq_col vf0 n r (c + 1) hdis]
  exact inc_spec hlim hn hco hloc.size hloc.choice hvt

end odometer

/-! ## An entry, a row, and the whole matrix -/

/-- One entry: the sum over the list of pairs is written to the next place, and the column odometer
moves on. -/
def fillEntry (kk gw co : ℕ) (L : List (ℕ × ℕ)) : Stmt :=
  .set Entry (k 0) ;;
  sumPairs kk L ;;
  .store (v Place) (v Entry) ;;
  .set Place (v Place +' k 1) ;;
  incStmt Choice Size co gw

/-- One row: an entry for every column. -/
def fillRow (kk gw co : ℕ) (L : List (ℕ × ℕ)) : Stmt :=
  .for Col (v Side) (fillEntry kk gw co L)

/-- The N × N matrix, row by row, from the address in local dl on. -/
def fillMat (kk gw ro co dl : ℕ) (L : List (ℕ × ℕ)) : Stmt :=
  .set Place (v dl) ;;
  .for Row (v Side) (fillRow kk gw co L ;; incStmt Choice Size ro gw)

/-- `incStmt` assigns no local variable. -/
@[simp] theorem incStmt_assigns (vb vn : ℕ) : ∀ j len : ℕ, (incStmt vb vn j len).assigns = []
  | _, 0 => rfl
  | j, len + 1 => by simp [incStmt, incStmt_assigns vb vn (j + 1) len]

/-- `sumPairs` assigns only `Entry`. -/
@[simp] theorem sumPairs_assigns (kk : ℕ) {xs : List ℕ} (h : Entry ∈ xs) :
    ∀ L : List (ℕ × ℕ), (sumPairs kk L).assigns ⊆ xs
  | [] => by simp [sumPairs]
  | _ :: L => by simp [sumPairs, h, sumPairs_assigns kk h L]

/-- `fillMat` assigns only `Row`, `Col`, `Place` and `Entry`. -/
@[simp] theorem fillMat_assigns (kk gw ro co dl : ℕ) (L : List (ℕ × ℕ)) {xs : List ℕ}
    (h : [Row, Col, Place, Entry] ⊆ xs) : (fillMat kk gw ro co dl L).assigns ⊆ xs := by
  simp only [List.cons_subset, List.nil_subset, and_true] at h
  simp [fillMat, fillRow, fillEntry, h]

/-- A bound on the number of steps of fillEntry, for a list of len pairs. -/
def entryTime (gw len : ℕ) : ℕ := 21 * len + 14 * gw + 14

/-- A bound on the number of steps of fillRow. -/
def rowTime (N gw len : ℕ) : ℕ := N * (entryTime gw len + 8) + 6

/-- A bound on the number of steps of fillMat. -/
def matTime (N gw len : ℕ) : ℕ := N * (rowTime N gw len + 14 * gw + 13) + 8

/-- What fillMat is asked to do: the graph has kk parts of n vertices, its weights stand at g and
have absolute value at most U; the chosen vertices stand at vt; the rows are counted by the gw
cells from vt + ro and the columns by the gw cells from vt + co; the other cells hold the choice
vf0; the matrix has side N = n^gw and goes to dst; an entry is the sum over the pairs of parts
in L. -/
structure FillJob where
  kk : ℕ
  n : ℕ
  g : ℕ
  vt : ℕ
  U : ℕ
  gw : ℕ
  ro : ℕ
  co : ℕ
  N : ℕ
  dst : ℕ
  vf0 : ℕ → ℕ
  L : List (ℕ × ℕ)

/-- The chosen vertices for the entry in row r and column c. -/
abbrev FillJob.choice (J : FillJob) (r c : ℕ) : ℕ → ℕ := choiceAt J.vf0 J.n J.gw J.ro J.co r c

/-- The entry in row r and column c, with the weights read from μ. -/
abbrev FillJob.entry (J : FillJob) (μ : ℕ → ℤ) (r c : ℕ) : ℤ :=
  memSum μ J.g J.kk J.n (J.choice r c) J.L

/-- What fillMat assumes of the memory μ at the start and of the limits: the two odometers lie among
the kk cells and do not meet; the sums fit in a word; the weights lie below the chosen vertices
and below the matrix, and these two do not meet. -/
structure MatCtx (lim : Limits) (μ : ℕ → ℤ) (J : FillJob) : Prop where
  fill : FillCtx lim μ J.kk J.n J.g J.vt J.U
  n_pos : 0 < J.n
  n_le : (J.n : ℤ) ≤ lim.word
  side : J.N = J.n ^ J.gw
  row : J.ro + J.gw ≤ J.kk
  col : J.co + J.gw ≤ J.kk
  apart : J.ro + J.gw ≤ J.co ∨ J.co + J.gw ≤ J.ro
  start_lt : ∀ p < J.kk, J.vf0 p < J.n
  pairs : ∀ pq ∈ J.L, pq.1 < J.kk ∧ pq.2 < J.kk ∧ pq.1 < pq.2
  sum_le : ((J.L.length * J.U : ℕ) : ℤ) ≤ lim.word
  dst_le : J.dst + J.N * J.N ≤ lim.space
  weights_dst : J.g + J.kk * J.kk * J.n * J.n ≤ J.dst
  weights_vt : J.g + J.kk * J.kk * J.n * J.n ≤ J.vt
  dst_vt : J.vt + J.kk ≤ J.dst ∨ J.dst + J.N * J.N ≤ J.vt

/-- **The invariant**, before column c of row r.  μ is the memory at the start.  The four locals
that are only read hold what they should; Place is the place of the next entry; the odometers show r
and c; the entries before this one, row by row, have been written; and outside the matrix and the
chosen vertices the memory is as at the start.  The column c runs up to N inclusive: (r, N) is the
same point as (r + 1, 0), but for the row odometer. -/
structure FillInv (J : FillJob) (μ : ℕ → ℤ) (r c : ℕ) (σ : State) : Prop where
  locals : FillLocals σ.loc J.n J.g J.N J.vt
  place : σ.loc Place = ((J.dst + r * J.N + c : ℕ) : ℤ)
  choice : ChoiceIs σ.mem J.vt J.kk (J.choice r c)
  written : ∀ r' < J.N, ∀ c' < J.N, r' * J.N + c' < r * J.N + c →
    σ.mem (J.dst + r' * J.N + c') = J.entry μ r' c'
  rest : SameOutside2 μ σ.mem J.dst (J.N * J.N) J.vt J.kk

/-- **What fillMat achieves**: the matrix is written, both odometers show 0 again, and no other cell
has changed. -/
structure Filled (J : FillJob) (μ : ℕ → ℤ) (σ : State) : Prop where
  choice : ChoiceIs σ.mem J.vt J.kk (J.choice 0 0)
  written : ∀ r < J.N, ∀ c < J.N, σ.mem (J.dst + r * J.N + c) = J.entry μ r c
  rest : SameOutside2 μ σ.mem J.dst (J.N * J.N) J.vt J.kk

section fill

variable {J : FillJob} {loc μ : ℕ → ℤ} {r c : ℕ} {σ : State}

/-- The side of the matrix fits in a word. -/
theorem MatCtx.side_le (X : MatCtx lim μ J) : (J.N : ℤ) ≤ lim.word := by
  have hw := X.fill.hw
  have hdst := X.dst_le
  have hside : J.N ≤ J.N * J.N := Nat.le_mul_self _
  omega

/-- After the last column the column odometer shows 0 again. -/
theorem MatCtx.choice_last_col (X : MatCtx lim μ J) (r : ℕ) : J.choice r J.N = J.choice r 0 := by
  rw [FillJob.choice, X.side, choiceAt_eq_col _ _ _ _ X.apart, withDigits_pow _ X.n_pos,
    ← choiceAt_eq_col _ _ _ _ X.apart]

/-- After the last row the row odometer shows 0 again. -/
theorem MatCtx.choice_last_row (X : MatCtx lim μ J) (c : ℕ) : J.choice J.N c = J.choice 0 c := by
  rw [FillJob.choice, X.side, choiceAt, withDigits_pow _ X.n_pos, ← choiceAt]

/-- All cells up to the end of the weights are as at the start. -/
theorem FillInv.kept (I : FillInv J μ r c σ) (X : MatCtx lim μ J) :
    Kept μ σ.mem (J.g + J.kk * J.kk * J.n * J.n) := fun a ha =>
  I.rest a (by have := X.weights_dst; have := X.weights_vt; omega)

/-- The invariant does not speak of the counters Row and Col and of Entry. -/
theorem FillInv.update (I : FillInv J μ r c σ) {y : ℕ} (hy : y = Row ∨ y = Col ∨ y = Entry)
    (z : ℤ) : FillInv J μ r c { σ with loc := Function.update σ.loc y z } :=
  { I with
    locals := I.locals.update (by rcases hy with rfl | rfl | rfl <;> decide) z
    place := (Function.update_of_ne
      (by simp only [Row, Col, Entry, Place] at hy ⊢; omega) _ _).trans I.place }

/-- Storing the entry in row r and column c, and then changing only cells of the column odometer,
takes the invariant to the next column. -/
theorem FillInv.next_col (I : FillInv J μ r c σ) (X : MatCtx lim μ J) (hr : r < J.N)
    (hc : c < J.N) {σ' : State} (hlocals : FillLocals σ'.loc J.n J.g J.N J.vt)
    (hplace : σ'.loc Place = ((J.dst + r * J.N + (c + 1) : ℕ) : ℤ))
    (hchoice : ChoiceIs σ'.mem J.vt J.kk (J.choice r (c + 1)))
    (hout : SameOutside (Function.update σ.mem (J.dst + r * J.N + c) (J.entry μ r c)) σ'.mem
      (J.vt + J.co) J.gw) : FillInv J μ r (c + 1) σ' := by
  have hidx : r * J.N + c < J.N * J.N := Nat.mul_add_lt_mul hr hc
  have hapart := X.dst_vt
  have hodometer := X.col
  refine
    { choice := hchoice
      locals := hlocals
      place := hplace
      written := fun r' hr' c' hc' hbefore => ?_
      rest := fun a ha => ?_ }
  · have hidx' : r' * J.N + c' < J.N * J.N := Nat.mul_add_lt_mul hr' hc'
    refine (hout _ (by omega)).trans ?_
    rcases Nat.lt_or_ge (r' * J.N + c') (r * J.N + c) with hlt | hge
    · -- an earlier entry
      exact (Function.update_of_ne (by omega) _ _).trans (I.written r' hr' c' hc' hlt)
    · -- the new entry
      obtain ⟨rfl, rfl⟩ := Nat.mul_add_inj_of_lt hc' hc (show r' * J.N + c' = r * J.N + c by omega)
      exact Function.update_self ..
  · exact (hout a (by omega)).trans ((Function.update_of_ne (by omega) _ _).trans (I.rest a ha))

/-- **fillEntry** writes the entry in row r and column c. -/
theorem fillEntry_spec (X : MatCtx lim μ J) (hr : r < J.N) (hc : c < J.N) (I : FillInv J μ r c σ) :
    Ends lim P d (fillEntry J.kk J.gw J.co J.L) σ (entryTime J.gw J.L.length) fun σ' =>
      σ'.loc Row = σ.loc Row ∧ σ'.loc Col = σ.loc Col ∧ FillInv J μ r (c + 1) σ' := by
  obtain ⟨loc', μ'⟩ := σ
  have hloc' : FillLocals loc' J.n J.g J.N J.vt := I.locals
  have hkept := I.kept X
  have hplace : loc' Place = ((J.dst + r * J.N + c : ℕ) : ℤ) := I.place
  have hvf := choiceAt_lt X.n_pos X.start_lt J.gw J.ro J.co r c
  have hidx : r * J.N + c < J.N * J.N := Nat.mul_add_lt_mul hr hc
  have hw := X.fill.hw
  have hdst := X.dst_le
  have hapart := X.dst_vt
  have hodometer := X.col
  -- The sum over the weights in μ' is the entry, which is read from μ.
  have hsum : memSum μ' J.g J.kk J.n (J.choice r c) J.L = J.entry μ r c :=
    memSum_congr hkept hvf X.pairs
  unfold fillEntry entryTime
  -- entry := 0
  refine Ends.setThen ?_
  -- sumPairs
  light_piece (sumPairs_spec (X.fill.of_kept hkept) I.choice hvf X.pairs
    (hloc'.update (by decide) _) (B := 0) (by simp) (by simpa using X.sum_le)) with _ rfl
  -- mem[place] := entry
  refine Ends.storeThen ?_ (by light_side [hplace])
  -- place := place + 1
  refine Ends.setThen ?_ (by light_side [hplace])
  -- Now Entry and the cell dst + r N + c hold the entry, and Place is dst + r N + c + 1.
  light_norm [Entry, Place, hplace, Int.toNat_natCast, zero_add, hsum]
  -- the column odometer moves on
  have hloc'' (z₁ z₂ z₃ : ℤ) := ((hloc'.update (y := Entry) (by decide) z₁).update (y := Entry)
    (by decide) z₂).update (y := Place) (by decide) z₃
  refine (incCol_spec ⟨hw, X.n_le, X.fill.vtB⟩ X.n_pos hodometer X.apart (hloc'' _ _ _)
    (r := r) (c := c) (vf0 := J.vf0) fun p hp => ?_).mono (by light_time) ?_
  · -- The store has not touched the chosen vertices.
    exact (Function.update_of_ne (by omega) _ _).trans (I.choice p hp)
  rintro ⟨_, μ''⟩ ⟨rfl, hchoice, hout⟩
  exact ⟨rfl, rfl, I.next_col X hr hc (hloc'' _ _ _) (by simp [Place, add_assoc]) hchoice hout⟩

/-- **fillRow** writes row r. -/
theorem fillRow_spec (X : MatCtx lim μ J) (hr : r < J.N) (I : FillInv J μ r 0 σ) :
    Ends lim P d (fillRow J.kk J.gw J.co J.L) σ (rowTime J.N J.gw J.L.length) fun σ' =>
      σ'.loc Row = σ.loc Row ∧ FillInv J μ r J.N σ' := by
  unfold fillRow rowTime
  -- for col < N
  refine Ends.for (fun c σ' => σ'.loc Row = σ.loc Row ∧ FillInv J μ r c σ') J.N
    (entryTime J.gw J.L.length) ?start ?round ?done ?bound (hn := X.side_le)
  case start => exact ⟨rfl, I.update (by simp) _⟩
  case round =>
    rintro c σ₁ hc hcount ⟨hkeep₁, I₁⟩
    refine (fillEntry_spec X hr hc I₁).mono le_rfl ?_
    rintro σ₂ ⟨hkeep₂, hcount₂, I₂⟩
    exact ⟨hcount₂.trans hcount, hkeep₂.trans hkeep₁, I₂.update (by simp) _⟩
  case done => exact fun _ _ h => h
  case bound => exact fun _ _ _ _ h => ⟨trivial, h.2.locals.side⟩

/-- After the last column of row r comes the first column of row r + 1: the column odometer shows 0
again, and **the row odometer moves on**. -/
theorem nextRow_spec (X : MatCtx lim μ J) (I : FillInv J μ r J.N σ) :
    Ends lim P d (incStmt Choice Size J.ro J.gw) σ (14 * J.gw + 5) fun σ' =>
      σ'.loc = σ.loc ∧ FillInv J μ (r + 1) 0 σ' := by
  have hodometer := X.row
  have hnext : (r + 1) * J.N + 0 = r * J.N + J.N := by ring
  have hchoice : ChoiceIs σ.mem J.vt J.kk (J.choice r 0) := X.choice_last_col r ▸ I.choice
  refine (inc_spec ⟨X.fill.hw, X.n_le, X.fill.vtB⟩ X.n_pos hodometer I.locals.size
    I.locals.choice hchoice).mono le_rfl ?_
  rintro σ' ⟨hl, hchoice', hout⟩
  refine ⟨hl,
    { choice := hchoice'
      locals := hl ▸ I.locals
      place := ?_
      written := fun r' hr' c' hc' hbefore => ?_
      rest := fun a ha => ?_ }⟩
  · rw [hl, I.place, Nat.add_assoc, Nat.add_assoc, hnext]
  · have hidx' : r' * J.N + c' < J.N * J.N := Nat.mul_add_lt_mul hr' hc'
    have hapart := X.dst_vt
    exact (hout _ (by omega)).trans (I.written r' hr' c' hc' (hnext ▸ hbefore))
  · exact (hout a (by omega)).trans (I.rest a ha)

/-- **fillMat** writes the matrix.  Both odometers show 0 before and afterwards. -/
theorem fillMat_spec (X : MatCtx lim μ J) (hloc : FillLocals loc J.n J.g J.N J.vt) {dl : ℕ}
    (hdl : loc dl = J.dst) (hvt : ChoiceIs μ J.vt J.kk (J.choice 0 0)) :
    Ends lim P d (fillMat J.kk J.gw J.ro J.co dl J.L) ⟨loc, μ⟩ (matTime J.N J.gw J.L.length)
      (Filled J μ) := by
  unfold fillMat matTime
  -- place := the address of the matrix
  refine Ends.setThen ?_
  -- for row < N
  refine Ends.for (fun r σ' => FillInv J μ r 0 σ') J.N
    (rowTime J.N J.gw J.L.length + (14 * J.gw + 5)) ?start ?round ?done ?bound (hn := X.side_le)
  case start =>
    exact
      { locals := (hloc.update (y := Place) (by decide) _).update (y := Row) (by decide) _
        place := by simp [Row, Place, hdl]
        choice := hvt
        written := fun r' _ c' _ hbefore => absurd hbefore (by omega)
        rest := SameOutside2.refl }
  case round =>
    rintro r σ₁ hr hcount I₁
    -- fillRow
    light_piece (fillRow_spec X hr I₁) with σ₂ ⟨hkeep, I₂⟩
    -- the row odometer moves on
    light_piece (nextRow_spec X I₂) with σ₃ ⟨hl, I₃⟩
    exact ⟨(congrFun hl Row).trans (hkeep.trans hcount), I₃.update (by simp) _⟩
  case done =>
    rintro σ' - I
    exact
      { rest := I.rest
        choice := X.choice_last_row 0 ▸ I.choice
        written :=
          fun r hr c hc => I.written r hr c hc (by have := Nat.mul_add_lt_mul hr hc; omega) }
  case bound => exact fun _ _ _ _ h => ⟨trivial, h.locals.side⟩

end fill

end Light.Sec5
