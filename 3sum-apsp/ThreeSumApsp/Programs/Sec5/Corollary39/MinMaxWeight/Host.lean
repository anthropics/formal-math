/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.Sec5.Corollary39.GraphH.Build
public import ThreeSumApsp.Sec5.Corollary39

/-!
# Corollary 39, minimum and maximum weight: the host

Proof of Corollary 39: "We enumerate the n^t ways of fixing one vertex in each of the first
t parts, and for each of them we build H as above from the remaining 3⌊k/3⌋ parts; now the triangles
of H correspond to the k-cliques through the t fixed vertices."  And: "We give H edge weights so
that a triangle and its k-clique have the same weight."  So a best triangle over the n^t graphs H
gives a best k-clique (`opt_of_best`, from `Corollary39.S_graphH_eq_cliqueWeight`).

This file has the reduction from Max-Weight (Min-Weight) k-Clique to Max-Weight (Min-Weight)
Triangle, as a procedure that calls an arbitrary solver of the triangle problem (`isHost_maxKc`,
`isHost_minKc`).  Where such a solver comes from ([VW13, Theorem 3.3], and the negated weights for
the minimum) is not the subject of this file.  The two hosts are one program with a flag mx, true
for the maximum and false for the minimum; the host for the minimum calls a solver of Min-Weight
Triangle.

The route.
* Set-up: `hostSetup`, the free pointer for the solver, and a weight that every triangle beats.
* A round takes the invariant `OptInv` from F to F + 1 (`optRound_spec`): `buildH` writes H; the
  solver writes a best triangle of H to three cells (`triangleAt_of_answer`); `readTriangle` adds up
  its weight; `keepBetter` compares it with the best weight of the earlier rounds (`BestSo.keep`,
  `BestSo.replace`); `nextChoice` goes on (`endOfRound_spec`).
* The end (`optDecode_spec`).  The paper does not speak of this step: the solver returns vertices of
  H as numbers below N, and the k vertices of the clique are their digits in base n.  The host
  writes them by counting up with odometers (`countUp_spec`, `decode_spec`), in O(k (n^t + N))
  steps, against more than n^t N² steps for the rounds.
`opt_spec` puts the three together.

The names of the local variables that both hosts for k-Clique use are in the namespace `KC`, those
of this host in `OptKc`, and `optLocals` lists all of them with their values before a round.

In the texts of programs the number of parts is called kk, because k is the constant of the
language.
-/

@[expose] public section

open ThreeSumApsp.Spec

namespace Light.Sec5

open ThreeSumApsp ThreeSumApsp.KClique Light.Sec3 KC

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The local variables -/

namespace OptKc

/-- The address of the k cells for the clique. -/
abbrev Dest : ℕ := 3
/-- The free pointer, at the start of the host.  `hostSetup` uses the same local as `Side`. -/
abbrev Free : ℕ := Side
/-- The counter of `countUp`.  `fillMat` uses the same local as `Row`. -/
abbrev Count : ℕ := Row
/-- The weight of the best triangle so far. -/
abbrev BestWeight : ℕ := 17
/-- The number of the round of the best triangle so far. -/
abbrev BestRound : ℕ := 18
/-- The first vertex of the best triangle so far. -/
abbrev BestA : ℕ := 19
/-- The second vertex of the best triangle so far. -/
abbrev BestB : ℕ := 20
/-- The third vertex of the best triangle so far. -/
abbrev BestC : ℕ := 21
/-- The free pointer for the solver. -/
abbrev SolverFree : ℕ := 22
/-- The first vertex of the triangle of this round. -/
abbrev TriA : ℕ := 23
/-- The second vertex of the triangle of this round. -/
abbrev TriB : ℕ := 24
/-- The third vertex of the triangle of this round. -/
abbrev TriC : ℕ := 25
/-- The weight of the triangle of this round. -/
abbrev TriWeight : ℕ := 26

end OptKc

open OptKc

/-! ## Counting up -/

/-- The odometer of len digits at base + j (base is local vb) is moved on as many times as local vt
says. -/
def countUp (vb vt j len : ℕ) : Stmt :=
  .for Count (v vt) (incStmt vb Size j len)

/-- `countUp` assigns only `Count`. -/
@[simp] theorem countUp_assigns (vb vt j len : ℕ) {xs : List ℕ} (h : Count ∈ xs) :
    (countUp vb vt j len).assigns ⊆ xs := by
  simp [countUp, h]

/-- **countUp** turns zeros into the digits of the number in local vt; val (14 len + 13) + 6 steps.
-/
theorem countUp_spec {vb vt base n j len val : ℕ} (hvb : vb ≠ Count) (hvt : vt ≠ Count)
    (hw : (lim.space : ℤ) ≤ lim.word) (hnw : (n : ℤ) ≤ lim.word) (hn : 0 < n)
    (hvw : ((val + 1 : ℕ) : ℤ) ≤ lim.word) (hB : base + j + len ≤ lim.space) (loc μ : ℕ → ℤ)
    (hsize : loc Size = n) (eb : loc vb = base) (et : loc vt = val)
    (hz : ∀ i < len, μ (base + j + i) = 0) :
    Ends lim P d (countUp vb vt j len) ⟨loc, μ⟩ (val * (14 * len + 13) + 6) fun σ' =>
      (∀ i < len, σ'.mem (base + j + i) = ((val / n ^ i % n : ℕ) : ℤ)) ∧
      SameOutside μ σ'.mem (base + j) len := by
  unfold countUp
  -- before round c the odometer shows c
  refine Ends.forMem (fun c μ' => SegN μ' (base + j) (ThreeSumApsp.digitsLE n len c) ∧
    SameOutside μ μ' (base + j) len) val (14 * len + 5) ?start ?round ?done ?bound
    (by push_cast at hvw; omega)
  case start => exact ⟨seg_digits_iff.2 fun i hi => (hz i hi).trans (by simp), SameOutside.refl⟩
  case round =>
    rintro c μ' hc ⟨hseg, hrest⟩
    have hinc := incStmt_ends (P := P) (d := d) (vb := vb) (vn := Size) (base := base) (n := n)
      (loc := Function.update loc Count c) hw hnw ((Function.update_of_ne hvb _ _).trans eb)
      ((Function.update_of_ne (by decide) _ _).trans hsize) (by simpa using hB)
      (fun _ => ThreeSumApsp.lt_of_mem_digitsLE hn) hseg
    simp only [ThreeSumApsp.length_digitsLE] at hinc
    refine hinc.mono le_rfl ?_
    rintro ⟨_, μ₂⟩ ⟨rfl, hnext, hout⟩
    rw [ThreeSumApsp.incDigits_digitsLE hn] at hnext
    exact ⟨rfl, hnext, hrest.trans hout⟩
  case done =>
    rintro μ' ⟨hseg, hrest⟩
    exact ⟨seg_digits_iff.1 hseg, hrest⟩
  case bound => exact fun c μ' _ _ => ⟨trivial, (Function.update_of_ne hvt _ _).trans et⟩

/-! ## Comparing weights -/

/-- Being at least as good is transitive. -/
theorem better_trans {mx : Bool} {x y z : ℤ} (h₁ : better mx x y) (h₂ : better mx y z) :
    better mx x z := by
  cases mx
  · exact le_trans h₁ h₂
  · exact le_trans h₂ h₁

/-- Of two weights one is at least as good as the other. -/
theorem better_of_not {mx : Bool} {x y : ℤ} (h : ¬ better mx x y) : better mx y x := by
  cases mx
  · exact le_of_lt (not_le.1 h)
  · exact le_of_lt (not_le.1 h)

/-- The weight of the triangle of this round is strictly better than the best weight so far. -/
def cmpE : Bool → Cond
  | true => v BestWeight <' v TriWeight
  | false => v TriWeight <' v BestWeight

/-- The test costs three steps. -/
@[simp] theorem cmpE_cost (mx : Bool) : (cmpE mx).cost = 3 := by cases mx <;> rfl

/-- The test is safe. -/
theorem cmpE_safe (mx : Bool) (σ : State) : (cmpE mx).Safe lim σ := by
  cases mx <;> exact ⟨trivial, trivial⟩

/-- The test holds if and only if the best weight so far is not at least as good as the weight of
this round. -/
theorem cmpE_holds (mx : Bool) (σ : State) :
    (cmpE mx).Holds σ ↔ ¬ better mx (σ.loc BestWeight) (σ.loc TriWeight) := by
  cases mx
  · simp [cmpE, better]
  · simp [cmpE, better]

/-- A weight that is worse than the weight of every triangle of H. -/
def sentinel (kk U : ℕ) : Bool → ℤ
  | true => -((3 * lenH kk * U + 1 : ℕ) : ℤ)
  | false => ((3 * lenH kk * U + 1 : ℕ) : ℤ)

/-- The expression whose value is `sentinel kk U mx`. -/
def sentinelE (kk : ℕ) : Bool → Expr
  | true => k 0 -' (k (3 * lenH kk) *' v Bound +' k 1)
  | false => k (3 * lenH kk) *' v Bound +' k 1

/-- The expression costs at most seven steps. -/
theorem sentinelE_cost_le (kk : ℕ) (mx : Bool) : (sentinelE kk mx).cost ≤ 7 := by
  cases mx <;> simp [sentinelE]

/-- The expression is safe and has the value sentinel kk U mx. -/
theorem sentinelE_safe_val {kk U : ℕ} {σ : State} (hbound : σ.loc Bound = U)
    (hw : ((3 * lenH kk * U + 3 * lenH kk + 1 : ℕ) : ℤ) ≤ lim.word) (mx : Bool) :
    (sentinelE kk mx).Safe lim σ ∧ (sentinelE kk mx).val σ = sentinel kk U mx := by
  push_cast at hw
  have hprod : (0 : ℤ) ≤ 3 * (lenH kk : ℤ) * U := by positivity
  have hlen : (0 : ℤ) ≤ 3 * (lenH kk : ℤ) := by positivity
  cases mx <;> simp [sentinelE, sentinel, abs_le, hbound] <;> omega

/-- No weight of a triangle of H is beaten or matched by the sentinel. -/
theorem not_better_sentinel {kk U : ℕ} {mx : Bool} {s : ℤ}
    (hs : |s| ≤ ((3 * lenH kk * U : ℕ) : ℤ)) : ¬ better mx (sentinel kk U mx) s := by
  have := abs_le.1 hs
  cases mx
  · simp only [better, sentinel]
    push_cast at this ⊢
    omega
  · simp only [better, sentinel]
    push_cast at this ⊢
    omega

/-! ## The program -/

/-- Read the triangle that the solver has found from the three cells behind the matrices of H, and
add up its weight from the three matrices. -/
def readTriangle : Stmt :=
  .set TriA (M (v Behind)) ;;
  .set TriB (M (v Behind +' k 1)) ;;
  .set TriC (M (v Behind +' k 2)) ;;
  .set TriWeight (M (v MatAB +' v TriA *' v Side +' v TriB)
    +' M (v MatBC +' v TriB *' v Side +' v TriC) +' M (v MatAC +' v TriA *' v Side +' v TriC))

/-- Keep the triangle of this round if it is strictly better than the best so far. -/
def keepBetter (mx : Bool) : Stmt :=
  .ite (cmpE mx)
    (.set BestWeight (v TriWeight) ;; .set BestRound (v Round) ;; .set BestA (v TriA) ;;
      .set BestB (v TriB) ;; .set BestC (v TriC)) .skip

/-- The end of a round. -/
def endOfRound (kk : ℕ) (mx : Bool) : Stmt :=
  readTriangle ;; keepBetter mx ;; nextChoice kk

/-- One choice of the fixed vertices: build H, let the solver (procedure pe) find a best triangle,
then endOfRound. -/
def optRound (kk pe : ℕ) (mx : Bool) : Stmt :=
  buildH kk ;;
  .call pe [v Side, k (lenH kk) *' v Bound, v MatAB, v MatBC, v MatAC, v Behind, v SolverFree]
    Answer ;;
  endOfRound kk mx

/-- The number of the best round and the three vertices of the best triangle are turned into their
digits in base n, in the kk cells for the clique. -/
def decodeStmt (kk : ℕ) : Stmt :=
  zeroStmt Dest 0 kk ;;
  countUp Dest BestRound 0 (numFixed kk) ;;
  countUp Dest BestA (numFixed kk) (width kk) ;;
  countUp Dest BestB (numFixed kk + width kk) (width kk) ;;
  countUp Dest BestC (numFixed kk + 2 * width kk) (width kk)

/-- optKc(n, U, g, res, fr). -/
def optBody (kk pe : ℕ) (mx : Bool) : Stmt :=
  .set Choice (v Free) ;;
  hostSetup kk ;;
  .set SolverFree (v Behind +' k 3) ;;
  .set BestWeight (sentinelE kk mx) ;;
  .while (v Round <' v Rounds) (optRound kk pe mx) ;;
  decodeStmt kk

/-- The time of one round: the three matrices of H, the solver, and the end of the round. -/
def optRoundT (kk : ℕ) (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  fillT kk (n ^ width kk) 0 + fillT kk (n ^ width kk) 1 + fillT kk (n ^ width kk) 2 +
    T (n ^ width kk) (lenH kk * U) + 14 * numFixed kk + 74

/-- The time of the host: n^t rounds, each with the test of the loop; the decoding, at most n^t + 3
N steps of an odometer; the set-up. -/
def optTime (kk : ℕ) (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  n ^ numFixed kk * (optRoundT kk T n U + 4) + n ^ numFixed kk * (14 * numFixed kk + 13)
    + 3 * (n ^ width kk * (14 * width kk + 13)) +
    2 * width kk + 2 * numFixed kk + 10 * kk + 80

/-- What the host needs.  Words: what the solver needs, three times the largest weight of H and one
more (the sentinel), and the sizes.  Cells: the k chosen vertices, the three matrices, the three
cells for the triangle, and what the solver needs.  Depth of calls: one more than the solver. -/
def optNeed (kk : ℕ) (r : ℕ → ℕ → Need) (n U : ℕ) : Need where
  word := (r (n ^ width kk) (lenH kk * U)).word + 3 * lenH kk * U + 3 * lenH kk + n ^ numFixed kk
    + n ^ width kk + n + kk + 4
  cells := kk + 3 * (n ^ width kk * n ^ width kk) + 3 + (r (n ^ width kk) (lenH kk * U)).cells
  depth := (r (n ^ width kk) (lenH kk * U)).depth + 1

/-! ## The best triangle so far -/

/-- What the host holds in `BestWeight` to `BestC`: the weight of a triangle, the number of its
round, and its three vertices. -/
structure Best : Type where
  weight : ℤ
  round : ℤ
  a : ℤ
  b : ℤ
  c : ℤ

/-- The triangle (a, b, c) of the graph H of the choice number Fb, as the host holds it. -/
def bestOf {k : ℕ} (x : KcInst k) (Fb : Fin (x.n ^ numFixed k)) (a b c : Fin (x.n ^ width k)) :
    Best :=
  ⟨(x.H Fb).S a b c, (Fb : ℕ), (a : ℕ), (b : ℕ), (c : ℕ)⟩

/-- The weight w is at least as good as that of every triangle of the choices number 0, …, F - 1. -/
def Beats {k : ℕ} (mx : Bool) (x : KcInst k) (F : ℕ) (w : ℤ) : Prop :=
  ∀ F' : Fin (x.n ^ numFixed k), (F' : ℕ) < F → ∀ a' b' c', better mx w ((x.H F').S a' b' c')

/-- What the host holds before round F: before the first round the weight is the sentinel; later it
holds a triangle that is at least as good as all triangles of the earlier rounds. -/
def BestSo {k : ℕ} (mx : Bool) (x : KcInst k) (F : ℕ) (best : Best) : Prop :=
  (F = 0 ∧ best.weight = sentinel k x.U mx) ∨
    ∃ Fb a b c, best = bestOf x Fb a b c ∧ Beats mx x F best.weight

/-- A weight that is at least as good as all triangles of the choices below F and of the choice
number F is at least as good as all triangles of the choices below F + 1. -/
theorem Beats.succ {k : ℕ} {mx : Bool} {x : KcInst k} {F : ℕ} (hF : F < x.n ^ numFixed k) {w : ℤ}
    (hearlier : Beats mx x F w) (hround : ∀ a' b' c', better mx w ((x.H ⟨F, hF⟩).S a' b' c')) :
    Beats mx x (F + 1) w := by
  intro F' hF' a' b' c'
  by_cases h : (F' : ℕ) = F
  · obtain rfl : F' = ⟨F, hF⟩ := Fin.ext h
    exact hround a' b' c'
  · exact hearlier F' (by omega) a' b' c'

section step

variable {k : ℕ} {mx : Bool} {x : KcInst k} {F : ℕ} {hF : F < x.n ^ numFixed k} {best : Best}
  {a b c : Fin (x.n ^ width k)}

/-- **The old triangle stays** if it is at least as good as a best triangle (a, b, c) of round F. -/
theorem BestSo.keep (hbest : BestSo mx x F best)
    (hle : |(x.H ⟨F, hF⟩).S a b c| ≤ ((3 * lenH k * x.U : ℕ) : ℤ))
    (hopt : ∀ a' b' c', better mx ((x.H ⟨F, hF⟩).S a b c) ((x.H ⟨F, hF⟩).S a' b' c'))
    (hb : better mx best.weight ((x.H ⟨F, hF⟩).S a b c)) : BestSo mx x (F + 1) best := by
  rcases hbest with ⟨-, hsentinel⟩ | ⟨Fb, a₀, b₀, c₀, hold, hbeats⟩
  · exact absurd (hsentinel ▸ hb) (not_better_sentinel hle)
  · exact Or.inr ⟨Fb, a₀, b₀, c₀, hold,
      hbeats.succ hF fun a' b' c' => better_trans hb (hopt a' b' c')⟩

/-- **A best triangle (a, b, c) of round F takes the place of the old one** if the old one is not at
least as good: it beats the old one, and so all that the old one beat. -/
theorem BestSo.replace (hbest : BestSo mx x F best)
    (hopt : ∀ a' b' c', better mx ((x.H ⟨F, hF⟩).S a b c) ((x.H ⟨F, hF⟩).S a' b' c'))
    (hb : ¬ better mx best.weight ((x.H ⟨F, hF⟩).S a b c)) :
    BestSo mx x (F + 1) (bestOf x ⟨F, hF⟩ a b c) := by
  refine Or.inr ⟨⟨F, hF⟩, a, b, c, rfl, Beats.succ hF (fun F' hF' a' b' c' => ?_) hopt⟩
  rcases hbest with ⟨hzero, -⟩ | ⟨_, _, _, _, -, hbeats⟩
  · omega
  · exact better_trans (better_of_not hb) (hbeats F' hF' a' b' c')

end step

/-! ## The answer of the solver -/

/-- **The answer of the solver in the memory.**  The triangle (a, b, c) stands in the three cells
behind the matrices of H.  The matrices hold the weights of the graph G, and the three weights of
the triangle are at most L in absolute value. -/
structure TriangleAt (lim : Limits) (μ : ℕ → ℤ) (k n fr L : ℕ)
    (G : TriangleInstance ℤ (n ^ width k)) (a b c : Fin (n ^ width k)) : Prop where
  space : matH k n fr 3 + 3 ≤ lim.space
  cell_a : μ (matH k n fr 3) = (a : ℕ)
  cell_b : μ (matH k n fr 3 + 1) = (b : ℕ)
  cell_c : μ (matH k n fr 3 + 2) = (c : ℕ)
  weight_ab : μ (matH k n fr 0 + a * n ^ width k + b) = G.wAB a b
  weight_bc : μ (matH k n fr 1 + b * n ^ width k + c) = G.wBC b c
  weight_ac : μ (matH k n fr 2 + a * n ^ width k + c) = G.wAC a c
  le_ab : |G.wAB a b| ≤ (L : ℤ)
  le_bc : |G.wBC b c| ≤ (L : ℤ)
  le_ac : |G.wAC a c| ≤ (L : ℤ)
  fits : 3 * (L : ℤ) + 2 ≤ lim.word

/-- The weight of the triangle is at most 3 L in absolute value. -/
theorem TriangleAt.abs_S_le {μ : ℕ → ℤ} {k n fr L : ℕ} {G : TriangleInstance ℤ (n ^ width k)}
    {a b c : Fin (n ^ width k)} (A : TriangleAt lim μ k n fr L G a b c) :
    |G.S a b c| ≤ ((3 * L : ℕ) : ℤ) := by
  have hle_ab := abs_le.1 A.le_ab
  have hle_bc := abs_le.1 A.le_bc
  have hle_ac := abs_le.1 A.le_ac
  unfold TriangleInstance.S
  push_cast
  exact abs_le.2 ⟨by omega, by omega⟩

/-- Three cells behind an instance of a triangle problem are a place for the answer. -/
theorem findPre_of_triPre {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr) :
    (⟨x, fr⟩ : FindInst).Pre μ (fr + 3) :=
  { toPre := h.mono (by omega)
    belowRes := le_rfl
    apartAB := Or.inl h.belowAB
    apartBC := Or.inl h.belowBC
    apartAC := Or.inl h.belowAC }

/-- **What the answer of the solver means.**  The solver was asked in the memory μ and has left the
memory μ', with the triangle (a, b, c) in the three cells behind the matrices of H.  Then μ' holds
the answer, for the graph whose matrices stand in μ. -/
theorem triangleAt_of_answer {k n U fr : ℕ} {μ μ' : ℕ → ℤ}
    (hpre : (triInstOf k n U fr μ).Pre μ (matH k n fr 3))
    (hkept : KeptBut μ μ' (matH k n fr 3 + 3) (matH k n fr 3) 3) (a b c : Fin (n ^ width k))
    (ra : μ' (matH k n fr 3) = (a : ℕ)) (rb : μ' (matH k n fr 3 + 1) = (b : ℕ))
    (rc : μ' (matH k n fr 3 + 2) = (c : ℕ)) (hspace : matH k n fr 3 + 3 ≤ lim.space)
    (hfits : 3 * ((lenH k * U : ℕ) : ℤ) + 2 ≤ lim.word) :
    TriangleAt lim μ' k n fr (lenH k * U) (graphAt k n U fr μ) a b c := by
  have iab := Nat.mul_add_lt_mul a.2 b.2
  have ibc := Nat.mul_add_lt_mul b.2 c.2
  have iac := Nat.mul_add_lt_mul a.2 c.2
  obtain ⟨hAt0, hAt1, hAt2, hAt3⟩ := matH_places k n fr
  have hsame : ∀ z, z < matH k n fr 3 → μ' z = μ z := fun z hz => hkept z ⟨by omega, Or.inl hz⟩
  have hL : (0 : ℤ) ≤ ((lenH k * U : ℕ) : ℤ) := by positivity
  exact
    { space := hspace
      cell_a := ra
      cell_b := rb
      cell_c := rc
      weight_ab := by
        rw [hsame _ (by omega)]
        exact ((getD_readSeg iab).trans (congrArg μ (by omega))).symm
      weight_bc := by
        rw [hsame _ (by omega)]
        exact ((getD_readSeg ibc).trans (congrArg μ (by omega))).symm
      weight_ac := by
        rw [hsame _ (by omega)]
        exact ((getD_readSeg iac).trans (congrArg μ (by omega))).symm
      le_ab := hpre.leAB.abs_getD_le hL _
      le_bc := hpre.leBC.abs_getD_le hL _
      le_ac := hpre.leAC.abs_getD_le hL _
      fits := hfits }

/-! ## The locals of the host -/

/-- The locals of the host before round F, with the best triangle so far. -/
@[simp] abbrev optLocals {k : ℕ} (x : KcFindInst k) (fr F : ℕ) (best : Best) : List ℤ :=
  setLocals [] (hostPairs k x.n x.U x.g fr F ++ [(Dest, (x.res : ℤ)), (BestWeight, best.weight),
    (BestRound, best.round), (BestA, best.a), (BestB, best.b), (BestC, best.c),
    (SolverFree, (matH k x.n fr 3 + 3 : ℕ))])

/-- The locals of the host whose values do not matter between two rounds. -/
abbrev optScratch : List ℕ := [Row, Col, Place, Entry, Answer, TriA, TriB, TriC, TriWeight]

/-- Before round F of the host: the locals, with the best triangle of the earlier rounds; the cells
below fr are as at the start; and the fixed vertices are those of the choice number F. -/
structure OptInv {k : ℕ} (mx : Bool) (x : KcFindInst k) (μ : ℕ → ℤ) (fr F : ℕ) (σ : State) :
    Prop where
  locals : ∃ best, LocalsBut optScratch (optLocals x fr F best) σ.loc ∧
    BestSo mx x.toKcInst F best
  kept : Kept μ σ.mem fr
  choice : ChoiceIs σ.mem fr k (vtx k x.n F 0 0 0)

/-! ## The end of a round -/

/-- The place of an entry of a matrix, as the program computes it. -/
private theorem toNat_entry (base r N c : ℕ) :
    ((base : ℤ) + r * N + c).toNat = base + r * N + c := by
  rw [← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, Int.toNat_natCast]

/-- **readTriangle** puts a, b, c and the weight of the triangle into `TriA` to `TriWeight`. -/
theorem readTriangle_spec {k n U g fr L : ℕ} {G : TriangleInstance ℤ (n ^ width k)}
    {a b c : Fin (n ^ width k)} {loc μ : ℕ → ℤ} (A : TriangleAt lim μ k n fr L G a b c)
    (hw : (lim.space : ℤ) ≤ lim.word) (hloc : HostLocals loc k n U g fr) :
    Ends lim P d readTriangle ⟨loc, μ⟩ 40 fun σ' => σ' = ⟨updateLocals loc
      [(TriA, (a : ℕ)), (TriB, (b : ℕ)), (TriC, (c : ℕ)), (TriWeight, G.S a b c)], μ⟩ := by
  -- the places are within the memory, the weights within L
  have hentry_ab := Nat.mul_add_lt_mul a.2 b.2
  have hentry_bc := Nat.mul_add_lt_mul b.2 c.2
  have hentry_ac := Nat.mul_add_lt_mul a.2 c.2
  obtain ⟨hAt0, hAt1, hAt2, hAt3⟩ := matH_places k n fr
  have hspace := A.space
  have hfits := A.fits
  have hle_ab := abs_le.1 A.le_ab
  have hle_bc := abs_le.1 A.le_bc
  have hle_ac := abs_le.1 A.le_ac
  have hcell_b : ((matH k n fr 3 : ℤ) + 1).toNat = matH k n fr 3 + 1 := by omega
  have hcell_c : ((matH k n fr 3 : ℤ) + 2).toNat = matH k n fr 3 + 2 := by omega
  unfold readTriangle
  -- TriA := mem[Behind]; TriB := mem[Behind + 1]; TriC := mem[Behind + 2]
  refine Ends.setValThen (a : ℕ) ?_ (by light_side [hloc.behind, A.cell_a])
  refine Ends.setValThen (b : ℕ) ?_
    (by light_side [hloc.behind, hcell_b, A.cell_b])
  refine Ends.setValThen (c : ℕ) ?_
    (by light_side [hloc.behind, hcell_c, A.cell_c])
  -- TriWeight := the sum of the three entries
  exact Ends.setVal _ rfl
    (by simp [-Nat.cast_pow, -Int.natCast_pow, hloc.side, hloc.matAB, hloc.matBC, hloc.matAC,
          toNat_entry, A.weight_ab, A.weight_bc, A.weight_ac, TriangleInstance.S, Limits.Addr,
          abs_le]
        omega)

/-- **keepBetter** copies the weight, the number of the round and the triangle of this round into
`BestWeight` to `BestC` if the weight is strictly better than the best so far, and changes nothing
if not. -/
theorem keepBetter_spec (mx : Bool) (loc μ : ℕ → ℤ) :
    Ends lim P d (keepBetter mx) ⟨loc, μ⟩ 14 fun σ' =>
      (¬ better mx (loc BestWeight) (loc TriWeight) → σ' = ⟨updateLocals loc
        [(BestWeight, loc TriWeight), (BestRound, loc Round), (BestA, loc TriA),
          (BestB, loc TriB), (BestC, loc TriC)], μ⟩) ∧
      (better mx (loc BestWeight) (loc TriWeight) → σ' = ⟨loc, μ⟩) := by
  unfold keepBetter
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (cmpE_safe mx _) (by rw [cmpE_cost]; omega)
  · rw [cmpE_holds] at hc
    exact Ends.block ⟨by simp, fun _ => by simp, fun hb => absurd hb hc⟩
      (by rw [cmpE_cost]; simp)
  · rw [cmpE_holds, not_not] at hc
    exact Ends.skip ⟨fun hb => absurd hc hb, fun _ => rfl⟩

/-- **nextChoice** leads to the invariant for round F + 1, if the best triangle of the rounds up to
F is in its place. -/
theorem optNext_spec {k : ℕ} {mx : Bool} {x : KcFindInst k} {μ₀ : ℕ → ℤ} {fr F : ℕ} {best : Best}
    {loc μ : ℕ → ℤ} (hloc : LocalsBut optScratch (optLocals x fr F best) loc)
    (hbest : BestSo mx x.toKcInst (F + 1) best) (hkept : Kept μ₀ μ fr)
    (hvt : ChoiceIs μ fr k (vtx k x.n F 0 0 0)) (hn : 0 < x.n) (hlim : OdometerOk lim x.n fr k)
    (hF : ((F + 1 : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d (nextChoice k) ⟨loc, μ⟩ (14 * numFixed k + 9) (OptInv mx x μ₀ fr (F + 1)) := by
  refine (nextChoice_spec (n := x.n) (fr := fr) (F := F) (hloc Size (by decide))
    (hloc Choice (by decide)) (hloc Round (by decide)) hn hlim hF hvt).mono le_rfl ?_
  rintro ⟨_, μ'⟩ ⟨rfl, hvt', hout⟩
  exact ⟨⟨best, hloc.update Round _, hbest⟩, fun z hz => (hout z (Or.inl hz)).trans (hkept z hz),
    hvt'⟩

/-- **endOfRound** reads the answer of the solver, a best triangle (a, b, c) of round F, keeps it if
it is strictly better than the best so far, and goes to the choice number F + 1. -/
theorem endOfRound_spec {k : ℕ} (mx : Bool) {x : KcFindInst k} {μ₀ : ℕ → ℤ} {fr F : ℕ}
    {hF : F < x.n ^ numFixed k} {best : Best} {a b c : Fin (x.n ^ width k)} {loc μ : ℕ → ℤ}
    (hloc : LocalsBut optScratch (optLocals x fr F best) loc)
    (hbest : BestSo mx x.toKcInst F best)
    (A : TriangleAt lim μ k x.n fr (lenH k * x.U) (x.H ⟨F, hF⟩) a b c)
    (hopt : ∀ a' b' c', better mx ((x.H ⟨F, hF⟩).S a b c) ((x.H ⟨F, hF⟩).S a' b' c'))
    (hkept : Kept μ₀ μ fr) (hvt : ChoiceIs μ fr k (vtx k x.n F 0 0 0)) (hn : 0 < x.n)
    (hlim : OdometerOk lim x.n fr k) (hFw : ((F + 1 : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d (endOfRound k mx) ⟨loc, μ⟩ (14 * numFixed k + 63)
      (OptInv mx x μ₀ fr (F + 1)) := by
  have hle : |(x.H ⟨F, hF⟩).S a b c| ≤ ((3 * lenH k * x.U : ℕ) : ℤ) := by
    rw [Nat.mul_assoc]
    exact A.abs_S_le
  refine Ends.asFrame hloc ?_
  unfold endOfRound
  -- readTriangle
  light_piece (readTriangle_spec (U := x.U) (g := x.g) A hlim.space
    (by constructor <;> rfl)) with _ rfl
  rw [updateLocals_frame]
  -- keepBetter
  light_piece (keepBetter_spec mx _ μ) with σ₂ ⟨hnew, hold⟩
  -- nextChoice
  by_cases hb : better mx best.weight ((x.H ⟨F, hF⟩).S a b c)
  · obtain rfl := hold hb
    exact (optNext_spec (LocalsBut.of_eq (by simp)) (hbest.keep hle hopt hb) hkept hvt hn hlim
      hFw).mono (by light_time) fun _ h => h
  · obtain rfl := hnew hb
    rw [updateLocals_frame]
    exact (optNext_spec (LocalsBut.of_eq (by simp [bestOf])) (hbest.replace hopt hb) hkept hvt hn
      hlim hFw).mono (by light_time) fun _ h => h

/-! ## A round -/

section host

variable {k : ℕ} {P₀ R : Program} {pe : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {mx : Bool}

/-- **One round of the host** takes the invariant from F to F + 1. -/
theorem optRound_spec (hsol : Solves (optTriTask mx) P₀ pe T r) (hk : 3 ≤ k) {x : KcFindInst k}
    {μ₀ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ₀ fr) (hok : (optNeed k r x.n x.U).Ok lim fr d) {F : ℕ}
    (hF : F < x.n ^ numFixed k) {σ : State} (I : OptInv mx x μ₀ fr F σ) :
    Ends lim (P₀ ++ R) d (optRound k pe mx) σ (optRoundT k T x.n x.U)
      (OptInv mx x μ₀ fr (F + 1)) := by
  obtain ⟨loc, μ⟩ := σ
  obtain ⟨⟨best, hloc, hbest⟩, hkept, hchoice⟩ := I
  obtain ⟨hokw, hokc, hw, hokd⟩ := hok
  simp only [optNeed] at hokw hokc hokd
  have hfits : ∀ a : ℕ, a ≤ (r (x.n ^ width k) (lenH k * x.U)).word + 3 * lenH k * x.U + 3 * lenH k
      + x.n ^ numFixed k + x.n ^ width k + x.n + k + 4 → (a : ℤ) ≤ lim.word :=
    fun a ha => le_trans (by exact_mod_cast ha) hokw
  have hthree : 3 * lenH k * x.U = 3 * (lenH k * x.U) := by ring
  obtain ⟨-, -, -, hAt3⟩ := matH_places k x.n fr
  refine Ends.asFrame hloc ?_
  unfold optRound optRoundT
  -- buildH k
  refine Ends.pieceToThen [Row, Col, Place, Entry] (buildH_spec hk x.toKcInst hpre.toPre
    ⟨hw, by omega, hfits _ (by omega)⟩ hF (by constructor <;> rfl) hkept hchoice) ?_
  rintro loc₃ μ₃ B
  -- Answer := the call of the solver, which writes a best triangle (a, b, c) of H behind H
  have hneed : (r (x.n ^ width k) (lenH k * x.U)).Ok lim (matH k x.n fr 3 + 3) (d + 1) :=
    ⟨hfits _ (by omega), by omega, hw, by omega⟩
  have hlen := hfits (lenH k) (by omega)
  have hbound : (lenH k : ℤ) * x.U ≤ lim.word := by exact_mod_cast hfits (lenH k * x.U) (by omega)
  refine Ends.callToThen (T' := T (x.n ^ width k) (lenH k * x.U))
    (hsol.meets R ⟨triInstOf k x.n x.U fr μ₃, matH k x.n fr 3⟩ _ (findPre_of_triPre B.pre) hneed) ?_
    (by simp [optTriTask, triInstOf, hlen, hbound])
  rintro res μ₄ ⟨⟨a, b, c, ra, rb, rc, hopt⟩, hkept₄⟩
  have A := triangleAt_of_answer (lim := lim) B.pre hkept₄ a b c ra rb rc (by omega)
    (by exact_mod_cast hfits (3 * (lenH k * x.U) + 2) (by omega))
  have hsame₄ : ∀ z < matH k x.n fr 3, μ₄ z = μ₃ z := fun z hz => hkept₄ z ⟨by omega, Or.inl hz⟩
  change ∀ a' b' c', better mx ((graphAt k x.n x.U fr μ₃).S a b c)
    ((graphAt k x.n x.U fr μ₃).S a' b' c') at hopt
  rw [B.graph] at A hopt
  -- endOfRound k mx
  light_piece (endOfRound_spec mx (LocalsBut.of_eq (by simp)) hbest A hopt
    (fun z hz => (hsame₄ z (by omega)).trans (B.kept z hz))
    (fun p hp => (hsame₄ _ (by omega)).trans (B.choice p hp)) hpre.n_pos
    ⟨hw, hfits _ (by omega), by omega⟩ (hfits _ (by omega)))

end host

/-! ## Decoding -/

/-- The first j of the kk cells at res hold the vertices vf, the others hold 0. -/
def DecodedTo (μ : ℕ → ℤ) (res kk j : ℕ) (vf : ℕ → ℕ) : Prop :=
  (∀ p < j, μ (res + p) = (vf p : ℤ)) ∧ ∀ p, j ≤ p → p < kk → μ (res + p) = 0

/-- What the decoding needs of the limits. -/
structure DecodeOk (lim : Limits) (kk n res : ℕ) : Prop where
  n_pos : 0 < n
  space : (lim.space : ℤ) ≤ lim.word
  word : ((n ^ numFixed kk + n ^ width kk + n : ℕ) : ℤ) ≤ lim.word
  cells : res + kk ≤ lim.space

/-- **One odometer of the decoding.**  If the next len vertices are the digits of the number val in
local vt, countUp writes them. -/
theorem countUp_decoded {kk n res vt j len val : ℕ} {vf : ℕ → ℕ} {loc μ : ℕ → ℤ}
    (hlim : DecodeOk lim kk n res) (hval : val < n ^ numFixed kk + n ^ width kk)
    (hlen : j + len ≤ kk) (hvf : ∀ i < len, vf (j + i) = val / n ^ i % n)
    (D : DecodedTo μ res kk j vf) (hsize : loc Size = n) (hdest : loc Dest = res)
    (et : loc vt = val) (hvt : vt ≠ Count := by decide) :
    Ends lim P d (countUp Dest vt j len) ⟨loc, μ⟩ (val * (14 * len + 13) + 6) fun σ' =>
      DecodedTo σ'.mem res kk (j + len) vf ∧ SameOutside μ σ'.mem res kk := by
  have hcells := hlim.cells
  have hfits : ∀ v : ℕ, v ≤ n ^ numFixed kk + n ^ width kk + n → (v : ℤ) ≤ lim.word :=
    fun v hv => le_trans (by exact_mod_cast hv) hlim.word
  refine (countUp_spec (vb := Dest) (vt := vt) (j := j) (len := len) (by decide) hvt hlim.space
    (hfits _ (by omega)) hlim.n_pos (hfits _ (by have := hlim.n_pos; omega)) (by omega) loc μ hsize
    hdest et fun i hi => (congrArg μ (by omega)).trans (D.2 (j + i) (by omega) (by omega))).mono
    le_rfl ?_
  rintro σ' ⟨hdigits, hout⟩
  refine ⟨⟨fun p hp => ?_, fun p hj hp => ?_⟩, hout.mono (by omega) (by omega)⟩
  · by_cases h : p < j
    · exact (hout _ (by omega)).trans (D.1 p h)
    · have := hdigits (p - j) (by omega)
      rw [← hvf (p - j) (by omega), show res + j + (p - j) = res + p by omega,
        show j + (p - j) = p by omega] at this
      exact this
  · exact (hout _ (by omega)).trans (D.2 p (by omega) hp)

/-- The vertices of the clique in the fixed parts and in the three groups are digits of the four
numbers. -/
theorem vtx_digits (kk n Fb a b c : ℕ) :
    (∀ i < numFixed kk, vtx kk n Fb a b c (0 + i) = Fb / n ^ i % n) ∧
    (∀ i < width kk, vtx kk n Fb a b c (numFixed kk + i) = a / n ^ i % n) ∧
    (∀ i < width kk, vtx kk n Fb a b c (numFixed kk + width kk + i) = b / n ^ i % n) ∧
    ∀ i < width kk, vtx kk n Fb a b c (numFixed kk + 2 * width kk + i) = c / n ^ i % n := by
  unfold vtx
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [if_pos (by omega), Nat.zero_add]
  · rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
  · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega),
      show numFixed kk + width kk + i - numFixed kk - width kk = i by omega]
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show numFixed kk + 2 * width kk + i - numFixed kk - 2 * width kk = i by omega]

/-- **decodeStmt** writes the clique that is given by the number Fb of the best round and the best
triangle (a, b, c). -/
theorem decode_spec {k : ℕ} {x : KcFindInst k} {fr F Fb a b c : ℕ} {w : ℤ} {loc μ : ℕ → ℤ}
    (hloc : LocalsBut optScratch (optLocals x fr F ⟨w, Fb, a, b, c⟩) loc)
    (hFb : Fb < x.n ^ numFixed k) (ha : a < x.n ^ width k) (hb : b < x.n ^ width k)
    (hc : c < x.n ^ width k) (hlim : DecodeOk lim k x.n x.res) :
    Ends lim P d (decodeStmt k) ⟨loc, μ⟩ (x.n ^ numFixed k * (14 * numFixed k + 13)
      + 3 * (x.n ^ width k * (14 * width k + 13)) + 5 * k + 24) fun σ' =>
      (∀ p < k, σ'.mem (x.res + p) = (vtx k x.n Fb a b c p : ℤ)) ∧
      SameOutside μ σ'.mem x.res k := by
  have h3w := three_width_add k
  have hcells := hlim.cells
  obtain ⟨dF, da, db, dc⟩ := vtx_digits k x.n Fb a b c
  -- the four numbers are below n^t and N
  have tF := Nat.mul_le_mul_right (14 * numFixed k + 13) hFb.le
  have ta := Nat.mul_le_mul_right (14 * width k + 13) ha.le
  have tb := Nat.mul_le_mul_right (14 * width k + 13) hb.le
  have tc := Nat.mul_le_mul_right (14 * width k + 13) hc.le
  refine Ends.asFrame hloc ?_
  unfold decodeStmt
  -- zeros in the k cells
  refine Ends.pieceToThen [] (zeroStmt_spec hlim.space k 0 μ _ rfl (by omega)) ?_
  rintro _ μ₀ ⟨-, hzero, hf₀⟩
  have D₀ : DecodedTo μ₀ x.res k 0 (vtx k x.n Fb a b c) :=
    ⟨fun p hp => absurd hp (by omega), fun p _ hp => by simpa using hzero p hp⟩
  -- the digits of Fb, a, b, c
  refine Ends.pieceToThen [Count] (countUp_decoded (vt := BestRound) hlim (by omega) (by omega) dF
    D₀ rfl rfl rfl) ?_
  rintro _ μ₁ ⟨D₁, hf₁⟩
  rw [Nat.zero_add] at D₁
  refine Ends.pieceToThen [Count] (countUp_decoded (vt := BestA) hlim (by omega) (by omega) da D₁
    rfl rfl rfl) ?_
  rintro _ μ₂ ⟨D₂, hf₂⟩
  refine Ends.pieceToThen [Count] (countUp_decoded (vt := BestB) hlim (by omega) (by omega) db D₂
    rfl rfl rfl) ?_
  rintro _ μ₃ ⟨D₃, hf₃⟩
  rw [show numFixed k + width k + width k = numFixed k + 2 * width k by omega] at D₃
  light_piece (countUp_decoded (vt := BestC) hlim (by omega) (by omega) dc D₃ rfl rfl rfl)
    with ⟨_, μ₄⟩ ⟨D₄, hf₄⟩
  exact ⟨fun p hp => D₄.1 p (by omega),
    ((((SameOutside.mono hf₀ (by omega) (by omega)).trans hf₁).trans hf₂).trans hf₃).trans hf₄⟩

/-- The clique that belongs to the best triangle is a best clique. -/
theorem opt_of_best {k : ℕ} {mx : Bool} (x : KcInst k) (hn : 0 < x.n) (Fb : Fin (x.n ^ numFixed k))
    (a b c : Fin (x.n ^ width k))
    (hall : ∀ F' a' b' c', better mx ((x.H Fb).S a b c) ((x.H F').S a' b' c'))
    (v' : Fin k → Fin x.n) :
    better mx (x.G.cliqueWeight (cliqueOf hn k Fb a b c)) (x.G.cliqueWeight v') := by
  have h1 := Corollary39.S_graphH_eq_cliqueWeight x.G (cliqueOf hn k Fb a b c)
  rw [fixedOf_cliqueOf, groupOf_cliqueOf_zero, groupOf_cliqueOf_one, groupOf_cliqueOf_two,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1
  have h2 := Corollary39.S_graphH_eq_cliqueWeight x.G v'
  rw [← h1, ← h2]
  have := hall (finFunctionFinEquiv (fixedOf v')) (finFunctionFinEquiv (groupOf v' 0))
    (finFunctionFinEquiv (groupOf v' 1)) (finFunctionFinEquiv (groupOf v' 2))
  rwa [KcInst.H, KcInst.H, Equiv.symm_apply_apply] at this

/-! ## The host -/

section whole

variable {k : ℕ} {P₀ R : Program} {pe : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {mx : Bool}

/-- **After the last round** decodeStmt writes a best clique. -/
theorem optDecode_spec {lim : Limits} {d : ℕ} {P : Program} {x : KcFindInst k} {μ : ℕ → ℤ} {fr : ℕ}
    (hpre : x.Pre μ fr) (hok : (optNeed k r x.n x.U).Ok lim fr d) {σ : State}
    (I : OptInv mx x μ fr (x.n ^ numFixed k) σ) :
    Ends lim P d (decodeStmt k) σ (x.n ^ numFixed k * (14 * numFixed k + 13)
      + 3 * (x.n ^ width k * (14 * width k + 13)) + 5 * k + 24) fun σ' =>
      (∃ v : Fin k → Fin x.n, (∀ p : Fin k, σ'.mem (x.res + p) = (v p).val) ∧
        ∀ v', better mx (x.G.cliqueWeight v) (x.G.cliqueWeight v')) ∧
      KeptBut μ σ'.mem fr x.res k := by
  obtain ⟨hokw, hokc, hw, -⟩ := hok
  simp only [optNeed] at hokw hokc
  have hn : 0 < x.n := hpre.n_pos
  have hres := hpre.belowRes
  have hrounds : 0 < x.n ^ numFixed k := by positivity
  -- there has been a round, so there is a best triangle
  obtain ⟨_, hloc, ⟨hzero, -⟩ | ⟨Fb, a, b, c, rfl, hbeats⟩⟩ := I.locals
  · omega
  refine (decode_spec hloc Fb.2 a.2 b.2 c.2
    ⟨hn, hw, le_trans (by exact_mod_cast (by omega)) hokw, by omega⟩).mono le_rfl ?_
  rintro σ' ⟨hdigits, hout⟩
  exact ⟨⟨cliqueOf hn k Fb a b c, fun p => hdigits p p.2,
    opt_of_best x.toKcInst hn Fb a b c fun F' a' b' c' => hbeats F' F'.2 a' b' c'⟩,
    fun z ⟨hz, hzr⟩ => (hout z hzr).trans (I.kept z hz)⟩

/-- **The host finds a k-clique of maximum (minimum) total weight.** -/
theorem opt_spec (hsol : Solves (optTriTask mx) P₀ pe T r) (hk : 3 ≤ k) (lim : Limits) (d : ℕ)
    (x : KcFindInst k) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (optNeed k r x.n x.U).Ok lim fr d) :
    Ends lim (P₀ ++ R) d (optBody k pe mx) ⟨frame [(x.n : ℤ), x.U, x.g, x.res, fr], μ⟩
      (optTime k T x.n x.U) fun σ' =>
      (∃ v : Fin k → Fin x.n, (∀ p : Fin k, σ'.mem (x.res + p) = (v p).val) ∧
        ∀ v', better mx (x.G.cliqueWeight v) (x.G.cliqueWeight v')) ∧
      KeptBut μ σ'.mem fr x.res k := by
  have hokw := hok.word
  have hokc := hok.cells
  have hw := hok.space
  simp only [optNeed] at hokw hokc
  have hfits : ∀ a : ℕ, a ≤ 3 * lenH k * x.U + 3 * lenH k + x.n ^ numFixed k + k + 4 →
      (a : ℤ) ≤ lim.word := fun a ha => le_trans (by exact_mod_cast (by omega)) hokw
  have hcost := sentinelE_cost_le k mx
  obtain ⟨-, -, -, hAt3⟩ := matH_places k x.n fr
  unfold optBody optTime
  -- Choice := fr; hostSetup k
  light_set fr
  light_piece (hostSetup_spec (k := k) (n := x.n) (fr := fr) rfl rfl hpre.n_pos hw
    (by omega) (hfits _ (by omega))) with ⟨_, μ₁⟩ ⟨rfl, hvt, hout⟩
  rw [updateLocals_frame]
  -- SolverFree := the free pointer for the solver, behind the three cells for its answer
  have h3 := hfits 3 (by omega)
  light_set (matH k x.n fr 3 + 3 : ℕ)
  -- BestWeight := a weight that every triangle beats
  refine Ends.setToThen (sentinel k x.U mx) ?_ (sentinelE_safe_val rfl (hfits _ (by omega)) mx)
  -- while Round < Rounds: optRound; then decodeStmt
  refine Ends.next (x.n ^ numFixed k * (optRoundT k T x.n x.U + 4) + 4) (Ends.whileConst
    (OptInv mx x μ fr) (x.n ^ numFixed k) (optRoundT k T x.n x.U) ?start ?round ?done
    (by simp only [Cond.cost, Expr.cost]; ring_nf; omega))
  case start =>
    exact ⟨⟨⟨sentinel k x.U mx, 0, 0, 0, 0⟩, LocalsBut.of_eq (by simp),
      Or.inl ⟨rfl, rfl⟩⟩, fun a ha => hout a (Or.inl ha), hvt⟩
  case round =>
    intro F σ hF I
    obtain ⟨_, hloc, -⟩ := I.locals
    have hround : σ.loc Round = F := hloc Round (by decide)
    have hrounds : σ.loc Rounds = (x.n ^ numFixed k : ℕ) := hloc Rounds (by decide)
    exact ⟨⟨trivial, trivial⟩, by
      simp only [Cond.Holds, Expr.val, hround, hrounds]
      exact_mod_cast hF, optRound_spec hsol hk hpre hok hF I⟩
  case done =>
    intro σ I
    obtain ⟨_, hloc, -⟩ := I.locals
    have hround : σ.loc Round = (x.n ^ numFixed k : ℕ) := hloc Round (by decide)
    have hrounds : σ.loc Rounds = (x.n ^ numFixed k : ℕ) := hloc Rounds (by decide)
    exact ⟨⟨trivial, trivial⟩, by simp [hround, hrounds],
      (optDecode_spec hpre hok I).mono (by light_time) fun _ h => h⟩

end whole

/-! ## The host as a reduction between tasks -/

/-- The need of the host is polynomially bounded if the need of the solver is. -/
theorem polyNeed_optNeed (k : ℕ) {r : ℕ → ℕ → Need} (hr : PolyNeed r) : PolyNeed (optNeed k r) := by
  unfold optNeed
  poly_need [hr.word, hr.cells, hr.depth]

/-- **Max-Weight (Min-Weight) k-Clique from Max-Weight (Min-Weight) Triangle** (Corollary 39). -/
theorem isHost_opt (mx : Bool) {k : ℕ} (hk : 3 ≤ k) :
    IsHost (optTriTask mx) (optKcTask mx k) (optTime k) (optNeed k) := by
  refine ⟨fun P p T r hsol => ?_, fun r hr => polyNeed_optNeed k hr⟩
  refine ⟨[optBody k p mx], P.length, optBody k p mx, by simp, ?_⟩
  intro R lim d x μ fr hpre hok
  rw [List.append_assoc]
  exact opt_spec hsol hk lim d x μ fr hpre hok

/-- **Max-Weight k-Clique from Max-Weight Triangle** (Corollary 39). -/
theorem isHost_maxKc {k : ℕ} (hk : 3 ≤ k) :
    IsHost maxTriTask (maxKcTask k) (optTime k) (optNeed k) :=
  optTriTask_true ▸ optKcTask_true k ▸ isHost_opt true hk

/-- **Min-Weight k-Clique from Min-Weight Triangle** (Corollary 39). -/
theorem isHost_minKc {k : ℕ} (hk : 3 ≤ k) :
    IsHost minTriTask (minKcTask k) (optTime k) (optNeed k) :=
  optTriTask_false ▸ optKcTask_false k ▸ isHost_opt false hk

end Light.Sec5
