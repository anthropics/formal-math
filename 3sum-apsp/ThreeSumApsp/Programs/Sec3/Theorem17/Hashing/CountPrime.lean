/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.Count
public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.StrassenTime
public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.ZOrder
public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Residues

/-!
# The count for one prime (proof of Theorem 17, "Hashing modulo a prime")

"For every prime p in the range we count the triples with S(a,b,c) ≡ 0 (mod p)", where S(a,b,c) =
w(a,b) + w(b,c) + w(a,c) is the weight of the triangle.  "Let P[a,c] := x^{w(a,c) mod p} and Q[c,b]
:= x^{w(b,c) mod p} be matrices over the ring ℤ[x]/(x^p - 1) […]; then F(p) + Z₀ is the sum over the
pairs (a,b) ∈ A × B of the coefficient of x^{-w(a,b) mod p} in (PQ)[a,b]."  Here F(p) is the number
of triples with S(a,b,c) ≠ 0 and p ∣ S(a,b,c), and Z₀ the number of triples with S(a,b,c) = 0.

countPrime(n, ab, bc, ac, p, len, K, N2, w) computes this count for one prime, in a work area at w.
Two letters of the quotation mean something else in the code.  There w is the address of the work
area, and the weights are the three lists ab, bc and ac.  And `P` is the program, while the matrices
P and Q occur only as the lists `matPList` and `matQList`.

The routine has three parts.

* The addresses of the parts of the work area (`cpAddr_spec`); they lie one behind the other
  (`cp_places`).
* Six tables: the doubles of p, the residues of the three lists of weights, the places of the
  Z-order, and the sizes 4^i p of the matrices of Strassen's recursion, which szTable(dst, p, J)
  writes (`szTable_spec`, `cpTables_spec`, `CpTabs`).
* The matrices P and Q in Z-order, their product by Strassen's algorithm, and the sum of the
  coefficients (`cpProduct_spec`).

`countPrime_spec` puts the three parts together.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

/-- The numbers of the procedures that countPrime calls. -/
structure CpNums : Type where
  pDbl : ℕ
  pResid : ℕ
  pResidues : ℕ
  pSpread : ℕ
  pSz : ℕ
  pBuild : ℕ
  pCount : ℕ
  str : StrNums

/-- The program holds the procedures that countPrime calls. -/
structure CpCtx (P : Program) (ν : CpNums) : Prop where
  hDbl : P[ν.pDbl]? = some dblTableBody
  hResid : P[ν.pResid]? = some residBody
  hResidues : P[ν.pResidues]? = some (residuesBody ν.pResid)
  hSpread : P[ν.pSpread]? = some spreadTableBody
  hSz : P[ν.pSz]? = some szTableBody
  hBuild : P[ν.pBuild]? = some buildZBody
  hCount : P[ν.pCount]? = some countZeroBody
  str : StrProg P ν.str

namespace CountPrime

/-- The local variables of countPrime.  The arguments n, ab, bc, ac, p, len, K, N2, w: N2 = 2^K is
the number of rows and columns of the padded matrices, and w, the address of the work area, is also
the address of the table of doubles.  Then n²; the addresses of the residues of the lists ab, bc and
ac, of the table of places and of the table of sizes; the size 4^K p of a matrix; the addresses
of P, Q, PQ and of the scratch space of Strassen's algorithm; a local that takes the results of the
calls, except the last one, whose result (the count) goes to local 0 and is returned. -/
abbrev Num : ℕ := 0
@[inherit_doc Num] abbrev ListAB : ℕ := 1
@[inherit_doc Num] abbrev ListBC : ℕ := 2
@[inherit_doc Num] abbrev ListAC : ℕ := 3
@[inherit_doc Num] abbrev Prime : ℕ := 4
@[inherit_doc Num] abbrev Len : ℕ := 5
@[inherit_doc Num] abbrev Level : ℕ := 6
@[inherit_doc Num] abbrev Rows : ℕ := 7
@[inherit_doc Num] abbrev Work : ℕ := 8
@[inherit_doc Num] abbrev Square : ℕ := 9
@[inherit_doc Num] abbrev ResAB : ℕ := 10
@[inherit_doc Num] abbrev ResBC : ℕ := 11
@[inherit_doc Num] abbrev ResAC : ℕ := 12
@[inherit_doc Num] abbrev Places : ℕ := 13
@[inherit_doc Num] abbrev Sizes : ℕ := 14
@[inherit_doc Num] abbrev Size : ℕ := 15
@[inherit_doc Num] abbrev MatP : ℕ := 16
@[inherit_doc Num] abbrev MatQ : ℕ := 17
@[inherit_doc Num] abbrev MatR : ℕ := 18
@[inherit_doc Num] abbrev Scr : ℕ := 19
@[inherit_doc Num] abbrev Res : ℕ := 20

end CountPrime

open CountPrime in
/-- The first part of countPrime: the addresses of the parts of the work area. -/
def cpAddr : Stmt :=
  .set Square (v Num *' v Num) ;;
  .set ResAB (v Work +' v Len +' k 1) ;;
  .set ResBC (v ResAB +' v Square) ;;
  .set ResAC (v ResBC +' v Square) ;;
  .set Places (v ResAC +' v Square) ;;
  .set Sizes (v Places +' v Rows) ;;
  .set Size (v Rows *' v Rows *' v Prime) ;;
  .set MatP (v Sizes +' v Level +' k 1) ;;
  .set MatQ (v MatP +' v Size) ;;
  .set MatR (v MatQ +' v Size) ;;
  .set Scr (v MatR +' v Size)

open CountPrime in
/-- The second part: the table of doubles, the residues of the three lists, the table of places, the
table of sizes. -/
def cpTables (ν : CpNums) : Stmt :=
  .call ν.pDbl [v Work, v Prime, v Len] Res ;;
  .call ν.pResidues [v ListAB, v ResAB, v Square, v Work, v Len] Res ;;
  .call ν.pResidues [v ListBC, v ResBC, v Square, v Work, v Len] Res ;;
  .call ν.pResidues [v ListAC, v ResAC, v Square, v Work, v Len] Res ;;
  .call ν.pSpread [v Places, v Rows] Res ;;
  .call ν.pSz [v Sizes, v Prime, v Level] Res

open CountPrime in
/-- The third part: the matrices P and Q, their product, the count. -/
def cpProduct (ν : CpNums) : Stmt :=
  .call ν.pBuild [v MatP, v ResAC, v Places, v Num, v Rows, v Prime, k 2, k 1] Res ;;
  .call ν.pBuild [v MatQ, v ResBC, v Places, v Num, v Rows, v Prime, k 1, k 2] Res ;;
  .call ν.str.pStr [v MatR, v MatP, v MatQ, v Level, v Sizes, v Prime, v Scr] Res ;;
  .call ν.pCount [v MatR, v ResAB, v Places, v Num, v Prime] Num

/-- countPrime(n, ab, bc, ac, p, len, K, N2, w). -/
def countPrimeBody (ν : CpNums) : Stmt := cpAddr ;; cpTables ν ;; cpProduct ν

/-- The number of cells of the work area of countPrime.  (The last summand is not written; it is
room that Strassen's algorithm asks for.) -/
def countCells (n p len K : ℕ) : ℕ :=
  (len + 1) + 3 * (n * n) + 2 ^ K + (K + 1) + 3 * (4 ^ K * p) + strScr p K + (8 * (4 ^ K * p) + 1)

/-- An upper bound on the number of steps of countPrime. -/
def countTime (n p len K : ℕ) : ℕ :=
  tDblTable len + 3 * tResidues (n * n) len + (30 * 2 ^ K + 17) + tSzTable K +
    2 * buildZTime n (2 ^ K) p + strSteps p K + countZeroTime n + 150

/-! ## The layout of the work area -/

/-- The address of the residues of the list ab. -/
def cpRab (w len : ℕ) : ℕ := w + (len + 1)

/-- The address of the residues of the list bc. -/
def cpRbc (w len n : ℕ) : ℕ := cpRab w len + n * n

/-- The address of the residues of the list ac. -/
def cpRac (w len n : ℕ) : ℕ := cpRbc w len n + n * n

/-- The address of the table of places. -/
def cpMort (w len n : ℕ) : ℕ := cpRac w len n + n * n

/-- The address of the table of sizes. -/
def cpSzt (w len n K : ℕ) : ℕ := cpMort w len n + 2 ^ K

/-- The address of the matrix P. -/
def cpPm (w len n K : ℕ) : ℕ := cpSzt w len n K + (K + 1)

/-- The address of the matrix Q. -/
def cpQm (w len n K p : ℕ) : ℕ := cpPm w len n K + 4 ^ K * p

/-- The address of the product. -/
def cpRm (w len n K p : ℕ) : ℕ := cpQm w len n K p + 4 ^ K * p

/-- The address of the scratch space of Strassen's algorithm. -/
def cpScr (w len n K p : ℕ) : ℕ := cpRm w len n K p + 4 ^ K * p

/-- The parts of the work area lie one behind the other; as one fact. -/
theorem cp_places (w len n K p : ℕ) :
    cpRab w len = w + (len + 1) ∧ cpRbc w len n = cpRab w len + n * n ∧
      cpRac w len n = cpRbc w len n + n * n ∧ cpMort w len n = cpRac w len n + n * n ∧
      cpSzt w len n K = cpMort w len n + 2 ^ K ∧ cpPm w len n K = cpSzt w len n K + (K + 1) ∧
      cpQm w len n K p = cpPm w len n K + 4 ^ K * p ∧
      cpRm w len n K p = cpQm w len n K p + 4 ^ K * p ∧
      cpScr w len n K p = cpRm w len n K p + 4 ^ K * p ∧
      w + countCells n p len K = cpScr w len n K p + strScr p K + (8 * (4 ^ K * p) + 1) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp only [cpScr, cpRm, cpQm, cpPm, cpSzt, cpMort, cpRac, cpRbc, cpRab, countCells]
  omega

/-- The local variables of countPrime after its first part. -/
@[simp] def cpFrame (n ab bc ac p len K w : ℕ) : List ℤ :=
  [n, ab, bc, ac, p, len, K, (2 ^ K : ℕ), w, (n * n : ℕ), cpRab w len, cpRbc w len n,
    cpRac w len n, cpMort w len n, cpSzt w len n K, (4 ^ K * p : ℕ), cpPm w len n K,
    cpQm w len n K p, cpRm w len n K p, cpScr w len n K p]

/-- **The first part of countPrime**, in 50 steps. -/
theorem cpAddr_spec {μ : ℕ → ℤ} {n ab bc ac p len K w : ℕ} (hw : (lim.space : ℤ) ≤ lim.word)
    (hp : 1 ≤ p) (hcells : w + countCells n p len K ≤ lim.space) :
    Ends lim P d cpAddr ⟨frame [n, ab, bc, ac, p, len, K, (2 ^ K : ℕ), w], μ⟩ 50 fun σ' =>
      σ' = ⟨frame (cpFrame n ab bc ac p len K w), μ⟩ := by
  have hplaces := cp_places w len n K p
  have hsq : ((2 ^ K : ℕ) : ℤ) * ((2 ^ K : ℕ) : ℤ) = ((4 ^ K : ℕ) : ℤ) := by
    rw [← Nat.cast_mul, ← mul_pow]
    norm_num
  have hsize : ((4 ^ K : ℕ) : ℤ) * p = ((4 ^ K * p : ℕ) : ℤ) := by push_cast; ring
  have hle : 4 ^ K ≤ 4 ^ K * p := Nat.le_mul_of_pos_right _ hp
  rw [cpFrame]
  generalize 4 ^ K * p = size at *
  generalize 4 ^ K = F at *
  generalize 2 ^ K = N2 at *
  refine Ends.setToThen (n * n : ℕ) <| Ends.setToThen (cpRab w len) <|
    Ends.setToThen (cpRbc w len n) <| Ends.setToThen (cpRac w len n) <|
    Ends.setToThen (cpMort w len n) <| Ends.setToThen (cpSzt w len n K) <|
    Ends.setToThen size (he := by light_side [hsq, hsize]) <|
    Ends.setToThen (cpPm w len n K) <| Ends.setToThen (cpQm w len n K p) <|
    Ends.setToThen (cpRm w len n K p) <| Ends.setTo (cpScr w len n K p) rfl

/-! ## What countPrime assumes -/

/-- What countPrime needs: the three lists of n² weights of absolute value at most U < 2^len lie
below the work area, the work area lies in the memory, and the numbers that are formed fit in a
word. -/
structure CountPrimePre (lim : Limits) (d : ℕ) (μ : ℕ → ℤ) (x : TriInst) (p len K w : ℕ) :
    Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  inst : x.Pre μ w
  p_pos : 1 ≤ p
  hK : K = Nat.clog 2 x.n
  hU : x.U < 2 ^ len
  cells : w + countCells x.n p len K ≤ lim.space
  wordDbl : ((p * 2 ^ (len + 1) : ℕ) : ℤ) ≤ lim.word
  wordStr : ((4 * (16 ^ K * p) : ℕ) : ℤ) ≤ lim.word
  wordSum : ((x.n * x.n * (16 ^ K * p) : ℕ) : ℤ) ≤ lim.word
  depth : d + 2 * K + 2 ≤ lim.depth

/-- A list of residues is as long as the list of numbers. -/
@[simp] theorem length_residList (p : ℕ) (l : List ℤ) : (residList p l).length = l.length := by
  simp [residList]

/-- Residues modulo p are below p. -/
theorem lt_of_mem_residList {p : ℕ} (hp : 1 ≤ p) {l : List ℤ} {x : ℕ} (hx : x ∈ residList p l) :
    x < p := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact resid_lt (by omega) w

section Premise

variable {μ : ℕ → ℤ} {x : TriInst} {p len K w : ℕ}

/-- The constant 4 fits in a word. -/
theorem CountPrimePre.four_le_word (pre : CountPrimePre lim d μ x p len K w) :
    (4 : ℤ) ≤ lim.word := by
  refine le_trans ?_ pre.wordStr
  have : 1 ≤ 16 ^ K * p := Nat.mul_pos (by positivity) pre.p_pos
  exact_mod_cast (by omega : 4 ≤ 4 * (16 ^ K * p))

/-- The size of a matrix fits in a word. -/
theorem CountPrimePre.size_le_word (pre : CountPrimePre lim d μ x p len K w) :
    ((4 ^ K * p : ℕ) : ℤ) ≤ lim.word := by
  have hle : 4 ^ K * p ≤ 16 ^ K * p := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by norm_num) K)
  exact le_trans (by exact_mod_cast (by omega : 4 ^ K * p ≤ 4 * (16 ^ K * p))) pre.wordStr

/-- The number of entries of a matrix fits in a word. -/
theorem CountPrimePre.sq_le_word (pre : CountPrimePre lim d μ x p len K w) :
    ((2 ^ K * 2 ^ K : ℕ) : ℤ) ≤ lim.word := by
  rw [show 2 ^ K * 2 ^ K = 4 ^ K by rw [← mul_pow]; norm_num]
  exact le_trans (by exact_mod_cast Nat.le_mul_of_pos_right _ pre.p_pos) pre.size_le_word

/-- The entries of the table of doubles fit in a word. -/
theorem CountPrimePre.dbl_le_word (pre : CountPrimePre lim d μ x p len K w) :
    ((p * 2 ^ len : ℕ) : ℤ) ≤ lim.word := by
  refine le_trans ?_ pre.wordDbl
  exact_mod_cast Nat.mul_le_mul_left p (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ len))

end Premise

/-! ## The procedures that countPrime calls -/

section meets

variable {μ : ℕ → ℤ}

/-- **dblTable** as a procedure. -/
theorem dblTable_meets {q dst p len : ℕ} (hP : P[q]? = some dblTableBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + (len + 1) ≤ lim.space)
    (hp : ((p * 2 ^ len : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [dst, p, len] μ (tDblTable len) fun _ μ' =>
      Seg μ' dst (dblList p len) ∧ SameOutside μ μ' dst (len + 1) :=
  Meets.of_body hP (dblTable_spec hw hdst hp)

/-- **residues** as a procedure. -/
theorem residues_meets {q pResid src dst m dbl p len U : ℕ} {l : List ℤ}
    (hP : P[q]? = some (residuesBody pResid)) (hR : P[pResid]? = some residBody)
    (hd : d < lim.depth) (pre : ResiduesPre lim μ src dst m dbl p len U l) :
    Meets lim P q d [src, dst, m, dbl, len] μ (tResidues m len) fun _ μ' =>
      SegN μ' dst (residList p l) ∧ SameOutside μ μ' dst m :=
  Meets.of_body hP (residues_spec hR hd pre)

end meets

/-! ## The tables -/

/-- The tables of countPrime are in their places. -/
structure CpTabs (μ : ℕ → ℤ) (x : TriInst) (p len K w : ℕ) : Prop where
  dbl : Seg μ w (dblList p len)
  rab : SegN μ (cpRab w len) (residList p x.AB)
  rbc : SegN μ (cpRbc w len x.n) (residList p x.BC)
  rac : SegN μ (cpRac w len x.n) (residList p x.AC)
  mort : Seg μ (cpMort w len x.n) (spreadList (2 ^ K))
  szt : Seg μ (cpSzt w len x.n K) (szList p K)

section parts

variable {ν : CpNums} {μ₀ μ μ' : ℕ → ℤ} {x : TriInst} {p len K w : ℕ}

/-- The tables stay in their places when only cells behind them change. -/
theorem CpTabs.keep (tabs : CpTabs μ x p len K w) (pre : CountPrimePre lim d μ₀ x p len K w)
    (hs : Kept μ μ' (cpPm w len x.n K) := by light_keep) : CpTabs μ' x p len K w := by
  have hplaces := cp_places w len x.n K p
  have hrows := Nat.one_le_two_pow (n := K)
  have lenM := length_spreadList (2 ^ K)
  light_facts pre.inst
  exact ⟨tabs.dbl.keep, tabs.rab.keep, tabs.rbc.keep, tabs.rac.keep, tabs.mort.keep,
    tabs.szt.keep⟩

/-- What a call of residues from countPrime assumes: the list l of weights at src lies below the
work area, the table of doubles is written, and the residues go to dst, behind that table. -/
theorem CountPrimePre.residuesPre (pre : CountPrimePre lim d μ₀ x p len K w)
    {src dst : ℕ} {l : List ℤ} (segDbl : Seg μ w (dblList p len)) (segSrc : Seg μ src l)
    (hlen : l.length = x.n * x.n) (hle : AbsLe l x.U) (hsrc : src + x.n * x.n ≤ w)
    (hdst : w + (len + 1) ≤ dst) (hend : dst + x.n * x.n ≤ lim.space) :
    ResiduesPre lim μ src dst (x.n * x.n) w p len x.U l := by
  have cells := pre.cells
  exact ⟨pre.space_le, pre.p_pos, segDbl, segSrc, hlen, hle, pre.hU, by omega, by omega, hend,
    by omega, Or.inr (by omega), Or.inr (by omega), pre.wordDbl⟩

open CountPrime in
/-- **The second part of countPrime** writes the six tables. -/
theorem cpTables_spec (ctx : CpCtx P ν) (pre : CountPrimePre lim d μ x p len K w) :
    Ends lim P d (cpTables ν) ⟨frame (cpFrame x.n x.ab x.bc x.ac p len K w), μ⟩
      (tDblTable len + 3 * tResidues (x.n * x.n) len + (30 * 2 ^ K + 17) + tSzTable K + 35)
      fun σ' => ∃ (r : ℤ) (μ' : ℕ → ℤ),
        σ' = ⟨frame (cpFrame x.n x.ab x.bc x.ac p len K w ++ [r]), μ'⟩ ∧
          CpTabs μ' x p len K w ∧ SameOutside μ μ' w (countCells x.n p len K) := by
  have hplaces := cp_places w len x.n K p
  have hrows := Nat.one_le_two_pow (n := K)
  have lenM := length_spreadList (2 ^ K)
  have cells := pre.cells
  have depth := pre.depth
  light_facts pre.inst
  -- the table of doubles
  light_call (dblTable_meets (dst := w) ctx.hDbl pre.space_le (by omega) pre.dbl_le_word)
    with _ μ₁ ⟨dbl₁, rest₁⟩
  -- the residues of the list ab
  light_call (residues_meets ctx.hResidues ctx.hResid (by omega)
    (pre.residuesPre (dst := cpRab w len) dbl₁ pre.inst.segAB.keep pre.inst.lenAB pre.inst.leAB
      pre.inst.belowAB (by omega) (by omega))) with _ μ₂ ⟨rab₂, rest₂⟩
  -- the residues of the list bc
  light_call (residues_meets ctx.hResidues ctx.hResid (by omega)
    (pre.residuesPre (dst := cpRbc w len x.n) dbl₁.keep pre.inst.segBC.keep pre.inst.lenBC
      pre.inst.leBC pre.inst.belowBC (by omega) (by omega))) with _ μ₃ ⟨rbc₃, rest₃⟩
  -- the residues of the list ac
  light_call (residues_meets ctx.hResidues ctx.hResid (by omega)
    (pre.residuesPre (dst := cpRac w len x.n) dbl₁.keep pre.inst.segAC.keep pre.inst.lenAC
      pre.inst.leAC pre.inst.belowAC (by omega) (by omega))) with _ μ₄ ⟨rac₄, rest₄⟩
  -- the table of places
  light_call (spreadTable_meets (dst := cpMort w len x.n) ctx.hSpread pre.space_le
    pre.four_le_word pre.sq_le_word (by omega)) with _ μ₅ ⟨mort₅, rest₅⟩
  -- the table of sizes
  light_call (szTable_meets (dst := cpSzt w len x.n K) ctx.hSz pre.space_le pre.four_le_word
    (by omega) pre.size_le_word) with r μ₆ ⟨szt₆, rest₆⟩
  -- Each call has written behind the tables that were there.
  exact ⟨r, μ₆, rfl, ⟨dbl₁.keep, rab₂.keep, rbc₃.keep, rac₄.keep, mort₅.keep, szt₆⟩,
    by light_keep⟩

/-! ## The product and the count -/

/-- What a call of buildZ from countPrime assumes: the residues R stand at r, one of the three lists
of residues, and the matrix goes to dst, behind the tables. -/
theorem CountPrimePre.buildZPre (pre : CountPrimePre lim d μ₀ x p len K w)
    (tabs : CpTabs μ x p len K w) {dst r : ℕ} {l : List ℤ} (segR : SegN μ r (residList p l))
    (hlen : l.length = x.n * x.n) (hr : r + x.n * x.n ≤ cpMort w len x.n)
    (hdst : cpPm w len x.n K ≤ dst) (hend : dst + 4 ^ K * p ≤ cpScr w len x.n K p) :
    BuildZPre lim μ dst r (cpMort w len x.n) x.n K p (residList p l) := by
  have hplaces := cp_places w len x.n K p
  have hrows := Nat.one_le_two_pow (n := K)
  have cells := pre.cells
  exact
    { space_le := pre.space_le
      res :=
        { len := by simp [hlen], seg := segR, lt := fun _ h => lt_of_mem_residList pre.p_pos h }
      table := { len := length_spreadList _, seg := tabs.mort }
      n_le := pre.hK ▸ Nat.le_pow_clog (by norm_num) x.n, p_pos := pre.p_pos, dst_le := by omega
      apartR := Or.inr (by omega), apartM := Or.inr (by omega) }

open CountPrime in
/-- **The third part of countPrime** returns the count. -/
theorem cpProduct_spec (ctx : CpCtx P ν) (pre : CountPrimePre lim d μ₀ x p len K w)
    (tabs : CpTabs μ x p len K w) (r : ℤ) :
    Ends lim P d (cpProduct ν) ⟨frame (cpFrame x.n x.ab x.bc x.ac p len K w ++ [r]), μ⟩
      (2 * buildZTime x.n (2 ^ K) p + strSteps p K + countZeroTime x.n + 36) fun σ' =>
        σ'.loc 0 = countOf x.n p x.AB x.BC x.AC ∧
          SameOutside μ σ'.mem w (countCells x.n p len K) := by
  have hplaces := cp_places w len x.n K p
  have hrows := Nat.one_le_two_pow (n := K)
  have h4 := pre.four_le_word
  have hw := pre.space_le
  have cells := pre.cells
  have depth := pre.depth
  have lenP := length_matPList x.n p K (residList p x.AC)
  -- the matrix P
  light_call (buildZ_P_meets ctx.hBuild (pre.buildZPre tabs (dst := cpPm w len x.n K) tabs.rac
    pre.inst.lenAC (by omega) le_rfl (by omega))) with _ μ₁ ⟨segP, rest₁⟩
  have tabs₁ : CpTabs μ₁ x p len K w := tabs.keep pre
  -- the matrix Q
  light_call (buildZ_Q_meets ctx.hBuild (pre.buildZPre tabs₁ (dst := cpQm w len x.n K p) tabs₁.rbc
    pre.inst.lenBC (by omega) (by omega) (by omega))) with _ μ₂ ⟨segQ, rest₂⟩
  have tabs₂ : CpTabs μ₂ x p len K w := tabs₁.keep pre
  -- the product
  light_call (strassen_spec ctx.str pre.space_le K
    { dst := cpRm w len x.n K p, a := cpPm w len x.n K, b := cpQm w len x.n K p
      szt := cpSzt w len x.n K, p := p, scr := cpScr w len x.n K p, len := 4 ^ K * p, J := K
      A := matPList x.n p K (residList p x.AC), B := matQList x.n p K (residList p x.BC)
      α := 1, β := 1 } μ₂
    { size := rfl, prime := pre.p_pos
      opA := { len := lenP, bound := absLe_matPList _ _ _ _, seg := segP.keep }
      opB := { len := length_matQList _ _ _ _, bound := absLe_matQList _ _ _ _, seg := segQ }
      table := { len := length_szList _ _, seg := tabs₂.szt }
      word := by rw [strassenBound_one_one]; exact_mod_cast pre.wordStr } _ (by omega))
    with _ μ₃ ⟨segR, rest₃⟩
  dsimp only at segR rest₃
  have tabs₃ : CpTabs μ₃ x p len K w := tabs₂.keep pre
  -- the count
  light_call (countZero_meets ctx.hCount (V := strassenBound p K 1 1)
    { space_le := pre.space_le
      mat :=
        { len := length_strassenList p K _ _ lenP (length_matQList _ _ _ _), seg := segR
          bound := absLe_strassenList p K _ _ 1 1 (absLe_matPList _ _ _ _) (absLe_matQList _ _ _ _)
            (by norm_num) (by norm_num) }
      res :=
        { len := by simp [pre.inst.lenAB], seg := tabs₃.rab
          lt := fun _ h => lt_of_mem_residList pre.p_pos h }
      table := { len := length_spreadList _, seg := tabs₃.mort }
      n_le := pre.hK ▸ Nat.le_pow_clog (by norm_num) x.n, rm_lt := by omega
      sum_le := by rw [strassenBound_one_one]; exact_mod_cast pre.wordSum })
    with _ μ₄ ⟨rfl, rfl⟩
  exact ⟨by simp [countOf, pre.hK], by light_keep⟩

/-- **countPrime** returns the count of the proof of Theorem 17 for the prime p, and changes only
cells of its work area. -/
theorem countPrime_spec (ctx : CpCtx P ν) (pre : CountPrimePre lim d μ x p len K w) :
    Ends lim P d (countPrimeBody ν) ⟨frame [x.n, x.ab, x.bc, x.ac, p, len, K, (2 ^ K : ℕ), w], μ⟩
      (countTime x.n p len K) fun σ' =>
        σ'.loc 0 = countOf x.n p x.AB x.BC x.AC ∧
          SameOutside μ σ'.mem w (countCells x.n p len K) := by
  unfold countTime
  -- the addresses
  light_piece (cpAddr_spec pre.space_le pre.p_pos pre.cells) with _ rfl
  -- the tables
  light_piece (cpTables_spec ctx pre) with _ ⟨r, μ₁, rfl, tabs, rest₁⟩
  -- the product and the count
  light_piece (cpProduct_spec ctx pre tabs r) with σ' ⟨hcount, rest₂⟩
  exact ⟨hcount, rest₁.trans rest₂⟩

/-- **countPrime** as a procedure. -/
theorem countPrime_meets {q : ℕ} (hP : P[q]? = some (countPrimeBody ν)) (ctx : CpCtx P ν)
    (pre : CountPrimePre lim d μ x p len K w) :
    Meets lim P q d [x.n, x.ab, x.bc, x.ac, p, len, K, (2 ^ K : ℕ), w] μ (countTime x.n p len K)
      fun r μ' =>
        r = countOf x.n p x.AB x.BC x.AC ∧ SameOutside μ μ' w (countCells x.n p len K) :=
  Meets.of_body hP (countPrime_spec ctx pre)

end parts

/-! ## Larger primes need more cells and more time -/

/-- The work area grows with p. -/
theorem countCells_mono {p q : ℕ} (h : p ≤ q) (n len K : ℕ) :
    countCells n p len K ≤ countCells n q len K := by
  have hsize : 4 ^ K * p ≤ 4 ^ K * q := Nat.mul_le_mul_left _ h
  have hscr := strScr_mono h K
  unfold countCells
  omega

/-- The time grows with p. -/
theorem countTime_mono {p q : ℕ} (h : p ≤ q) (n len K : ℕ) :
    countTime n p len K ≤ countTime n q len K := by
  have hsize : 2 ^ K * 2 ^ K * p ≤ 2 ^ K * 2 ^ K * q := Nat.mul_le_mul_left _ h
  have hsteps := strSteps_mono h K
  unfold countTime buildZTime
  omega

end Light.Sec3
