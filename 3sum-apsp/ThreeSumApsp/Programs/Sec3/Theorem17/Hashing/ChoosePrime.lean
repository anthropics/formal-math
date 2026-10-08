/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Hashing.CountPrime
public import ThreeSumApsp.Programs.Sec3.Theorem17.Parameters.Primes
public import ThreeSumApsp.Spec.Sec3.Theorem17.Choice

/-!
# The choice of the prime (proof of Theorem 17, "Hashing modulo a prime")

"We reduce the weights modulo a prime p ∈ [√D/2, √D), chosen deterministically. […] For every prime
p in the range we count the triples with S(a,b,c) ≡ 0 (mod p). […] We select the prime with the
smallest count".  Here S(a,b,c) is the weight of the triangle, the sum of its entries in the three
lists of weights ab, bc and ac, and D is the parameter of Theorem 17.

choosePrime(n, U, ab, bc, ac, D, w), where w is the address of the work area, lists the primes of
the range (`primesList D`) at w, computes the number len of binary digits of U and the numbers
K = ⌈log₂ n⌉ and 2^K (`chLevel_spec`), and goes through the primes once.  A round counts for one
prime, by a call of countPrime with the work area behind the list of the primes, and keeps the prime
if it is the first one or its count is smaller than the best so far (`chKeep_spec`,
`chRound_spec`).

On the pure side, `bestOf f L i` is the first of the first i primes with the smallest count, one
more prime changes it as the program does (`BestSoFar.step`), and at the end it is the chosen prime
(`bestOf_length`).  `choosePrime_spec` is the whole routine.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

/-- The numbers of the procedures that choosePrime calls. -/
structure ChNums : Type where
  pPrimes : ℕ
  pBitLen : ℕ
  pCountPrime : ℕ
  cp : CpNums
  pSqrt : ℕ
  pSieve : ℕ

/-- The program holds the procedures that choosePrime calls. -/
structure ChCtx (P : Program) (ν : ChNums) : Prop where
  hPrimes : P[ν.pPrimes]? = some (primesBody ν.pSqrt ν.pSieve)
  hBitLen : P[ν.pBitLen]? = some bitLenBody
  hCountPrime : P[ν.pCountPrime]? = some (countPrimeBody ν.cp)
  cp : CpCtx P ν.cp
  primes : Primes.Ctx P ν.pSqrt ν.pSieve

namespace ChoosePrime

/-- The local variables of choosePrime: the arguments n, U, ab, bc, ac, D, w; the number of primes;
len; K; 2^K; the address of the work area of countPrime; the number of the prime; the prime; its
count; the best prime so far; its count. -/
abbrev Num : ℕ := 0
@[inherit_doc Num] abbrev Bound : ℕ := 1
@[inherit_doc Num] abbrev ListAB : ℕ := 2
@[inherit_doc Num] abbrev ListBC : ℕ := 3
@[inherit_doc Num] abbrev ListAC : ℕ := 4
@[inherit_doc Num] abbrev Range : ℕ := 5
@[inherit_doc Num] abbrev Work : ℕ := 6
@[inherit_doc Num] abbrev Primes : ℕ := 7
@[inherit_doc Num] abbrev Len : ℕ := 8
@[inherit_doc Num] abbrev Level : ℕ := 9
@[inherit_doc Num] abbrev Rows : ℕ := 10
@[inherit_doc Num] abbrev Area : ℕ := 11
@[inherit_doc Num] abbrev Idx : ℕ := 12
@[inherit_doc Num] abbrev Prime : ℕ := 13
@[inherit_doc Num] abbrev Count : ℕ := 14
@[inherit_doc Num] abbrev Best : ℕ := 15
@[inherit_doc Num] abbrev BestCount : ℕ := 16

end ChoosePrime

open ChoosePrime in
/-- K = ⌈log₂ n⌉ and 2^K, by doubling. -/
def chLevel : Stmt :=
  .set Level (k 0) ;;
  .set Rows (k 1) ;;
  .while (v Rows <' v Num) (
    .set Rows (v Rows +' v Rows) ;;
    .set Level (v Level +' k 1))

open ChoosePrime in
/-- The prime is kept if it is the first one or its count is smaller than the best so far. -/
def chKeep : Stmt :=
  .ite (v Idx =' k 0) (.set Best (v Prime) ;; .set BestCount (v Count))
    (.ite (v Count <' v BestCount) (.set Best (v Prime) ;; .set BestCount (v Count)) .skip)

open ChoosePrime in
/-- One round: the count for the prime number i. -/
def chRound (ν : ChNums) : Stmt :=
  .set Prime (M (v Work +' v Idx)) ;;
  .call ν.pCountPrime
    [v Num, v ListAB, v ListBC, v ListAC, v Prime, v Len, v Level, v Rows, v Area] Count ;;
  chKeep

open ChoosePrime in
/-- choosePrime(n, U, ab, bc, ac, D, w). -/
def choosePrimeBody (ν : ChNums) : Stmt :=
  .call ν.pPrimes [v Work, v Range] Primes ;;
  .call ν.pBitLen [v Bound] Len ;;
  chLevel ;;
  .set Area (v Work +' v Primes) ;;
  .set Best (k 0) ;;
  .set BestCount (k 0) ;;
  .for Idx (v Primes) (chRound ν) ;;
  .set Num (v Best)

/-- The number of cells that choosePrime may change, from w on: the list of the primes and the work
area of countPrime for the largest possible prime. -/
def chooseCells (n U D : ℕ) : ℕ :=
  Nat.sqrt D + countCells n (Nat.sqrt D) (bitLen U) (Nat.clog 2 n)

/-- An upper bound on the number of steps of choosePrime. -/
def chooseTime (n U D : ℕ) : ℕ :=
  tPrimes D + tBitLen U + 12 * Nat.clog 2 n +
    Nat.sqrt D * (countTime n (Nat.sqrt D) (bitLen U) (Nat.clog 2 n) + 50) + 60

/-- What choosePrime needs: the three lists of n² weights of absolute value at most U lie below w,
the cells from w on lie in the memory, and the numbers that are formed fit in a word. -/
structure ChoosePrimePre (lim : Limits) (d : ℕ) (μ : ℕ → ℤ) (x : TriInst) (D w : ℕ) : Prop where
  space_le : (lim.space : ℤ) ≤ lim.word
  inst : x.Pre μ w
  cells : w + chooseCells x.n x.U D ≤ lim.space
  wordD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word
  wordU : ((2 * x.U + 2 : ℕ) : ℤ) ≤ lim.word
  wordN : ((2 * x.n + 1 : ℕ) : ℤ) ≤ lim.word
  wordDbl : ((Nat.sqrt D * 2 ^ (bitLen x.U + 1) : ℕ) : ℤ) ≤ lim.word
  wordStr : ((4 * (16 ^ Nat.clog 2 x.n * Nat.sqrt D) : ℕ) : ℤ) ≤ lim.word
  wordSum : ((x.n * x.n * (16 ^ Nat.clog 2 x.n * Nat.sqrt D) : ℕ) : ℤ) ≤ lim.word
  depth : d + 2 * Nat.clog 2 x.n + 3 ≤ lim.depth

/-! ## The pure side: the best prime so far -/

/-- The count is not negative: it is a number of triples. -/
theorem countOf_nonneg (n : ℕ) {p : ℕ} (hp : 1 ≤ p) (AB BC AC : List ℤ) :
    0 ≤ countOf n p AB BC AC := by
  rw [countOf_eq n AB BC AC (by omega)]
  exact Int.natCast_nonneg _

/-- What the locals best and cnt hold after i primes: nothing yet, or the best prime so far and its
count c, where c q is the count for the prime q. -/
def BestSoFar (c : ℕ → ℤ) (L : List ℕ) (i : ℕ) (best cnt : ℤ) : Prop :=
  (i = 0 ∧ best = 0) ∨
    (1 ≤ i ∧ best = (bestOf (fun q => (c q).toNat) L i : ℕ) ∧
      cnt = c (bestOf (fun q => (c q).toNat) L i) ∧ 0 ≤ cnt)

/-- One more prime: it is kept if it is the first one or its count is smaller. -/
theorem BestSoFar.step {c : ℕ → ℤ} {L : List ℕ} {i : ℕ} {best cnt : ℤ}
    (h : BestSoFar c L i best cnt) (hi : i < L.length) (hc : 0 ≤ c L[i]) :
    BestSoFar c L (i + 1) (if i = 0 ∨ c L[i] < cnt then (L[i] : ℕ) else best)
      (if i = 0 ∨ c L[i] < cnt then c L[i] else cnt) := by
  refine Or.inr ⟨Nat.succ_pos i, ?_⟩
  obtain ⟨rfl, -⟩ | ⟨hi1, rfl, rfl, hcnt⟩ := h
  · rw [show bestOf (fun q => (c q).toNat) L (0 + 1) = L[0] from
      (bestOf_one _ L).trans (List.getD_eq_getElem _ _ hi)]
    simp [hc]
  · have hcmp : (c L[i]).toNat < (c (bestOf (fun q => (c q).toNat) L i)).toNat ↔
        c L[i] < c (bestOf (fun q => (c q).toNat) L i) := by omega
    rw [bestOf_succ _ L hi1 hi]
    simp only [hcmp, show i ≠ 0 by omega, false_or]
    split_ifs <;> simp [hc, hcnt]

/-! ## The parts of the program -/

/-- The local variables of choosePrime during the loop over the primes. -/
@[simp] def chFrame (n U ab bc ac D w nP len K : ℕ) (i q c best cnt : ℤ) : List ℤ :=
  [n, U, ab, bc, ac, D, w, nP, len, K, (2 ^ K : ℕ), (w + nP : ℕ), i, q, c, best, cnt]

section parts

variable {ν : ChNums} {μ μ' : ℕ → ℤ} {n U ab bc ac D w nP len K : ℕ} {AB BC AC : List ℤ}

/-- **K = ⌈log₂ n⌉ and 2^K.** -/
theorem chLevel_spec (hword : ((2 * n + 1 : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d chLevel ⟨frame [n, U, ab, bc, ac, D, w, nP, len], μ⟩ (12 * Nat.clog 2 n + 8)
      fun σ' => σ' = ⟨frame [n, U, ab, bc, ac, D, w, nP, len, (Nat.clog 2 n : ℕ),
        (2 ^ Nat.clog 2 n : ℕ)], μ⟩ := by
  have test : ∀ j, 2 ^ j < n ↔ j < Nat.clog 2 n := fun j =>
    (Nat.lt_clog_iff_pow_lt (by norm_num)).symm
  generalize Nat.clog 2 n = L at test
  push_cast at hword
  -- level := 0; rows := 1
  light_set (0 : ℕ)
  light_set (1 : ℕ)
  -- while rows < n: rows := rows + rows; level := level + 1.  Before round j, rows = 2^j.
  refine Ends.whileBlock
    (fun j σ => σ = ⟨frame [n, U, ab, bc, ac, D, w, nP, len, j, (2 ^ j : ℕ)], μ⟩) L (by simp) ?round
    ?done
  case round =>
    rintro j _ hj rfl
    have hlt := (test j).2 hj
    have hjlt : j < 2 ^ j := Nat.lt_two_pow_self
    rw [pow_succ, Nat.mul_two]
    generalize 2 ^ j = q at hlt hjlt
    exact ⟨by light_side, by light_side, by light_side, by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hnot := mt (test L).1 (lt_irrefl L)
    generalize 2 ^ L = q at hnot
    exact ⟨by light_side, by light_side, rfl⟩

/-- **Keeping the better prime.** -/
theorem chKeep_spec (h0 : 0 ≤ lim.word) (i : ℕ) (q c best cnt : ℤ) :
    Ends lim P d chKeep ⟨frame (chFrame n U ab bc ac D w nP len K i q c best cnt), μ⟩ 12 fun σ' =>
      σ' = ⟨frame (chFrame n U ab bc ac D w nP len K i q c
        (if i = 0 ∨ c < cnt then q else best) (if i = 0 ∨ c < cnt then c else cnt)), μ⟩ := by
  refine Ends.block ⟨by simp [chKeep, h0], ?_⟩ (by simp [chKeep])
  by_cases hi : i = 0 <;> by_cases hc : c < cnt <;>
    simp [chKeep, update_frame_setLocal, hi, hc]

variable {x : TriInst}

/-- The cells that choosePrime may change lie in the memory: the list of the primes, and the work
area of countPrime. -/
theorem ChoosePrimePre.cells_le (pre : ChoosePrimePre lim d μ x D w) :
    w + (Nat.sqrt D + countCells x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n)) ≤ lim.space :=
  pre.cells

/-- What countPrime assumes holds for each prime q of the range, with the work area behind the list
of the primes, as long as only cells from w on have changed. -/
theorem ChoosePrimePre.countPre (pre : ChoosePrimePre lim d μ x D w)
    (rest : SameOutside μ μ' w (chooseCells x.n x.U D)) {q : ℕ} (hq : q ∈ primesList D) :
    CountPrimePre lim (d + 1) μ' x q (bitLen x.U) (Nat.clog 2 x.n) (w + (primesList D).length) := by
  have cells := pre.cells_le
  have depth := pre.depth
  have hprimes := length_primesList_le D
  have hqS : q ≤ Nat.sqrt D := le_sqrt_of_mem_primesList hq
  have hcells := countCells_mono hqS x.n (bitLen x.U) (Nat.clog 2 x.n)
  exact
    { space_le := pre.space_le, inst := pre.inst.keep.mono (Nat.le_add_right _ _)
      p_pos := (mem_primesList.1 hq).1.one_le, hK := rfl, hU := Nat.lt_size_self x.U
      cells := by omega
      wordDbl := le_trans (by exact_mod_cast Nat.mul_le_mul_right _ hqS) pre.wordDbl
      wordStr := le_trans
        (by exact_mod_cast Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left _ hqS)) pre.wordStr
      wordSum := le_trans
        (by exact_mod_cast Nat.mul_le_mul_left (x.n * x.n) (Nat.mul_le_mul_left _ hqS)) pre.wordSum
      depth := by omega }

/-- The state of choosePrime before round i: the best prime so far and its count are in their
locals, the list of the primes stands at w, and only cells from w on have changed. -/
def ChInv (μ : ℕ → ℤ) (x : TriInst) (D w i : ℕ) (σ : State) : Prop :=
  ∃ (q c best cnt : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame (chFrame x.n x.U x.ab x.bc x.ac D w (primesList D).length (bitLen x.U)
      (Nat.clog 2 x.n) i q c best cnt), μ'⟩ ∧
    BestSoFar (fun p => countOf x.n p x.AB x.BC x.AC) (primesList D) i best cnt ∧
    SegN μ' w (primesList D) ∧ SameOutside μ μ' w (chooseCells x.n x.U D)

open ChoosePrime in
/-- **One round of choosePrime.** -/
theorem chRound_spec (ctx : ChCtx P ν) (pre : ChoosePrimePre lim d μ x D w) {i : ℕ}
    (hi : i < (primesList D).length) {σ : State} (h : ChInv μ x D w i σ) :
    Ends lim P d (chRound ν) σ (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 28)
      fun σ' => σ'.loc Idx = i ∧ ChInv μ x D w (i + 1)
        { σ' with loc := Function.update σ'.loc Idx ((i : ℤ) + 1) } := by
  obtain ⟨q₀, c₀, best, cnt, μ', rfl, hbest, seg, rest⟩ := h
  have hw := pre.space_le
  have cells := pre.cells_le
  have depth := pre.depth
  have hprimes := length_primesList_le D
  have hmem : (primesList D)[i] ∈ primesList D := List.getElem_mem hi
  have htime := countTime_mono (le_sqrt_of_mem_primesList hmem) x.n (bitLen x.U) (Nat.clog 2 x.n)
  have hcells :=
    countCells_mono (le_sqrt_of_mem_primesList hmem) x.n (bitLen x.U) (Nat.clog 2 x.n)
  have hread : μ' (w + i) = ((primesList D)[i] : ℕ) := by
    rw [seg i (by simpa using hi), List.getElem_map]
  -- prime := w[i]
  light_set ((primesList D)[i] : ℕ) using hread
  -- count := countPrime(n, ab, bc, ac, prime, len, K, 2^K, area)
  refine Ends.callToThen (countPrime_meets ctx.hCountPrime ctx.cp (pre.countPre rest hmem)) ?_
    (hT := by simp; omega)
  rintro _ μ'' ⟨rfl, rest'⟩
  -- The prime is kept if it is the first one or its count is smaller.
  refine (chKeep_spec (by omega) i _ _ best cnt).mono (by simp; omega) ?_
  rintro _ rfl
  refine ⟨by simp, ((primesList D)[i] : ℕ), countOf x.n (primesList D)[i] x.AB x.BC x.AC, _, _,
    μ'', by simp [update_frame_setLocal],
    hbest.step hi (countOf_nonneg x.n (mem_primesList.1 hmem).1.one_le x.AB x.BC x.AC),
    seg.keep, rest.trans (rest'.mono (by omega) ?_)⟩
  unfold chooseCells
  omega

/-- **primes** as a procedure. -/
theorem primes_meets {q dst pSqrt pSieve : ℕ} (hP : P[q]? = some (primesBody pSqrt pSieve))
    (C : Primes.Ctx P pSqrt pSieve) (hw : (lim.space : ℤ) ≤ lim.word)
    (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word) (hdst : dst + (2 * Nat.sqrt D + 1) ≤ lim.space)
    (hd : d < lim.depth) :
    Meets lim P q d [dst, D] μ (tPrimes D) fun r μ' =>
      r = ((primesList D).length : ℕ) ∧ SegN μ' dst (primesList D) ∧
        SameOutside μ μ' dst (2 * Nat.sqrt D + 1) :=
  Meets.of_body hP (primes_spec C hw hD hdst hd)

/-- **bitLen** as a procedure. -/
theorem bitLen_meets {q : ℕ} (hP : P[q]? = some bitLenBody)
    (hU : ((2 * U + 2 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P q d [U] μ (tBitLen U) fun r μ' => r = (bitLen U : ℕ) ∧ μ' = μ :=
  Meets.of_body hP (bitLen_spec hU)

open ChoosePrime in
/-- **choosePrime** returns the first prime of the range with the smallest count (0 if the range has
no prime), and changes only cells of its work area. -/
theorem choosePrime_spec (ctx : ChCtx P ν) (pre : ChoosePrimePre lim d μ x D w) :
    Ends lim P d (choosePrimeBody ν) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, D, w], μ⟩
      (chooseTime x.n x.U D) fun σ' =>
        σ'.loc 0 = (chosenPrime x.n D x.AB x.BC x.AC : ℕ) ∧
          SameOutside μ σ'.mem w (chooseCells x.n x.U D) := by
  have hw := pre.space_le
  have cells := pre.cells_le
  have depth := pre.depth
  have hprimes := length_primesList_le D
  have hroom : Nat.sqrt D + 1 ≤ countCells x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) := by
    have hle : Nat.sqrt D ≤ 4 ^ Nat.clog 2 x.n * Nat.sqrt D :=
      Nat.le_mul_of_pos_left _ (by positivity)
    unfold countCells
    generalize 4 ^ Nat.clog 2 x.n * Nat.sqrt D = A at hle ⊢
    generalize 2 ^ Nat.clog 2 x.n = B
    omega
  have hloop : (primesList D).length *
      (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 36) ≤
      Nat.sqrt D * (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 50) :=
    Nat.mul_le_mul (length_primesList_le D) (by omega)
  unfold chooseTime
  -- primes := the primes of the range, at w
  light_call (primes_meets (dst := w) ctx.hPrimes ctx.primes pre.space_le pre.wordD
    (by omega) (by omega)) with _ μ₁ ⟨rfl, seg, rest⟩
  -- len := bitLen(U)
  light_call (bitLen_meets ctx.hBitLen pre.wordU) with _ μ₂ ⟨rfl, hμ⟩
  rw [hμ]
  -- K and 2^K
  light_piece (chLevel_spec pre.wordN) with _ rfl
  -- area := w + primes; best := 0; bestCount := 0
  light_set (w + (primesList D).length : ℕ)
  light_set 0
  light_set 0
  -- for i < primes: one round
  refine Ends.next _ (Ends.for (ChInv μ x D w) (primesList D).length
    (countTime x.n (Nat.sqrt D) (bitLen x.U) (Nat.clog 2 x.n) + 28) ?start
    (fun i σ hi _ h => chRound_spec ctx pre hi h) ?done ?bound (hT := le_rfl))
    (by simp; ring_nf at hloop ⊢; omega)
  case start =>
    exact ⟨0, 0, 0, 0, μ₁, by simp [update_frame_setLocal], Or.inl ⟨rfl, rfl⟩, seg,
      rest.mono le_rfl (by unfold chooseCells; omega)⟩
  case bound =>
    rintro i _ - - ⟨q, c, best, cnt, μ', rfl, -⟩
    simp
  case done =>
    rintro _ - ⟨q, c, best, cnt, μ', rfl, hbest, -, rest'⟩
    -- return best
    refine Ends.setTo best ⟨?_, rest'⟩ (hT := by simp; ring_nf at hloop ⊢; omega)
    change best = (((primesList D).argmin fun q => (countOf x.n q x.AB x.BC x.AC).toNat).getD 0 : ℕ)
    obtain ⟨hnil, rfl⟩ | ⟨hpos, rfl, -, -⟩ := hbest
    · rw [List.eq_nil_of_length_eq_zero hnil]
      rfl
    · rw [bestOf_length]

/-- **choosePrime** as a procedure. -/
theorem choosePrime_meets {q : ℕ} (hP : P[q]? = some (choosePrimeBody ν)) (ctx : ChCtx P ν)
    (pre : ChoosePrimePre lim d μ x D w) :
    Meets lim P q d [x.n, x.U, x.ab, x.bc, x.ac, D, w] μ (chooseTime x.n x.U D) fun r μ' =>
      r = (chosenPrime x.n D x.AB x.BC x.AC : ℕ) ∧ SameOutside μ μ' w (chooseCells x.n x.U D) :=
  Meets.of_body hP (choosePrime_spec ctx pre)

end parts

end Light.Sec3
