/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecCrossing_PolyDefs
public import Eight.SecCrossing_MulOut
public import SingleBitPieces.SecCrossing_PolyA
public import ToTuring.Lib.Table

/-! # Lemma 2 from the eight-square identity: «computable in time poly(λ)»

Lemma 2 of the paper says of the functions A_i, and of the functions of both factorizations, that
they are «computable in time poly(λ)». This file gives certificates (`Groundwork.PolyT`,
proof/machines/ToTuring/PolyT.lean: some fragment of a
multi-stack machine of Mathlib turns the word of the input into the word of the output within a
number of steps polynomial in the length of the input) for the three programs `aMul`, `fTop`, `fBot`
of proof/networks/Eight/SecCrossing_PolyDefs.lean, and for all parts of the family `eightF`
(`stKeeps`).
That the programs compute A_i and factorize it is proved in other files.

How: ψ, R and C are functions of finitely many blocks of three bits, hence tables. The strings are
lists of bits, so λ and t = ⌈λ/3⌉ are given in unary. The program for A_i («multiplying them out one
at a time») is a loop of t rounds whose state is a list of at most t + 1 integers of at most t + 1
bits
(`len_mulUpTo_le`, proof/networks/Eight/SecCrossing_MulOut.lean). The index i comes in binary and
may be huge; it is only used to look an entry of a list up. The number s of a block is the length of
a loop in `off`; it is replaced by min(s, t) inside the product over s < t.
The auxiliary statements are in the namespace `Eight.SecCrossing_Cert`. -/

public section

namespace Eight

open Groundwork PaddedDescent.F ClauseBound.Alg SingleBitPieces.SecCrossing_PolyA

namespace SecCrossing_Cert

variable {α : Type} [Enc α]

/-! ### Closure lemmas -/

/-- A product over s < n is polynomial-time, for n in unary; the factors need to be polynomial-time
only at indices cut off at n (min(s, n)). -/
theorem prodL_polyT' {n : α → ℕ} {f : α → ℕ → ℤ} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    PolyT fun x => prodL (n x) (f x) :=
  (prodL_polyT (f := fun x s => f x (min s (n x))) hn hf).congr fun x => by
    rw [prodL_eq, prodL_eq]
    exact Finset.prod_congr rfl fun s hs => by rw [min_eq_left (Finset.mem_range.1 hs).le]

/-- t = ⌈λ/3⌉ is given in unary, for λ in unary. -/
theorem tOf_unary {lam : α → ℕ} (hl : Unary lam) : Unary fun x => tOf (lam x) := by
  unfold tOf; fun_prop

/-! ### Blocks -/

/-- Three bits of a list from a position on. -/
theorem blkAt_polyT {w : α → List Bool} {j : α → ℕ} (hw : PolyT w) (hj : PolyT j) : PolyT fun x => blkAt (w x) (j x) := by
  unfold blkAt; fun_prop

/-- The block number s of a string. -/
theorem blkL_polyT {w : α → List Bool} {s : α → ℕ} (hw : PolyT w) (hs : PolyT s) : PolyT fun x => blkL (w x) (s x) := by
  unfold blkL
  exact blkAt_polyT hw (by fun_prop)

/-- ψ_k(p, q) is a table. -/
theorem psi_polyT {k p q : α → Block} (hk : PolyT k) (hp : PolyT p) (hq : PolyT q) : PolyT fun x => psi (k x) (p x) (q x) :=
  PolyT.table₃ psi hk hp hq

/-- R is a table. -/
theorem Rb_polyT {a b c d : α → Block} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) (hd : PolyT d) : PolyT fun x => Rb (a x) (b x) (c x) (d x) :=
  PolyT.comp (g := fun x => ((a x, b x), (c x, d x))) (PolyT.table fun p : (Block × Block) × (Block × Block) => Rb p.1.1 p.1.2 p.2.1 p.2.2) (by fun_prop)

/-- C is a table. -/
theorem Cb_polyT {a b c d : α → Block} (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) (hd : PolyT d) : PolyT fun x => Cb (a x) (b x) (c x) (d x) :=
  PolyT.comp (g := fun x => ((a x, b x), (c x, d x))) (PolyT.table fun p : (Block × Block) × (Block × Block) => Cb p.1.1 p.1.2 p.2.1 p.2.2) (by fun_prop)

/-! ### A_i -/

/-- R at the block number s. -/
theorem rAt_polyT : PolyT fun p : FourL × ℕ => rAt p.1 p.2 := by
  unfold rAt
  exact Rb_polyT (blkL_polyT (by fun_prop) (by fun_prop)) (blkL_polyT (by fun_prop) (by fun_prop)) (blkL_polyT (by fun_prop) (by fun_prop))
    (blkL_polyT (by fun_prop) (by fun_prop))

/-- C at the block number s. -/
theorem cAt_polyT : PolyT fun p : FourL × ℕ => cAt p.1 p.2 := by
  unfold cAt
  exact Cb_polyT (blkL_polyT (by fun_prop) (by fun_prop)) (blkL_polyT (by fun_prop) (by fun_prop)) (blkL_polyT (by fun_prop) (by fun_prop))
    (blkL_polyT (by fun_prop) (by fun_prop))

/-- The number of blocks is given in unary. -/
theorem tL_unary : Unary tL := by
  unfold tL
  exact tOf_unary (by fun_prop)

/-- One multiplication is polynomial-time. -/
theorem mulStep_polyT {r c : α → ℤ} {l : α → List ℤ} (hr : PolyT r) (hc : PolyT c) (hl : PolyT l) : PolyT fun x => mulStep (r x) (c x) (l x) := by
  unfold mulStep
  fun_prop

/-- «multiplying them out one at a time takes time poly(λ)»: the paper's program is polynomial-time.
It is a loop of t rounds; a loop is polynomial-time if each round is and the words of all the states
that occur have polynomial length
(Groundwork.PolyT.foldl), which is len_mulUpTo_le. -/
theorem mulOut_polyT : PolyT mulOut := by
  have hr : PolyT fun p : FourL × List ℤ × ℕ => rAt p.1 p.2.2 := PolyT.comp (g := fun p : FourL × List ℤ × ℕ => (p.1, p.2.2)) rAt_polyT (by fun_prop)
  have hc : PolyT fun p : FourL × List ℤ × ℕ => cAt p.1 p.2.2 := PolyT.comp (g := fun p : FourL × List ℤ × ℕ => (p.1, p.2.2)) cAt_polyT (by fun_prop)
  refine PolyT.foldl (l := fun q : FourL => List.range (tL q)) (a := fun _ => [1]) (g := fun q l s => mulStep (rAt q s) (cAt q s) l)
    (PolyT.range tL_unary) (PolyT.const _) (mulStep_polyT hr hc (by fun_prop))
    ⟨fun n => (n + 1) * (3 * n + 10) + 2, ((PB.id'.add (PB.const 1)).mul (((PB.const 3).mul PB.id').add (PB.const 10))).add (PB.const 2), fun q k => ?_⟩
  rw [List.take_range]
  have h1 : min k (tL q) ≤ len q := (min_le_right _ _).trans (MulOut.tL_le_len q)
  refine (len_mulUpTo_le q (min k (tL q))).trans ?_
  exact Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 2

/-- The entry number i of the list, i in binary, is polynomial-time. -/
theorem aMul_polyT : PolyT aMul := by
  have h := mulOut_polyT
  unfold aMul
  fun_prop

/-! ### The two factorizations -/

/-- The number of bits of the factorization with θ = (Q, θ') is polynomial-time. -/
theorem longCap_polyT {tr : α → Bool} {t i : α → ℕ} (htr : PolyT tr) (ht : PolyT t) (hi : PolyT i) : PolyT fun x => longCap (tr x) (t x) (i x) := by
  unfold longCap; fun_prop

/-- The choice between the two factorizations is polynomial-time, for λ in unary. -/
theorem useLong_polyT {tr : α → Bool} {lam i : α → ℕ} (htr : PolyT tr) (hl : Unary lam) (hi : PolyT i) : PolyT fun x => useLong (tr x) (lam x) (i x) := by
  have h1 := longCap_polyT htr (tOf_unary hl).poly hi
  have h2 := hl.poly
  unfold useLong; fun_prop

/-- The test `wide` (whether the block number s takes the factor through 6 bits rather than ψ,
through 3 bits) is polynomial-time. -/
theorem wide_polyT {tr : α → Bool} {Q : α → List Bool} {s : α → ℕ} (htr : PolyT tr) (hQ : PolyT Q) (hs : PolyT s) : PolyT fun x => wide (tr x) (Q x) (s x) := by
  unfold wide; fun_prop

/-- The place where the index of the block number s begins is polynomial-time, for s in unary. -/
theorem off_polyT {tr : α → Bool} {Q : α → List Bool} {s : α → ℕ} (htr : PolyT tr) (hQ : PolyT Q) (hs : Unary s) : PolyT fun x => off (tr x) (Q x) (s x) := by
  have h1 : PolyT fun p : α × ℕ => wide (tr p.1) (Q p.1) p.2 := wide_polyT (PolyT.comp htr PolyT.id'.fst) (PolyT.comp hQ PolyT.id'.fst) PolyT.id'.snd
  have h2 := hs.poly
  unfold off
  exact PolyT.add (by fun_prop) (PolyT.mul (PolyT.const 3) (PolyT.countP (f := fun x k => wide (tr x) (Q x) k) h1 (PolyT.range hs)))

/-- The factor of the block number s in the first function is polynomial-time, for s in unary. -/
theorem topAt_polyT {tr : α → Bool} {Q w a b : α → List Bool} {s : α → ℕ} (htr : PolyT tr) (hQ : PolyT Q) (hw : PolyT w) (ha : PolyT a) (hb : PolyT b)
    (hs : Unary s) : PolyT fun x => topAt (tr x) (Q x) (w x) (a x) (b x) (s x) := by
  have ho := off_polyT htr hQ hs
  have h1 := blkAt_polyT hw ho
  have h2 := blkAt_polyT hw (PolyT.add ho (PolyT.const 3))
  have h3 := blkL_polyT ha hs.poly
  have h4 := blkL_polyT hb hs.poly
  unfold topAt
  exact PolyT.ite' (PolyT.decide_eq (wide_polyT htr hQ hs.poly) (PolyT.const true))
    (PolyT.ite' (PolyT.decide_and (PolyT.decide_eq h3 h1) (PolyT.decide_eq h4 h2)) (PolyT.const 1) (PolyT.const 0)) (psi_polyT h1 h3 h4)

/-- The factor of the block number s in the second function is polynomial-time, for s in unary. -/
theorem botAt_polyT {tr : α → Bool} {Q w a b : α → List Bool} {s : α → ℕ} (htr : PolyT tr) (hQ : PolyT Q) (hw : PolyT w) (ha : PolyT a) (hb : PolyT b)
    (hs : Unary s) : PolyT fun x => botAt (tr x) (Q x) (w x) (a x) (b x) (s x) := by
  have ho := off_polyT htr hQ hs
  have h1 := blkAt_polyT hw ho
  have h2 := blkAt_polyT hw (PolyT.add ho (PolyT.const 3))
  have h3 := blkL_polyT ha hs.poly
  have h4 := blkL_polyT hb hs.poly
  unfold botAt
  exact PolyT.ite' (PolyT.decide_eq (wide_polyT htr hQ hs.poly) (PolyT.const true)) (Rb_polyT h1 h3 h2 h4) (psi_polyT h1 h4 h3)

/-- The arguments of `fTop` and `fBot`: direction, i, two strings, θ. -/
abbrev Arg : Type := Bool × ℕ × List Bool × List Bool × List Bool

/-- λ, the length of the first string, is given in unary. -/
theorem lam_unary : Unary fun q : Arg => q.2.2.1.length := Unary.of_length PolyT.id'.snd.snd.fst

/-- t is given in unary. -/
theorem t_unary : Unary fun q : Arg => tOf q.2.2.1.length := tOf_unary lam_unary

/-- The test «|Q| = i» is polynomial-time. -/
theorem card_polyT : PolyT fun q : Arg => decide ((q.2.2.2.2.take (tOf q.2.2.1.length)).count true = q.2.1) := by
  have h := t_unary.poly
  fun_prop

/-- The first function of the factorization with θ = (Q, θ') is polynomial-time. -/
theorem topLong_polyT : PolyT fun q : Arg =>
    prodL (tOf q.2.2.1.length) (topAt q.1 (q.2.2.2.2.take (tOf q.2.2.1.length)) (q.2.2.2.2.drop (tOf q.2.2.1.length)) q.2.2.1 q.2.2.2.1) := by
  have h : PolyT fun p : Arg × ℕ => tOf p.1.2.2.1.length := (t_unary.comp PolyT.id'.fst).poly
  exact prodL_polyT' t_unary (topAt_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (unary_min_right PolyT.id'.snd (t_unary.comp PolyT.id'.fst)))

/-- The second function of the factorization with θ = (Q, θ') is polynomial-time. -/
theorem botLong_polyT : PolyT fun q : Arg =>
    prodL (tOf q.2.2.1.length) (botAt q.1 (q.2.2.2.2.take (tOf q.2.2.1.length)) (q.2.2.2.2.drop (tOf q.2.2.1.length)) q.2.2.1 q.2.2.2.1) := by
  have h : PolyT fun p : Arg × ℕ => tOf p.1.2.2.1.length := (t_unary.comp PolyT.id'.fst).poly
  exact prodL_polyT' t_unary (botAt_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (unary_min_right PolyT.id'.snd (t_unary.comp PolyT.id'.fst)))

/-- The first function of a factorization is polynomial-time. -/
theorem fTop_polyT : PolyT fTop := by
  unfold fTop
  exact PolyT.ite' (PolyT.decide_eq (useLong_polyT PolyT.id'.fst lam_unary PolyT.id'.snd.fst) (PolyT.const true))
    (PolyT.ite' card_polyT topLong_polyT (PolyT.const 0)) (PolyT.ite' (by fun_prop) (PolyT.const 1) (PolyT.const 0))

/-- The second function of a factorization is polynomial-time. -/
theorem fBot_polyT : PolyT fBot := by
  have hl := lam_unary.poly
  unfold fBot
  exact PolyT.ite' (PolyT.decide_eq (useLong_polyT PolyT.id'.fst lam_unary PolyT.id'.snd.fst) (PolyT.const true))
    (PolyT.ite' card_polyT botLong_polyT (PolyT.const 0))
    (PolyT.cond' PolyT.id'.fst
      (PolyT.comp (g := fun q : Arg => (q.2.1, q.2.2.2.2.take q.2.2.1.length, q.2.2.1, q.2.2.2.2.drop q.2.2.1.length, q.2.2.2.1)) aMul_polyT (by fun_prop))
      (PolyT.comp (g := fun q : Arg => (q.2.1, q.2.2.2.2.take q.2.2.1.length, q.2.2.2.2.drop q.2.2.1.length, q.2.2.1, q.2.2.2.1)) aMul_polyT (by fun_prop)))

/-! ### The numbers of bits -/

/-- c_i^row = min{2λ, 4t + 3i} is given in unary, for λ in unary; i may be in binary. -/
theorem crow_unary {lam i : α → ℕ} (hl : Unary lam) (hi : PolyT i) : Unary fun x => crow (lam x) (i x) := by
  have h1 := hl.poly
  have h2 := (tOf_unary hl).poly
  exact Unary.of_le (g := fun x => 2 * lam x) (by fun_prop) (by unfold crow; exact PolyT.min' (by fun_prop) (by fun_prop)) fun x => min_le_left _ _

/-- c_i^col = min{2λ, 7t − 3i} is given in unary, for λ in unary; i may be in binary. -/
theorem ccol_unary {lam i : α → ℕ} (hl : Unary lam) (hi : PolyT i) : Unary fun x => ccol (lam x) (i x) := by
  have h1 := hl.poly
  have h2 := (tOf_unary hl).poly
  exact Unary.of_le (g := fun x => 2 * lam x) (by fun_prop) (by unfold ccol; exact PolyT.min' (by fun_prop) (by fun_prop)) fun x => min_le_left _ _

end SecCrossing_Cert

open SecCrossing_Cert

/-- **Lemma 2 of the paper**, «computable in time poly(λ)», said there of A_i in (a) and of the
functions of both factorizations in (b): the program `aMul` is one polynomial-time function of (i in
binary, the four strings as
lists of bits), and `fTop` and `fBot` are polynomial-time functions of (direction, i in binary, two
strings and θ as lists of bits). Same as in the paper, with «time poly(λ)» read as: polynomial in
the length of the input, on a
multi-stack machine of Mathlib; for i ≤ t and θ of at most 2λ bits that is polynomial in λ. -/
theorem stPoly : StPoly := ⟨aMul_polyT, fTop_polyT, fBot_polyT⟩

/-- All parts of the family `eightF` are computed in polynomial time: the number t + 1 of pieces,
the numbers of bits c_i^row and c_i^col and the bound t on the sizes in unary, the factor 2^t in
binary, and the two functions of
the factorizations. The paper has no sentence on the numbers; for the functions see Lemma 2 (b) of
the paper and `fTop_polyT`, `fBot_polyT` above. -/
theorem stKeeps : StKeeps where
  cnt := by
    change Unary fun p : U × U => tOf p.2.length + 1
    exact (tOf_unary (by fun_prop)).add (Unary.const 1)
  d := by
    change PolyT fun p : U × U => 2 ^ tOf p.2.length
    exact pow_polyT (PolyT.const 2) (tOf_unary (by fun_prop))
  cap := by
    have h1 : Unary fun p : Bool × U × U × ℕ => ccol p.2.2.1.length p.2.2.2 := ccol_unary (by fun_prop) (by fun_prop)
    have h2 : Unary fun p : Bool × U × U × ℕ => crow p.2.2.1.length p.2.2.2 := crow_unary (by fun_prop) (by fun_prop)
    exact (PolyT.cond' (by fun_prop : PolyT fun p : Bool × U × U × ℕ => p.1) h1 h2).congr fun p => by
      rcases p with ⟨_ | _, _⟩ <;> rfl
  top := PolyT.comp (g := fun q : PQ => (q.1.2, q.2.1.2, q.2.2.1, q.2.2.2.1, q.2.2.2.2)) fTop_polyT (by fun_prop)
  bot := PolyT.comp (g := fun q : PQ => (q.1.2, q.2.1.2, q.2.2.1, q.2.2.2.1, q.2.2.2.2)) fBot_polyT (by fun_prop)
  need := by change Unary fun _ : U × U => 0; fun_prop
  bits := by
    change Unary fun p : U × U => tOf p.2.length
    exact tOf_unary (by fun_prop)

end Eight
