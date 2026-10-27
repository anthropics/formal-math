/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Interfaces
public import PaddedDescent.F.FuelCert
public import ToTuring.Poly.Digits

/-! # Certificates: one level and all levels

Polynomial time (`PolyT`) in the pad and the data, for any pieces with certificates, of

* `expandG`, one level on a p × d grid (`stCertExpandG`), from the certificates of the network of a
  term, of the label length one level down, of the evaluation by enumeration and
  of the rebalancing;
* `solveG`, all levels, brute force at the bottom and the final division (`stCertSolveG`), from the
  certificates of one level, of the label length and of brute force;
* `needC`, the exponent of a pad that suffices, computed under a bound (`stCertNeedC`), from the
  certificate of the label length.

All numbers of a step are given in unary, and so is the label length. The state of the loop of
`needC` holds the current number of nodes in binary, while the length of the word of
an instance has that number in an exponent. The numbers of nodes that occur are those of the steps
and the first one, so their sum M is given in unary; the certificate is proved
for the loop in which the number of nodes in the state is cut off at M (`needCut`), and the cut-off
changes nothing (`needCut_eq`). -/

public section

namespace ClauseBound.Alg.CertLevel

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F

variable {α : Type} [Enc α] {P : PiecesF}

/-! ### Division of an integer by a natural number -/

/-- The quotient, rounded down, in terms of quotients of natural numbers. -/
theorem ediv_natCast (a : ℤ) (b : ℕ) :
    a / (b : ℤ) = if 0 ≤ a then ((a.toNat / b : ℕ) : ℤ) else if b = 0 then 0 else -(((a.natAbs - 1) / b + 1 : ℕ) : ℤ) := by
  cases a with
  | ofNat n => simp
  | negSucc m =>
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have h0 : ¬ (0 : ℤ) ≤ Int.negSucc m := by simp
      rw [if_neg h0, if_neg (by omega), Int.negSucc_ediv m (by exact_mod_cast hb)]
      simp
      rfl

/-- Division of an integer by a natural number is polynomial-time. -/
theorem divZ_polyT {a : α → ℤ} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) : PolyT fun x => a x / (b x : ℤ) := by
  have h1 : PolyT fun x => (a x).toNat / b x := PolyT.div (by fun_prop) hb
  have h2 : PolyT fun x => ((a x).natAbs - 1) / b x := PolyT.div (by fun_prop) hb
  have key : ∀ q r : α → ℕ, PolyT q → PolyT r →
      PolyT fun x => if 0 ≤ a x then ((q x : ℕ) : ℤ) else if b x = 0 then 0 else -((r x + 1 : ℕ) : ℤ) := by
    intro q r hq hr
    fun_prop
  exact (key _ _ h1 h2).congr fun x => (ediv_natCast _ _).symm

/-! ### The numbers of a step -/

/-- The numbers of a step are given in unary. -/
theorem K_unary {s : α → Step} (hs : PolyT s) : Unary fun x => (s x).K := by unfold Step.K; fun_prop
theorem p_unary {s : α → Step} (hs : PolyT s) : Unary fun x => (s x).p := by unfold Step.p; fun_prop
theorem d_unary {s : α → Step} (hs : PolyT s) : Unary fun x => (s x).d := by unfold Step.d; fun_prop
theorem h_unary {s : α → Step} (hs : PolyT s) : Unary fun x => (s x).h := by unfold Step.h; fun_prop
theorem a_unary {s : α → Step} (hs : PolyT s) : Unary fun x => (s x).a := by unfold Step.a; fun_prop
theorem b_unary {s : α → Step} (hs : PolyT s) : Unary fun x => (s x).b := by unfold Step.b; fun_prop
theorem thin_polyT {s : α → Step} (hs : PolyT s) : PolyT fun x => (s x).thin := by unfold Step.thin; fun_prop

/-- The number of pairs is given in unary. -/
theorem c2_unary {g : α → ℕ} (hg : Unary g) : Unary fun x => c2 (g x) := by
  have := hg.poly
  unfold c2; fun_prop

/-- The number of rectangles of a step is given in unary. -/
theorem nRectG_unary {s : α → Step} (hs : PolyT s) : Unary fun x => nRectG (s x).p (s x).d :=
  (c2_unary (p_unary hs)).mul (c2_unary (d_unary hs))

/-! ### The numbers of the pieces -/

section
variable (hP : P.Keeps)
include hP

/-- The number of pieces is given in unary. -/
theorem cnt_unary {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) : Unary fun x => P.cnt (s x).h (l x).length :=
  hP.cnt.comp (h := fun x => ((s x).2.1.2, l x)) (by fun_prop)

/-- The factor d of the pieces. -/
theorem d_polyT {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) : PolyT fun x => P.d (s x).h (l x).length :=
  PolyT.comp (g := fun x => ((s x).2.1.2, l x)) hP.d (by fun_prop)

/-- The number of bits through which a piece factors is given in unary. -/
theorem cap_unary {tr : α → Bool} {s : α → Step} {l : α → U} {i : α → ℕ} (ht : PolyT tr) (hs : PolyT s) (hl : PolyT l) (hi : PolyT i) :
    Unary fun x => P.cap (tr x) (s x).h (l x).length (i x) :=
  hP.cap.comp (h := fun x => (tr x, (s x).2.1.2, l x, i x)) (by fun_prop)

/-- The factor d^R of a step. -/
theorem dpow_polyT {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) :
    PolyT fun x => P.d (s x).h (l x).length ^ nRectG (s x).p (s x).d :=
  PolyT.pow_unary (d_polyT hP hs hl) (nRectG_unary hs)

/-- The number of patterns. -/
theorem nPat_polyT {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) : PolyT fun x => nPat P (s x) (l x).length :=
  PolyT.pow_unary (cnt_unary hP hs hl).poly (nRectG_unary hs)

/-- A digit of a pattern. -/
theorem dig_polyT {s : α → Step} {l : α → U} {y q : α → ℕ} (hs : PolyT s) (hl : PolyT l) (hy : PolyT y) (hq : PolyT q) :
    PolyT fun x => digit (P.cnt (s x).h (l x).length - 1) (y x) (q x) := by
  have := (cnt_unary hP hs hl).poly
  fun_prop

/-- The sum of the digits of a pattern. -/
theorem sumDig_polyT {s : α → Step} {l : α → U} {y : α → ℕ} (hs : PolyT s) (hl : PolyT l) (hy : PolyT y) :
    PolyT fun x => sumDig P (s x) (l x).length (y x) := by
  have h1 : PolyT fun q : α × ℕ => digit (P.cnt (s q.1).h (l q.1).length - 1) (y q.1) q.2 :=
    dig_polyT hP (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have h2 : PolyT fun x => (List.range (nRectG (s x).p (s x).d)).map fun q => digit (P.cnt (s x).h (l x).length - 1) (y x) q :=
    PolyT.map (f := fun x q => digit (P.cnt (s x).h (l x).length - 1) (y x) q) h1 (PolyT.range (nRectG_unary hs))
  refine h2.sum.congr fun x => ?_
  simp only [sumDig, sum_range_eq_list]

/-- What the rectangles cost. -/
theorem priceG_polyT {tr : α → Bool} {s : α → Step} {l : α → U} {y : α → ℕ} (ht : PolyT tr) (hs : PolyT s) (hl : PolyT l) (hy : PolyT y) :
    PolyT fun x => priceG P (s x).p (s x).d (tr x) (s x).h (l x).length (y x) := by
  have h1 : PolyT fun q : α × ℕ => P.cap (tr q.1) (s q.1).h (l q.1).length (digit (P.cnt (s q.1).h (l q.1).length - 1) (y q.1) q.2) :=
    (cap_unary hP (by fun_prop) (by fun_prop) (by fun_prop)
      (dig_polyT hP (s := fun q : α × ℕ => s q.1) (l := fun q => l q.1) (y := fun q => y q.1) (q := fun q => q.2)
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))).poly
  have h2 : PolyT fun x => (List.range (nRectG (s x).p (s x).d)).map fun q =>
      P.cap (tr x) (s x).h (l x).length (digit (P.cnt (s x).h (l x).length - 1) (y x) q) :=
    PolyT.map (f := fun x q => P.cap (tr x) (s x).h (l x).length (digit (P.cnt (s x).h (l x).length - 1) (y x) q)) h1
      (PolyT.range (nRectG_unary hs))
  refine ((PolyT.const 2).mul h2.sum).congr fun x => ?_
  simp only [priceG, sum_range_eq_list]

/-- The total U of the network of a pattern. -/
theorem totalG_polyT {tr : α → Bool} {s : α → Step} {l : α → U} {y : α → ℕ} (ht : PolyT tr) (hs : PolyT s) (hl : PolyT l) (hy : PolyT y) :
    PolyT fun x => totalG P (s x).p (s x).d (tr x) (s x).h (l x).length (y x) := by
  have h1 := priceG_polyT hP ht hs hl hy
  have h2 := (p_unary hs).poly
  have h3 := (d_unary hs).poly
  have key : ∀ p d n r : α → ℕ, PolyT p → PolyT d → PolyT n → PolyT r →
      PolyT fun x => (if tr x = true then d x else p x) * ((if tr x = true then d x else p x) - 1) * (if tr x = true then p x else d x) * n x + r x := by
    intro p d n r _ _ _ _
    fun_prop
  exact key _ _ _ _ h2 h3 (by fun_prop) h1

/-- The choice of the side. -/
theorem colSide_polyT {s : α → Step} {l : α → U} {y : α → ℕ} (hs : PolyT s) (hl : PolyT l) (hy : PolyT y) :
    PolyT fun x => colSide P (s x) (l x).length (y x) := by
  have h1 := sumDig_polyT hP hs hl hy
  have h2 := totalG_polyT hP (tr := fun _ => true) (by fun_prop) hs hl hy
  have h3 := totalG_polyT hP (tr := fun _ => false) (by fun_prop) hs hl hy
  have h4 := (nRectG_unary hs).poly
  have h5 := (a_unary hs).poly
  have h6 := (b_unary hs).poly
  have h7 := thin_polyT hs
  have h8 : PolyT fun x => Pieces.nblk (l x).length (s x).h := by
    have := (h_unary hs).poly
    unfold Pieces.nblk
    exact PolyT.div (by fun_prop) (by fun_prop)
  have key : ∀ (t : α → Bool) (a b c e f g u : α → ℕ), PolyT t → PolyT a → PolyT b → PolyT c → PolyT e → PolyT f → PolyT g → PolyT u →
      PolyT fun x => if t x = true then decide (a x ^ 2 * b x ≤ c x * (e x * f x) ^ 2) else decide (g x < u x) := by
    intro t a b c e f g u _ _ _ _ _ _ _ _
    fun_prop
  exact key _ _ _ _ _ _ _ _ h7 h1 h5 h6 h4 h8 h2 h3

end

/-! ### One level -/

/-- The context of the network of a pattern. -/
theorem gctx_polyT {pad : α → U} {s : α → Step} {tr : α → Bool} {I : α → PInst} {y : α → ℕ} (hp : PolyT pad) (hs : PolyT s) (ht : PolyT tr)
    (hI : PolyT I) (hy : PolyT y) : PolyT fun x => gctx (pad x) (s x) (tr x) (I x) (y x) := by
  unfold gctx; fun_prop

section
variable (hP : P.Keeps)
include hP

/-- Is the term of a pattern evaluated at once? -/
theorem atOnce_polyT {s : α → Step} {l : α → U} {y : α → ℕ} (hs : PolyT s) (hl : PolyT l) (hy : PolyT y) :
    PolyT fun x => ((s x).thin && colSide P (s x) (l x).length (y x)) :=
  PolyT.and' (thin_polyT hs) (colSide_polyT hP hs hl hy)

/-- The label length one level down is given in unary. -/
theorem lamNextG_unary (hL : StCertLam P) {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) :
    Unary fun x => lamNextG P (s x) (l x).length :=
  (hL hP).comp (h := fun x => (s x, l x)) (by fun_prop)

/-- The child of one pattern. -/
theorem childG_polyT (hG : StCertGrid P) (hL : StCertLam P) (hR : StCertRebalG) {pad : α → U} {s : α → Step} {I : α → PInst} {y : α → ℕ}
    (hp : PolyT pad) (hs : PolyT s) (hI : PolyT I) (hy : PolyT y) : PolyT fun x => childG P (pad x) (s x) (I x) (y x) :=
  hR GridCtx (gridF P) (hG hP) α pad (fun x => (s x).K) (fun x => (s x).p) (fun x => lamNextG P (s x) (I x).1.length)
    (fun x => gctx (pad x) (s x) (!(s x).thin && colSide P (s x) (I x).1.length (y x)) (I x) (y x)) hp (K_unary hs) (p_unary hs)
    (lamNextG_unary hP hL hs (by fun_prop))
    (gctx_polyT hp hs (PolyT.and' (PolyT.not' (thin_polyT hs)) (colSide_polyT hP hs (by fun_prop) hy)) hI hy)

/-- One level. -/
theorem expandG_polyT (hG : StCertGrid P) (hL : StCertLam P) (hE : StCertEnum) (hR : StCertRebalG) {pad : α → U} {s : α → Step} {I : α → PInst}
    (hp : PolyT pad) (hs : PolyT s) (hI : PolyT I) : PolyT fun x => expandG P (pad x) (s x) (I x) := by
  have hn : PolyT fun x => nPat P (s x) (I x).1.length := nPat_polyT hP hs (by fun_prop)
  have ha : PolyT fun q : α × ℕ => ((s q.1).thin && colSide P (s q.1) (I q.1).1.length q.2) :=
    atOnce_polyT hP (by fun_prop) (by fun_prop) (by fun_prop)
  have he : PolyT fun q : α × ℕ => enumF (pad q.1) (s q.1).d (gridF P) (gctx (pad q.1) (s q.1) true (I q.1) q.2) :=
    hE GridCtx (gridF P) (hG hP) (α × ℕ) (fun q => pad q.1) (fun q => (s q.1).d) (fun q => gctx (pad q.1) (s q.1) true (I q.1) q.2)
      (by fun_prop) (d_unary (by fun_prop)) (gctx_polyT (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
  have hc : PolyT fun q : α × ℕ => childG P (pad q.1) (s q.1) (I q.1) q.2 :=
    childG_polyT hP hG hL hR (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have h1 : PolyT fun x => sumF (nPat P (s x) (I x).1.length) (pad x) fun y =>
      if ((s x).thin && colSide P (s x) (I x).1.length y) = true then enumF (pad x) (s x).d (gridF P) (gctx (pad x) (s x) true (I x) y) else 0 :=
    sumF_polyT hn hp (PolyT.ite' (PolyT.decide_eq_true ha) he (by fun_prop))
  have h2 : PolyT fun x => (rng (pad x) (nPat P (s x) (I x).1.length)).filterMap fun y =>
      if ((s x).thin && colSide P (s x) (I x).1.length y) = true then none else childG P (pad x) (s x) (I x) y :=
    PolyT.filterMap (f := fun x y => if ((s x).thin && colSide P (s x) (I x).1.length y) = true then none else childG P (pad x) (s x) (I x) y)
      (PolyT.ite' (PolyT.decide_eq_true ha) (by fun_prop) hc) (rng_polyT hp hn)
  exact h1.prodMk h2

end

/-- One level is polynomial-time in the pad, the step and the instance. -/
theorem stCertExpandG (P : PiecesF) (hG : StCertGrid P) (hL : StCertLam P) (hE : StCertEnum) (hR : StCertRebalG) : StCertExpandG P :=
  fun hP => expandG_polyT hP hG hL hE hR (by fun_prop) (by fun_prop) (by fun_prop)

/-! ### All levels -/

/-- One round of the descent. -/
theorem stepG_polyT (hP : P.Keeps) (hL : StCertLam P) (hX : StCertExpandG P) {pad : α → U} {st : α → DState} {s : α → Step} (hp : PolyT pad)
    (hst : PolyT st) (hs : PolyT s) : PolyT fun x => stepG P (pad x) (st x) (s x) := by
  have hd : PolyT fun x => P.d (s x).h (st x).2.1.length ^ nRectG (s x).p (s x).d := dpow_polyT hP hs (by fun_prop)
  have hl : PolyT fun x => List.replicate (lamNextG P (s x) (st x).2.1.length) () := lamNextG_unary hP hL hs (by fun_prop)
  have he : PolyT fun q : α × PInst => expandG P (pad q.1) (s q.1) q.2 :=
    PolyT.comp (g := fun q : α × PInst => (pad q.1, s q.1, q.2)) (hX hP) (by fun_prop)
  have hm : PolyT fun x => (st x).2.2.map (expandG P (pad x) (s x)) :=
    PolyT.map (f := fun x J => expandG P (pad x) (s x) J) he (by fun_prop)
  have key : ∀ (D : α → ℕ) (l : α → U) (m : α → List (ℤ × List PInst)), PolyT D → PolyT l → PolyT m →
      PolyT fun x => ((((st x).1.1 * (D x : ℕ) + ((m x).map Prod.fst).sum, (st x).1.2 * D x), l x, (m x).flatMap Prod.snd) : DState) := by
    intro D l m _ _ _
    fun_prop
  exact key _ _ _ hd hl hm

/-- The descent through all levels. -/
theorem descendG_polyT (hP : P.Keeps) (hL : StCertLam P) (hX : StCertExpandG P) {pad : α → U} {sched : α → List Step} {I : α → PInst}
    (hp : PolyT pad) (hs : PolyT sched) (hI : PolyT I) : PolyT fun x => descendG P (pad x) (sched x) (I x) :=
  foldl_cap (pad := pad) (l := sched) (a := fun x => (((0, 1), (I x).1, [I x]) : DState)) (g := fun x st s => stepG P (pad x) st s)
    ((0, 1), [], []) hp hs (by fun_prop) (stepG_polyT hP hL hX (by fun_prop) (by fun_prop) (by fun_prop))

/-- All levels, brute force at the bottom and the division are polynomial-time in the pad, K₀ in
unary, the schedule and the instance. -/
theorem stCertSolveG (P : PiecesF) (hL : StCertLam P) (hX : StCertExpandG P) (hB : StCertBruteK) : StCertSolveG P := by
  intro hP
  have hD : PolyT fun p : U × U × List Step × PInst => descendG P p.1 p.2.2.1 p.2.2.2 :=
    descendG_polyT hP hL hX (by fun_prop) (by fun_prop) (by fun_prop)
  have hb : PolyT fun q : (U × U × List Step × PInst) × PInst => bruteF q.1.1 q.1.2.1.length q.2 :=
    PolyT.comp (g := fun q : (U × U × List Step × PInst) × PInst => (q.1.1, q.1.2.1, q.2)) hB (by fun_prop)
  have hm : PolyT fun p : U × U × List Step × PInst => (descendG P p.1 p.2.2.1 p.2.2.2).2.2.map (bruteF p.1 p.2.1.length) :=
    PolyT.map (f := fun (p : U × U × List Step × PInst) J => bruteF p.1 p.2.1.length J) hb (by fun_prop)
  exact divZ_polyT (PolyT.addZ (by fun_prop) (sumZ_polyT hm)) (by fun_prop)

/-! ### The square root of a number given in unary -/

/-- Among 0, …, N − 1 there are min N (k + 1) numbers that are at most k. -/
theorem countP_le_range (k N : ℕ) : (List.range N).countP (fun r => decide (r ≤ k)) = min N (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.countP_append, ih, List.countP_singleton]
    by_cases h : N ≤ k
    · simp only [h, decide_true, if_true]; omega
    · simp only [h, decide_false]; simp; omega

/-- The square root, rounded down, by counting. -/
theorem sqrt_eq_countP (n : ℕ) : Nat.sqrt n = (List.range (n + 1)).countP (fun r => decide (r * r ≤ n)) - 1 := by
  have h : (fun r => decide (r * r ≤ n)) = fun r => decide (r ≤ Nat.sqrt n) := by
    funext r
    exact decide_eq_decide.2 Nat.le_sqrt.symm
  have h2 := Nat.sqrt_le_self n
  rw [h, countP_le_range]
  omega

/-- The square root of a number given in unary is polynomial-time. -/
theorem sqrt_polyT {n : α → ℕ} (hn : Unary n) : PolyT fun x => Nat.sqrt (n x) := by
  have hp := hn.poly
  have h : PolyT fun x => (List.range (n x + 1)).countP (fun r => decide (r * r ≤ n x)) - 1 := by fun_prop
  exact h.congr fun x => (sqrt_eq_countP _).symm

/-! ### The numbers in the exponent -/

/-- The bound for the column networks that are evaluated by enumeration. -/
theorem ebarG_polyT {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) : PolyT fun x => ebarG (s x) (l x).length := by
  have hR := nRectG_unary hs
  have hb := b_unary hs
  have hh := h_unary hs
  have ha := (a_unary hs).poly
  have h1 : PolyT fun x => Nat.sqrt ((s x).b * (nRectG (s x).p (s x).d * ((l x).length + (s x).h)) ^ 2 / (s x).a) :=
    sqrt_polyT (unary_div (by fun_prop) ha)
  have h2 := (c2_unary (d_unary hs)).poly
  have h3 := (p_unary hs).poly
  have h4 := hR.poly
  have key : ∀ a b c e : α → ℕ, PolyT a → PolyT b → PolyT c → PolyT e → PolyT fun x => a x * b x * (l x).length + c x + 8 * (e x + 1) := by
    intro a b c e _ _ _ _
    fun_prop
  exact key _ _ _ _ h2 h3 h4 h1

/-- The length of the word of an instance, for K and the label length in unary. -/
theorem instLen_polyT {K lam B : α → ℕ} (hK : Unary K) (hl : Unary lam) (hB : PolyT B) : PolyT fun x => instLen (K x) (lam x) (B x) := by
  have h1 := hK.poly
  have h2 := hl.poly
  have h3 : PolyT fun x => 2 ^ ((K x - 1) * lam x) := PolyT.pow_unary (by fun_prop) (by fun_prop)
  have key : ∀ e : α → ℕ, PolyT e → PolyT fun x => 4 * lam x + K x * (e x * (3 * B x + 10) + 4) + 10 := by
    intro e _
    fun_prop
  exact key _ h3

/-- P of the networks that are rebalanced. -/
theorem PnG_polyT {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) : PolyT fun x => PnG P (s x) (l x).length := by
  have h1 := (p_unary hs).poly
  have h2 := (d_unary hs).poly
  have key : ∀ p d : α → ℕ, PolyT p → PolyT d → PolyT fun x => P.m * (p x * d x ^ 2 * (l x).length) := by
    intro p d _ _
    fun_prop
  exact key _ _ h1 h2

/-- 2p/K. -/
theorem quo_polyT {s : α → Step} (hs : PolyT s) : PolyT fun x => 2 * (s x).p / (s x).K :=
  PolyT.div ((PolyT.const 2).mul (p_unary hs).poly) (K_unary hs).poly

/-- The bound for the number of bits of the values of the pieces. -/
theorem bits_polyT (hP : P.Keeps) {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) : PolyT fun x => P.bits (s x).h (l x).length :=
  (hP.bits.comp (h := fun x => ((s x).2.1.2, l x)) (by fun_prop)).poly

/-- The exponent that the loops inside the pieces need. -/
theorem need_polyT (hP : P.Keeps) {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) : PolyT fun x => P.need (s x).h (l x).length :=
  (hP.need.comp (h := fun x => ((s x).2.1.2, l x)) (by fun_prop)).poly

/-- The bound for the bit length of the entries one level down. -/
theorem bNextG_polyT (hP : P.Keeps) {s : α → Step} {l : α → U} {B : α → ℕ} (hs : PolyT s) (hl : PolyT l) (hB : PolyT B) :
    PolyT fun x => bNextG P (s x) (l x).length (B x) := by
  have h1 := PnG_polyT (P := P) hs hl
  have h2 := quo_polyT hs
  have h3 := (d_unary hs).poly
  have h4 := bits_polyT hP hs hl
  have h5 := (K_unary hs).poly
  have key : ∀ n q d b K : α → ℕ, PolyT n → PolyT q → PolyT d → PolyT b → PolyT K →
      PolyT fun x => n x * q x + (d x * B x + d x ^ 2 * b x) * (q x + q x * q x) * K x := by
    intro n q d b K _ _ _ _ _
    fun_prop
  exact key _ _ _ _ _ h1 h2 h3 h4 h5

/-- N = (pd)²λ. -/
theorem Nof_polyT {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) : PolyT fun x => Nof (s x) (l x).length := by
  have h1 := (p_unary hs).poly
  have h2 := (d_unary hs).poly
  have key : ∀ p d : α → ℕ, PolyT p → PolyT d → PolyT fun x => (p x * d x) ^ 2 * (l x).length := by
    intro p d _ _
    fun_prop
  exact key _ _ h1 h2

/-! ### The exponent, computed under a bound -/

/-- The bound for the number of bits of the sum and the factor. -/
theorem zNext_polyT {cnt z B nP nR dP nof d p bits : α → ℕ} (h1 : PolyT cnt) (h2 : PolyT z) (h3 : PolyT B) (h4 : PolyT nP) (h5 : PolyT nR) (h6 : PolyT dP)
    (h7 : PolyT nof) (h8 : PolyT d) (h9 : PolyT p) (h10 : PolyT bits) :
    PolyT fun x => z x + nR x * Nat.size (dP x) + Nat.size (cnt x * nP x) + nof x + d x ^ 2 * (p x * B x + p x ^ 2 * bits x + 1) + 2 :=
  ((((h2.add (h5.mul (PolyT.size' h6))).add (PolyT.size' (h1.mul h4))).add h7).add
    ((PolyT.pow_const h8 2).mul (((h9.mul h3).add ((PolyT.pow_const h9 2).mul h10)).add (PolyT.const 1)))).add (PolyT.const 2)

/-- The exponent for the state of the descent. -/
theorem needState_polyT {cnt z B lam Kst inst : α → ℕ} (h1 : PolyT cnt) (h2 : PolyT z) (h3 : PolyT B) (h4 : PolyT lam) (h5 : PolyT Kst) (h6 : PolyT inst) :
    PolyT fun x => max (Nat.size (cnt x * inst x + 8 * z x + 4 * lam x + 40)) (max (lam x) (max (Nat.size (B x)) (Nat.size (Kst x)))) := by
  fun_prop

/-- The exponents for the loops of one step. -/
theorem needLoops_polyT {need nP p K Pn quo LN eb d lam : α → ℕ} {thin : α → Bool} (h1 : PolyT need) (h2 : PolyT nP) (h3 : PolyT p) (h4 : PolyT K) (h5 : PolyT Pn)
    (h6 : PolyT quo) (h7 : PolyT LN) (h8 : PolyT eb) (h9 : PolyT d) (h10 : PolyT lam) (h11 : PolyT thin) :
    PolyT fun x => max (max (max (need x) (Nat.size (nP x))) (max (p x * Nat.size (K x)) (Pn x * (quo x + 1))))
      (max ((K x - 1) * LN x) (if thin x = true then max (eb x) (p x ^ 2 * d x * lam x) else 0)) := by
  fun_prop

/-- One step of the computation of the exponent, if the number of nodes in the state is given in
unary. -/
theorem needStep_polyT (hP : P.Keeps) (hL : StCertLam P) {st : α → NState} {s : α → Step} (hst : PolyT st) (hs : PolyT s)
    (hK : Unary fun x => (st x).2.2.1) : PolyT fun x => needStep P (st x) (s x) := by
  have hl : PolyT fun x => (st x).1.1 := by fun_prop
  have a1 := lamNextG_unary hP hL hs hl
  have a2 := bNextG_polyT hP (B := fun x => (st x).1.2) hs hl (by fun_prop)
  have a3 := nPat_polyT hP hs hl
  have a4 := (nRectG_unary hs).poly
  have a5 := d_polyT hP hs hl
  have a6 := Nof_polyT hs hl
  have a7 := (d_unary hs).poly
  have a8 := (p_unary hs).poly
  have a9 := bits_polyT hP hs hl
  have a10 := (K_unary hs).poly
  have a11 := instLen_polyT (B := fun x => (st x).1.2) hK (Unary.of_length hl) (by fun_prop)
  have a12 := need_polyT hP hs hl
  have a13 := PnG_polyT (P := P) hs hl
  have a14 := quo_polyT hs
  have a15 := ebarG_polyT hs hl
  have a16 := thin_polyT hs
  have b1 : PolyT fun x => (st x).2.1.1 := by fun_prop
  have b2 : PolyT fun x => (st x).2.1.2 := by fun_prop
  have b3 : PolyT fun x => (st x).1.2 := by fun_prop
  have b4 : PolyT fun x => (st x).1.1.length := by fun_prop
  have b5 : PolyT fun x => (st x).2.2.2 := by fun_prop
  exact (PolyT.prodMk a1 a2).prodMk ((PolyT.prodMk (b1.mul a3) (zNext_polyT b1 b2 b3 a3 a4 a5 a6 a7 a8 a9)).prodMk
    (PolyT.prodMk a10 (PolyT.max' b5 (PolyT.max' (needState_polyT b1 b2 b3 b4 hK.poly a11) (needLoops_polyT a12 a3 a8 a10 a13 a14 a1.poly a15 a7 b4 a16)))))

/-- The end of that computation, if the number of nodes in the state is given in unary. -/
theorem needFin_polyT {st : α → NState} (hst : PolyT st) (hK : Unary fun x => (st x).2.2.1) : PolyT fun x => needFin (st x) := by
  have hl : PolyT fun x => (st x).1.1 := by fun_prop
  have a1 := instLen_polyT (B := fun x => (st x).1.2) hK (Unary.of_length hl) (by fun_prop)
  have a2 : PolyT fun x => (st x).2.2.1 * ((st x).2.2.1 - 1) / 2 := PolyT.div (by fun_prop) (by fun_prop)
  have b4 : PolyT fun x => (st x).1.1.length := by fun_prop
  exact PolyT.max' (by fun_prop) (PolyT.max' (needState_polyT (by fun_prop) (by fun_prop) (by fun_prop) b4 hK.poly a1) (a2.mul b4))

/-- The length of the word of an optional value can be computed in polynomial time. -/
theorem measOption {γ : Type} [Enc γ] [Meas γ] : Meas (Option γ) := ⟨by
  have h1 := Meas.poly (α := γ)
  have : PolyT fun o : Option γ => o.elim 2 fun a => len a + 4 := by fun_prop
  exact this.congr fun o => by cases o <;> simp [len_none, len_some]⟩

/-- The state with the number of nodes cut off at M. -/
def clip (M : ℕ) (st : NState) : NState := (st.1, st.2.1, (min st.2.2.1 M, st.2.2.2))

/-- A state whose number of nodes is at most M is not changed. -/
theorem clip_eq {M : ℕ} {st : NState} (h : st.2.2.1 ≤ M) : clip M st = st := by
  unfold clip
  rw [min_eq_left h]

/-- If no number of nodes exceeds M, the cut-off changes nothing in a loop that writes the number of
nodes of the step into the state, and the number of nodes in the result is
at most M. -/
theorem fold_clip (f : NState → Step → NState) (hf : ∀ st s, (f st s).2.2.1 = s.K) (c : U) (M : ℕ) :
    ∀ (l : List Step) (o : Option NState), (∀ s ∈ l, s.K ≤ M) → (∀ st, o = some st → st.2.2.1 ≤ M) →
      l.foldl (fun o s => cap c none (o.map fun st => f (clip M st) s)) o = l.foldl (fun o s => cap c none (o.map fun st => f st s)) o ∧
        ∀ st, l.foldl (fun o s => cap c none (o.map fun st => f st s)) o = some st → st.2.2.1 ≤ M := by
  intro l
  induction l with
  | nil => intro o _ ho; exact ⟨rfl, ho⟩
  | cons s l ih =>
    intro o hl ho
    have h1 : (o.map fun st => f (clip M st) s) = o.map fun st => f st s := by
      cases o with
      | none => rfl
      | some st => rw [Option.map_some, Option.map_some, clip_eq (ho st rfl)]
    have h2 : ∀ st, cap c none (o.map fun st => f st s) = some st → st.2.2.1 ≤ M := by
      intro st hst
      unfold cap at hst
      split_ifs at hst
      · obtain ⟨st', -, rfl⟩ := Option.map_eq_some_iff.1 hst
        rw [hf]
        exact hl s (by simp)
    rw [List.foldl_cons, List.foldl_cons, h1]
    exact ih _ (fun s' hs' => hl s' (by simp [hs'])) h2

/-- The computation of the exponent under a bound, with the numbers of nodes cut off at M. -/
def needCut (P : PiecesF) (M : ℕ) (b : U) (Kup lam B : ℕ) (sched : List Step) : Option ℕ :=
  (sched.foldl (fun o s => cap (List.replicate (100 * (b.length + 2)) ()) none (o.map fun st => needStep P (clip M st) s))
    (cap (List.replicate (100 * (b.length + 2)) ()) none (some ((List.replicate lam (), B), (1, 1), (Kup, 0))))).bind fun st =>
      if needFin (clip M st) ≤ b.length then some (needFin (clip M st)) else none

/-- With M the sum of all numbers of nodes, the cut-off changes nothing. -/
theorem needCut_eq (P : PiecesF) (b : U) (Kup lam B : ℕ) (sched : List Step) :
    needCut P (Kup + (sched.map Step.K).sum) b Kup lam B sched = needC P b Kup lam B sched := by
  have h0 : ∀ st, cap (List.replicate (100 * (b.length + 2)) ()) (none : Option NState) (some ((List.replicate lam (), B), (1, 1), (Kup, 0))) = some st →
      st.2.2.1 ≤ Kup + (sched.map Step.K).sum := by
    intro st hst
    unfold cap at hst
    split_ifs at hst
    · cases hst
      exact Nat.le_add_right _ _
  obtain ⟨h1, h2⟩ := fold_clip (needStep P) (fun _ _ => rfl) (List.replicate (100 * (b.length + 2)) ()) (Kup + (sched.map Step.K).sum) sched _
    (fun s hs => (List.le_sum_of_mem (List.mem_map_of_mem hs)).trans (Nat.le_add_left _ _)) h0
  unfold needCut needC
  rw [h1]
  cases h : sched.foldl (fun o s => cap (List.replicate (100 * (b.length + 2)) ()) none (o.map fun st => needStep P st s))
      (cap (List.replicate (100 * (b.length + 2)) ()) none (some ((List.replicate lam (), B), (1, 1), (Kup, 0)))) with
  | none => rfl
  | some st => rw [Option.bind_some, Option.bind_some, clip_eq (h2 st h)]

/-- The state, cut off, is polynomial-time. -/
theorem clip_polyT {M : α → ℕ} {st : α → NState} (hM : PolyT M) (hst : PolyT st) : PolyT fun x => clip (M x) (st x) := by
  unfold clip; fun_prop

/-- The number of nodes in a state that is cut off at a number in unary is given in unary. -/
theorem clip_unary {M : α → ℕ} {st : α → NState} (hM : Unary M) (hst : PolyT st) : Unary fun x => (clip (M x) (st x)).2.2.1 :=
  Unary.of_le hM (PolyT.min' (by fun_prop) hM.poly) fun _ => Nat.min_le_right _ _

/-- The computation with the cut-off is polynomial-time. -/
theorem needCut_polyT (hP : P.Keeps) (hL : StCertLam P) {M Kup lam B : α → ℕ} {b : α → U} {sched : α → List Step} (hM : Unary M) (hb : PolyT b)
    (hK : PolyT Kup) (hl : Unary lam) (hB : PolyT B) (hs : PolyT sched) :
    PolyT fun x => needCut P (M x) (b x) (Kup x) (lam x) (B x) (sched x) := by
  have : Meas (Option NState) := measOption
  have hg : PolyT fun q : α × Option NState × Step => q.2.1.map fun st => needStep P (clip (M q.1) st) q.2.2 :=
    PolyT.optionMap (f := fun (q : α × Option NState × Step) st => needStep P (clip (M q.1) st) q.2.2)
      (needStep_polyT hP hL (clip_polyT (hM.poly.comp (by fun_prop)) (by fun_prop)) (by fun_prop)
        (clip_unary (M := fun r : (α × Option NState × Step) × NState => M r.1.1) (hM.comp (by fun_prop)) (by fun_prop))) (by fun_prop)
  have hf := foldl_cap (pad := fun x => List.replicate (100 * ((b x).length + 2)) ()) (l := sched)
    (a := fun x => (some ((List.replicate (lam x) (), B x), (1, 1), (Kup x, 0)) : Option NState))
    (g := fun x o s => o.map fun st => needStep P (clip (M x) st) s) none (by fun_prop) hs (by fun_prop) hg
  have hfin : PolyT fun r : α × NState => needFin (clip (M r.1) r.2) :=
    needFin_polyT (clip_polyT (hM.poly.comp (by fun_prop)) (by fun_prop))
      (clip_unary (M := fun r : α × NState => M r.1) (hM.comp (by fun_prop)) (by fun_prop))
  have key : ∀ v : α × NState → ℕ, PolyT v → PolyT fun r => if v r ≤ (b r.1).length then some (v r) else none := by
    intro v _
    fun_prop
  exact PolyT.optionBind (f := fun x st => if needFin (clip (M x) st) ≤ (b x).length then some (needFin (clip (M x) st)) else none) (key _ hfin) hf

/-- The exponent under a bound is polynomial-time in the bound, the three numbers in unary and the
schedule. -/
theorem stCertNeedC (P : PiecesF) (hL : StCertLam P) : StCertNeedC P := by
  intro hP
  have hM : Unary fun p : U × (U × U × U) × List Step => p.2.1.1.length + (p.2.2.map Step.K).sum :=
    unary_add (by fun_prop) (unary_sum_map (f := fun _ s => Step.K s) (K_unary (by fun_prop)) (by fun_prop))
  exact (needCut_polyT hP hL hM (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)).congr fun p => needCut_eq P _ _ _ _ _

end ClauseBound.Alg.CertLevel
