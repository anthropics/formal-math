/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.Data
public import ClauseBound.Rec.Defs
public import ClauseBound.Rec.CountRow
public import PaddedDescent.F.FuelCert

/-! # The arithmetic of the recombined pieces as programs

The coefficients of the recombined pieces are sums of binomial coefficients with an integer on top.
This file writes them as programs made of loops over ranges, proves that `chooseZ` is the binomial
coefficient
and that `nbF` and `muF` are the block sizes and the number μ of `Pieces`, and proves that the
programs are polynomial-time when the lengths of the loops are given in unary:

* `chooseZ a k` is the binomial coefficient C(a, k) for an integer a, `phiF` is φ_{a,w}(j), `qqF` is
  the coefficient of ψ_β(x,y)·ψ_β(u,v) in Â_t;
* `ccF` is the coefficient of ψ_β(x,u)·ψ_β(y,v) in Â_t, computed from the few numbers through which
  it depends on β: all blocks but the last have the same number of positions, so the
  polynomial of β is a power of one linear factor times at most one other, and the binomial theorem
  gives its coefficients;
* `muF` is μ, by the closed form with the common denominator 2^(λ+1);
* the number of blocks (`nblk`), the block sizes and μ can be written in unary. -/

@[expose] public section

namespace ClauseBound.Inst.Rec

open Finset Polynomial Groundwork PaddedDescent.F ClauseBound.Rec

/-! ### The programs -/

/-- b^k. -/
def powZ (b : ℤ) (k : ℕ) : ℤ := prodL k fun _ => b

/-- a(a − 1)⋯(a − k + 1). -/
def fallZ (a : ℤ) (k : ℕ) : ℤ := prodL k fun i => a - i

/-- k!. -/
def factN (k : ℕ) : ℕ := (prodL k fun i => (i : ℤ) + 1).natAbs

/-- The binomial coefficient C(a, k) for an integer a: the falling product divided by k!, sign and
absolute value apart. -/
def chooseZ (a : ℤ) (k : ℕ) : ℤ :=
  if fallZ a k < 0 then -(((fallZ a k).natAbs / factN k : ℕ) : ℤ) else (((fallZ a k).natAbs / factN k : ℕ) : ℤ)

/-- Σ_{k<w} f k. -/
def sumR (w : ℕ) (f : ℕ → ℤ) : ℤ := ((List.range w).map f).sum

/-- (−1)^a. -/
def sgnZ (a : ℤ) : ℤ := if a.natAbs % 2 = 0 then 1 else -1

/-- φ_{a,w}(j). -/
def phiF (a : ℤ) (w : ℕ) (j : ℤ) : ℤ := sgnZ a * sumR w fun k => powZ (-2) k * chooseZ (j - a) k

/-- The coefficient of ψ_β(x,y)·ψ_β(u,v) in Â_t, for odd(β) = j. -/
def qqF (μ t j : ℕ) : ℤ := phiF ((μ : ℤ) - t) (2 * t + 1) j - phiF ((μ : ℤ) - t + 1) (2 * t - 1) j

/-- The functional with parameters a and w at the polynomial σ·T^ν·(2^{n₀} − (2^{n₀} − 1)·T)^z,
times 2^r − (2^r − 1)·T if ε. -/
def linF (a : ℤ) (w : ℕ) (σ : ℤ) (ν z n₀ : ℕ) (ε : Bool) (r : ℕ) : ℤ :=
  σ * sumR (z + 1) fun i => chooseZ z i * powZ (powZ 2 n₀) (z - i) * powZ (1 - powZ 2 n₀) i *
    ((bif ε then powZ 2 r else 1) * phiF a (w - (ν + i)) 0 + (bif ε then 1 - powZ 2 r else 0) * phiF a (w - (ν + i + 1)) 0)

/-- The coefficient of ψ_β(x,u)·ψ_β(y,v) in Â_t, for a label β whose polynomial is σ·T^ν·(2^{n₀} −
(2^{n₀} − 1)·T)^z, times 2^r − (2^r − 1)·T if ε. -/
def ccF (μ t : ℕ) (σ : ℤ) (ν z n₀ : ℕ) (ε : Bool) (r : ℕ) : ℤ :=
  linF ((μ : ℤ) - t) (2 * t + 1) σ ν z n₀ ε r - linF ((μ : ℤ) - t + 1) (2 * t - 1) σ ν z n₀ ε r

/-- The number of positions of block b. -/
def nbF (lam h b : ℕ) : ℕ := (List.range lam).countP fun k => decide (k / h = b)

/-- μ: the sum of (2^{n_b} − 1)·2^{λ − n_b} over the blocks, divided by 2^{λ+1}. -/
def muF (lam h : ℕ) : ℕ :=
  ((List.range (Pieces.nblk lam h)).map fun b => (2 ^ nbF lam h b - 1) * 2 ^ (lam - nbF lam h b)).sum / 2 ^ (lam + 1)

/-! ### What some of the programs compute -/

theorem factN_eq (k : ℕ) : factN k = k.factorial := by
  rw [factN, prodL_eq]
  have : ∏ i ∈ range k, ((i : ℤ) + 1) = ((k.factorial : ℕ) : ℤ) := by
    rw [← Finset.prod_range_add_one_eq_factorial]; push_cast; rfl
  rw [this, Int.natAbs_natCast]

theorem fallZ_eq (a : ℤ) (k : ℕ) : fallZ a k = k.factorial * Ring.choose a k := by
  rw [fallZ, prodL_eq, ← descPochhammer_eval_eq_prod_range, ← nsmul_eq_mul, ← Ring.descPochhammer_eq_factorial_smul_choose,
    Polynomial.eval_eq_smeval]

theorem chooseZ_eq (a : ℤ) (k : ℕ) : chooseZ a k = Ring.choose a k := by
  have hk : 0 < k.factorial := k.factorial_pos
  have hk' : (0 : ℤ) < (k.factorial : ℤ) := by exact_mod_cast hk
  rw [chooseZ, fallZ_eq, factN_eq, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_div_cancel_left _ hk]
  rcases lt_or_ge (Ring.choose a k) 0 with h | h
  · rw [if_pos (mul_neg_of_pos_of_neg hk' h)]
    omega
  · rw [if_neg (not_lt.2 (mul_nonneg hk'.le h))]
    omega

theorem sumR_eq (w : ℕ) (f : ℕ → ℤ) : sumR w f = ∑ k ∈ range w, f k := by
  rw [sumR, ← List.sum_toFinset _ (List.nodup_range), List.toFinset_range]

theorem sgnZ_eq (a : ℤ) : sgnZ a = if Even a then 1 else -1 := by
  unfold sgnZ
  refine if_congr ?_ rfl rfl
  rw [← Int.natAbs_even, Nat.even_iff]

/-- Counting in a list of the numbers below n is counting in the finite set. -/
theorem countP_range (n : ℕ) (q : ℕ → Bool) : (List.range n).countP q = #{k ∈ range n | q k = true} := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih, range_add_one, filter_insert]
    by_cases hq : q n = true
    · rw [if_pos hq, card_insert_of_notMem (by simp)]; simp [hq]
    · rw [if_neg hq]; simp [hq]

theorem nbF_eq (lam h b : ℕ) : nbF lam h b = #(Pieces.blk lam h b) := by
  rw [nbF, countP_range, Pieces.blk]
  simp only [decide_eq_true_eq]
  rw [card_filter, card_filter, Fin.sum_univ_eq_sum_range fun k => if k / h = b then 1 else 0]

theorem nbF_le (lam h b : ℕ) : nbF lam h b ≤ lam :=
  (List.countP_le_length).trans_eq List.length_range

theorem sumN_eq (w : ℕ) (f : ℕ → ℕ) : ((List.range w).map f).sum = ∑ k ∈ range w, f k := by
  rw [← List.sum_toFinset _ (List.nodup_range), List.toFinset_range]

/-- μ, for all λ and h. -/
theorem muF_eq (lam h : ℕ) : muF lam h = Pieces.mu lam h := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · have h0 : Pieces.nblk lam 0 = 0 := Nat.div_zero _
    simp [muF, Pieces.mu, Pieces.odd, h0]
  · rw [mu_eq lam hh, muF, sumN_eq]
    have key : (∑ b ∈ range (Pieces.nblk lam h), (2 ^ nbF lam h b - 1) * 2 ^ (lam - nbF lam h b)) * 2 ^ h =
        (∑ b ∈ range (Pieces.nblk lam h), (2 ^ #(Pieces.blk lam h b) - 1) * 2 ^ (h - #(Pieces.blk lam h b))) * 2 ^ lam := by
      rw [sum_mul, sum_mul]
      refine sum_congr rfl fun b _ => ?_
      have h1 := nbF_le lam h b
      have h2 := card_blk_le (n := lam) hh b
      rw [nbF_eq] at h1 ⊢
      rw [mul_assoc, mul_assoc, ← pow_add, ← pow_add]
      congr 2
      omega
    rw [← Nat.mul_div_mul_right _ _ (Nat.pow_pos (n := h) (by norm_num : 0 < 2)), key, pow_succ, pow_succ,
      show 2 ^ lam * 2 * 2 ^ h = 2 ^ h * 2 * 2 ^ lam by ring, Nat.mul_div_mul_right _ _ (Nat.pow_pos (by norm_num))]

/-- There are at most λ blocks. -/
theorem nblk_le_all (lam h : ℕ) : Pieces.nblk lam h ≤ lam := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · rw [Pieces.nblk, Nat.div_zero]; exact Nat.zero_le _
  · exact nblk_le lam hh

/-- μ ≤ λ. -/
theorem muF_le (lam h : ℕ) : muF lam h ≤ lam := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · have h0 : Pieces.nblk lam 0 = 0 := Nat.div_zero _
    simp [muF, h0]
  · have h1 := two_mul_mu_le lam hh
    have h2 := nblk_le lam hh
    rw [muF_eq]
    omega

/-- ⌈log₂ n⌉ is the number of binary digits of n − 1. -/
theorem clog_two_eq (n : ℕ) : Nat.clog 2 n = Nat.size (n - 1) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · rw [Nat.clog_of_right_le_one (by omega)]
    have : n - 1 = 0 := by omega
    rw [this, Nat.size_zero]
  · refine le_antisymm ?_ ?_
    · rw [Nat.clog_le_iff_le_pow (by norm_num)]
      have := Nat.lt_size_self (n - 1)
      omega
    · rw [Nat.size_le]
      have := Nat.le_pow_clog (b := 2) (by norm_num) n
      omega

/-! ### The certificates -/

variable {α β : Type} [Enc α] [Enc β]

@[fun_prop] theorem unary_min_right {f g : α → ℕ} (hf : PolyT f) (hg : Unary g) : Unary fun x => min (f x) (g x) :=
  Unary.of_le hg (by have := hg.poly; fun_prop) fun _ => min_le_right _ _

theorem map_range_polyT {w : α → ℕ} {f : α → ℕ → β} (hw : Unary w) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (w p.1))) :
    PolyT fun x => (List.range (w x)).map (f x) := by
  have h : PolyT fun x => (List.range (w x)).map fun k => f x (min k (w x)) :=
    PolyT.map (f := fun x k => f x (min k (w x))) hf (range_polyT hw)
  exact h.congr fun x => List.map_congr_left fun k hk => by rw [min_eq_left (List.mem_range.1 hk).le]

theorem sumR_polyT {w : α → ℕ} {f : α → ℕ → ℤ} (hw : Unary w) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (w p.1))) :
    PolyT fun x => sumR (w x) (f x) := by
  have := map_range_polyT hw hf
  unfold sumR; fun_prop

@[fun_prop] theorem powZ_polyT {b : α → ℤ} {k : α → ℕ} (hb : PolyT b) (hk : Unary k) : PolyT fun x => powZ (b x) (k x) := by
  unfold powZ; fun_prop

@[fun_prop] theorem fallZ_polyT {a : α → ℤ} {k : α → ℕ} (ha : PolyT a) (hk : Unary k) : PolyT fun x => fallZ (a x) (k x) := by
  unfold fallZ; fun_prop

@[fun_prop] theorem factN_polyT {k : α → ℕ} (hk : Unary k) : PolyT fun x => factN (k x) := by
  unfold factN; fun_prop

@[fun_prop] theorem chooseZ_polyT {a : α → ℤ} {k : α → ℕ} (ha : PolyT a) (hk : Unary k) : PolyT fun x => chooseZ (a x) (k x) := by
  have h0 : PolyT fun x => fallZ (a x) (k x) := fallZ_polyT ha hk
  have h1 : PolyT fun x => (fallZ (a x) (k x)).natAbs / factN (k x) := PolyT.div (PolyT.natAbs h0) (factN_polyT hk)
  exact PolyT.ite' (PolyT.decide_ltZ h0 (PolyT.const 0)) (PolyT.negZ (PolyT.natCast h1)) (PolyT.natCast h1)

@[fun_prop] theorem sgnZ_polyT {a : α → ℤ} (ha : PolyT a) : PolyT fun x => sgnZ (a x) := by
  unfold sgnZ; fun_prop

@[fun_prop] theorem phiF_polyT {a j : α → ℤ} {w : α → ℕ} (ha : PolyT a) (hw : Unary w) (hj : PolyT j) :
    PolyT fun x => phiF (a x) (w x) (j x) := by
  have := sumR_polyT (f := fun x k => powZ (-2) k * chooseZ (j x - a x) k) hw (by fun_prop)
  unfold phiF; fun_prop

@[fun_prop] theorem qqF_polyT {μ t j : α → ℕ} (hμ : PolyT μ) (ht : Unary t) (hj : PolyT j) :
    PolyT fun x => qqF (μ x) (t x) (j x) := by
  have := ht.poly
  unfold qqF; fun_prop

@[fun_prop] theorem linF_polyT {a σ : α → ℤ} {w ν z n₀ r : α → ℕ} {ε : α → Bool} (ha : PolyT a) (hw : Unary w) (hσ : PolyT σ) (hν : PolyT ν)
    (hz : Unary z) (hn : Unary n₀) (hε : PolyT ε) (hr : Unary r) :
    PolyT fun x => linF (a x) (w x) (σ x) (ν x) (z x) (n₀ x) (ε x) (r x) := by
  have hz' := hz.poly
  have := sumR_polyT (w := fun x => z x + 1) (f := fun x i => chooseZ (z x) i * powZ (powZ 2 (n₀ x)) (z x - i) * powZ (1 - powZ 2 (n₀ x)) i *
    ((bif ε x then powZ 2 (r x) else 1) * phiF (a x) (w x - (ν x + i)) 0 +
      (bif ε x then 1 - powZ 2 (r x) else 0) * phiF (a x) (w x - (ν x + i + 1)) 0)) (by fun_prop) (by fun_prop)
  unfold linF; fun_prop

@[fun_prop] theorem ccF_polyT {μ t ν z n₀ r : α → ℕ} {σ : α → ℤ} {ε : α → Bool} (hμ : PolyT μ) (ht : Unary t) (hσ : PolyT σ) (hν : PolyT ν)
    (hz : Unary z) (hn : Unary n₀) (hε : PolyT ε) (hr : Unary r) :
    PolyT fun x => ccF (μ x) (t x) (σ x) (ν x) (z x) (n₀ x) (ε x) (r x) := by
  have := ht.poly
  unfold ccF; fun_prop

@[fun_prop] theorem nblk_polyT {lam h : α → ℕ} (hl : PolyT lam) (hh : PolyT h) : PolyT fun x => Pieces.nblk (lam x) (h x) := by
  unfold Pieces.nblk; fun_prop

@[fun_prop] theorem nblk_unary {lam h : α → ℕ} (hl : Unary lam) (hh : PolyT h) : Unary fun x => Pieces.nblk (lam x) (h x) :=
  Unary.of_le hl (nblk_polyT hl.poly hh) fun _ => nblk_le_all _ _

@[fun_prop] theorem nbF_polyT {lam h b : α → ℕ} (hl : Unary lam) (hh : PolyT h) (hb : PolyT b) : PolyT fun x => nbF (lam x) (h x) (b x) := by
  unfold nbF; fun_prop

@[fun_prop] theorem nbF_unary {lam h b : α → ℕ} (hl : Unary lam) (hh : PolyT h) (hb : PolyT b) : Unary fun x => nbF (lam x) (h x) (b x) :=
  Unary.of_le hl (nbF_polyT hl hh hb) fun _ => nbF_le _ _ _

@[fun_prop] theorem muF_polyT {lam h : α → ℕ} (hl : Unary lam) (hh : PolyT h) : PolyT fun x => muF (lam x) (h x) := by
  have := hl.poly
  unfold muF; fun_prop

@[fun_prop] theorem muF_unary {lam h : α → ℕ} (hl : Unary lam) (hh : PolyT h) : Unary fun x => muF (lam x) (h x) :=
  Unary.of_le hl (muF_polyT hl hh) fun _ => muF_le _ _

end ClauseBound.Inst.Rec
