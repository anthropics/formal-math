/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Sieve
public import ThreeSumApsp.Lang.Lib.Sqrt
public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Spec.Sec3.Theorem17.Hashing

/-!
# The primes of the window (proof of Theorem 17)

The hashing of the proof of Theorem 17 uses "a prime p ∈ [√D/2, √D)".  primes(dst, D) lists these
primes in increasing order and returns their number (`primes_spec`).

* It computes s = ⌊√D⌋ and calls the sieve of Eratosthenes, which writes all primes up to s to dst.
  The sieve gets the s + 1 cells behind these s cells for its table.
* One pass keeps the primes p with D ≤ 4p² and p² < D and moves them to the front (`pass_spec`, with
  the round `keep_spec`).  What it keeps is the list of the window (`filter_primesBelow`).
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The pure side -/

/-- The number p lies in the window: √D/2 ≤ p < √D, by integer comparisons. -/
abbrev InWindow (D p : ℕ) : Prop := D ≤ 4 * (p * p) ∧ p * p < D

/-- The numbers of the list L that lie in the window. -/
abbrev inWindow (D : ℕ) (L : List ℕ) : List ℕ := L.filter fun p => InWindow D p

/-- The primes of the window are those of the primes up to ⌊√D⌋ that lie in the window. -/
theorem filter_primesBelow (D : ℕ) :
    inWindow D (Sieve.primesBelow (Nat.sqrt D + 1)) = primesList D := by
  refine List.Perm.eq_of_pairwise' (r := (· ≤ ·)) ?_ ?_ ?_
  · exact ((List.pairwise_le_range).filter _).filter _
  · exact (List.pairwise_le_range).filter _
  · refine (List.perm_ext_iff_of_nodup ((List.nodup_range.filter _).filter _)
      (List.nodup_range.filter _)).2 fun q => ?_
    refine Iff.trans ?_ (Spec.mem_primesList (D := D) (q := q)).symm
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, sq]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨Nat.lt_succ_of_le (Nat.le_sqrt.2 h.2.2.le), h.1⟩, h.2⟩⟩

theorem mul_self_le_of_mem_primesBelow {D p : ℕ} (hp : p ∈ Sieve.primesBelow (Nat.sqrt D + 1)) :
    p * p ≤ D :=
  Nat.le_sqrt.1 (Nat.lt_succ_iff.1 (List.mem_range.1 (List.mem_filter.1 hp).1))

/-- There are at most s - 1 primes up to s. -/
theorem length_primesBelow_succ_le (s : ℕ) : (Sieve.primesBelow (s + 1)).length ≤ s - 1 := by
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · simp [Sieve.primesBelow_one]
  · have := Sieve.length_primesBelow_add_two_le (i := s + 1) (by omega)
    omega

theorem inWindow_take_succ_of_mem {D j : ℕ} {L : List ℕ} (hj : j < L.length) (h : InWindow D L[j]) :
    inWindow D (L.take (j + 1)) = inWindow D (L.take j) ++ [L[j]] := by
  unfold inWindow
  rw [List.take_succ_eq_append_getElem hj, List.filter_append,
    List.filter_cons_of_pos (by simpa using h), List.filter_nil]

theorem inWindow_take_succ_of_not_mem {D j : ℕ} {L : List ℕ} (hj : j < L.length)
    (h : ¬ InWindow D L[j]) : inWindow D (L.take (j + 1)) = inWindow D (L.take j) := by
  unfold inWindow
  rw [List.take_succ_eq_append_getElem hj, List.filter_append,
    List.filter_cons_of_neg (by simpa using h), List.filter_nil, List.append_nil]

/-! ## The program -/

namespace Primes

/-- The local variables of primes: the arguments dst and D; s = ⌊√D⌋; the number of primes up to s;
the number j of those that have been looked at; the prime p that is looked at and its square; the
number cnt of primes that have been kept. -/
abbrev Dest : ℕ := 0
@[inherit_doc Dest] abbrev Size : ℕ := 1
@[inherit_doc Dest] abbrev Root : ℕ := 2
@[inherit_doc Dest] abbrev Total : ℕ := 3
@[inherit_doc Dest] abbrev Index : ℕ := 4
@[inherit_doc Dest] abbrev Prime : ℕ := 5
@[inherit_doc Dest] abbrev Square : ℕ := 6
@[inherit_doc Dest] abbrev Count : ℕ := 7

end Primes

open Primes

/-- The prime number j of the list is kept if it lies in the window. -/
def primesKeep : Stmt :=
  .set Prime (M (v Dest +' v Index)) ;;
  .set Square (v Prime *' v Prime) ;;
  .set Index (v Index +' k 1) ;;
  .ite (v Size ≤' k 4 *' v Square)
    (.ite (v Square <' v Size)
      (.store (v Dest +' v Count) (v Prime) ;; .set Count (v Count +' k 1))
      .skip)
    .skip

/-- The pass over the primes up to s; the result is the number of primes that are kept. -/
def primesPass : Stmt :=
  .set Count (k 0) ;;
  .set Index (k 0) ;;
  .while (v Index <' v Total) primesKeep ;;
  .set 0 (v Count)

/-- primes(dst, D), with the numbers of the procedure sqrt and of the sieve. -/
def primesBody (pSqrt pSieve : ℕ) : Stmt :=
  .call pSqrt [v Size] Root ;;
  .call pSieve [v Root, v Dest, v Dest +' v Root] Total ;;
  primesPass

/-- The number of steps of primes(dst, D). -/
def tPrimes (D : ℕ) : ℕ := 80 * (Nat.sqrt D ^ 3 + 1)

namespace Primes

variable {μ : ℕ → ℤ} {dst D s : ℕ} {L : List ℕ}

/-- The first j primes of the list L have been looked at: those in the window stand at the front of
dst, the primes from number j on are still in their places, and no cell outside the list has
changed. -/
def Sifted (μ : ℕ → ℤ) (dst D s : ℕ) (L : List ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (p q : ℤ),
    σ = ⟨frame [dst, D, s, L.length, j, p, q, (inWindow D (L.take j)).length], μ'⟩ ∧
    SegN μ' dst (inWindow D (L.take j)) ∧ SegN μ' (dst + j) (L.drop j) ∧
    SameOutside μ μ' dst L.length

/-- One round of the pass. -/
theorem keep_spec {j : ℕ} {σ : State} (hw : (lim.space : ℤ) ≤ lim.word)
    (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word) (hdst : dst + L.length ≤ lim.space)
    (hL : ∀ p ∈ L, p * p ≤ D) (hj : j < L.length) (h : Sifted μ dst D s L j σ) :
    Ends lim P d primesKeep σ primesKeep.blockCost (Sifted μ dst D s L (j + 1)) := by
  obtain ⟨μ', p₀, q₀, rfl, front, rest, same⟩ := h
  rw [List.drop_eq_getElem_cons hj] at rest
  obtain ⟨hread, hrest⟩ : μ' (dst + j) = (L[j] : ℕ) ∧ SegN μ' (dst + (j + 1)) (L.drop (j + 1)) :=
    seg_cons.1 rest
  have hcnt : (inWindow D (L.take j)).length ≤ j :=
    (List.length_filter_le _ _).trans (List.length_take_le _ _)
  have hsq : ((L[j] : ℕ) : ℤ) * (L[j] : ℕ) ≤ D := by exact_mod_cast hL _ (List.getElem_mem hj)
  have hsq0 : (0 : ℤ) ≤ ((L[j] : ℕ) : ℤ) * (L[j] : ℕ) := by positivity
  have hle : L[j] ≤ D := (Nat.le_mul_self _).trans (hL _ (List.getElem_mem hj))
  have htake := inWindow_take_succ_of_mem (D := D) hj
  have hpass := inWindow_take_succ_of_not_mem (D := D) hj
  unfold Sifted
  generalize L[j] = p at *
  generalize inWindow D (L.take j) = F at *
  push_cast at hD
  unfold primesKeep
  -- p := dst[j]; q := p * p; j := j + 1
  refine Ends.setToThen (p : ℕ) ?_ (by simp [Limits.Addr, abs_le, hread]; omega)
  refine Ends.setToThen (p * p : ℕ) ?_ (by simp [abs_le, -abs_mul]; omega)
  refine Ends.setToThen (j + 1 : ℕ) ?_
  -- if D ≤ 4 q and q < D
  refine Ends.iteLast (fun hlow => Ends.iteLast (fun hhigh => ?_) fun hnhigh => ?_) fun hnlow => ?_
  · have hin : InWindow D p :=
      ⟨by exact_mod_cast (by simpa [Cond.holds_le] using hlow : (D : ℤ) ≤ 4 * ((p : ℤ) * p)),
        by exact_mod_cast (by simpa using hhigh : (p : ℤ) * p < D)⟩
    rw [htake hin]
    -- dst[cnt] := p; cnt := cnt + 1
    refine Ends.storeToThen (dst + F.length) p ?_
    exact Ends.setTo (F.length + 1 : ℕ) ⟨Function.update μ' (dst + F.length) p, p, (p * p : ℕ),
      by simp, front.snoc p, hrest.update_out (Or.inl (by omega)) _,
      same.update ⟨by omega, by omega⟩ _⟩
  · rw [hpass fun hin => hnhigh (by simpa using (by exact_mod_cast hin.2 : (p : ℤ) * p < D))]
    exact Ends.skip ⟨μ', p, (p * p : ℕ), rfl, front, hrest, same⟩
  · rw [hpass fun hin => hnlow (by
      simpa [Cond.holds_le] using (by exact_mod_cast hin.1 : (D : ℤ) ≤ 4 * ((p : ℤ) * p)))]
    exact Ends.skip ⟨μ', p, (p * p : ℕ), rfl, front, hrest, same⟩

/-- The pass keeps the numbers of the list that lie in the window, and returns how many they are. -/
theorem pass_spec (hw : (lim.space : ℤ) ≤ lim.word) (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word)
    (hdst : dst + L.length ≤ lim.space) (hL : ∀ p ∈ L, p * p ≤ D) (seg : SegN μ dst L) :
    Ends lim P d primesPass ⟨frame [dst, D, s, L.length], μ⟩ (38 * L.length + 10) fun σ' =>
      σ'.loc 0 = ((inWindow D L).length : ℕ) ∧ SegN σ'.mem dst (inWindow D L) ∧
        SameOutside μ σ'.mem dst L.length := by
  -- cnt := 0; j := 0
  refine Ends.setToThen (0 : ℕ) (Ends.setToThen (0 : ℕ) ?_)
  -- while j < total
  refine Ends.next _ (Ends.whileConst (Sifted μ dst D s L) L.length primesKeep.blockCost ?start
    ?round ?done le_rfl) (by simp [primesKeep]; omega)
  case start =>
    exact ⟨μ, 0, 0, by simp, by rw [List.take_zero]; exact Seg.nil, by simpa using seg, .refl⟩
  case round =>
    rintro j σ hj h
    have hrun := keep_spec (P := P) (d := d) hw hD hdst hL hj h
    obtain ⟨μ', p, q, rfl, -⟩ := h
    exact ⟨by light_side, by light_side, hrun⟩
  case done =>
    rintro _ h
    rw [Sifted, List.take_length] at h
    obtain ⟨μ', p, q, rfl, front, -, same⟩ := h
    refine ⟨by light_side, by light_side, ?_⟩
    -- the result is cnt
    exact Ends.setTo ((inWindow D L).length : ℕ) ⟨by simp, front, same⟩ (by simp)
      (by simp [primesKeep]; omega)

/-- What primes needs of the program: the procedures sqrt and the sieve of Eratosthenes. -/
structure Ctx (P : Program) (pSqrt pSieve : ℕ) : Prop where
  hSqrt : P[pSqrt]? = some sqrtBody
  hSieve : P[pSieve]? = some sieveBody

/-- The square root, the sieve up to s, and a pass over n ≤ s - 1 primes. -/
theorem time_le {s n : ℕ} (hn : n ≤ s - 1) :
    18 * s + sieveTime s + 38 * n + 32 ≤ 80 * (s ^ 3 + 1) := by
  unfold sieveTime
  rcases Nat.lt_or_ge s 2 with hs | hs
  · interval_cases s <;> simp at hn ⊢ <;> omega
  · have hlog : 15 * s * (Nat.log 2 s + 5) ≤ 15 * s * (s + 4) :=
      Nat.mul_le_mul_left _ (by have := Nat.log_lt_self 2 (x := s) (by omega); omega)
    have hsq : 2 * (s * s) ≤ s ^ 3 := by
      rw [pow_succ, sq, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ hs
    have hlin : 2 * s ≤ s * s := Nat.mul_le_mul_right _ hs
    have hmul : 15 * s * (s + 4) = 15 * (s * s) + 60 * s := by ring
    omega

end Primes

/-- **primes** writes the primes of the window, in increasing order, to dst, and returns their
number.  Only the 2 ⌊√D⌋ + 1 cells from dst may change. -/
theorem primes_spec {μ : ℕ → ℤ} {dst D pSqrt pSieve : ℕ} (C : Primes.Ctx P pSqrt pSieve)
    (hw : (lim.space : ℤ) ≤ lim.word) (hD : ((4 * D + 4 : ℕ) : ℤ) ≤ lim.word)
    (hdst : dst + (2 * Nat.sqrt D + 1) ≤ lim.space) (hd : d < lim.depth) :
    Ends lim P d (primesBody pSqrt pSieve) ⟨frame [dst, D], μ⟩ (tPrimes D) fun σ' =>
      σ'.loc 0 = ((primesList D).length : ℕ) ∧ SegN σ'.mem dst (primesList D) ∧
        SameOutside μ σ'.mem dst (2 * Nat.sqrt D + 1) := by
  have hsD : Nat.sqrt D ≤ D := Nat.sqrt_le_self D
  have hL := fun p => mul_self_le_of_mem_primesBelow (D := D) (p := p)
  have hlen := length_primesBelow_succ_le (Nat.sqrt D)
  have htime := time_le hlen
  have hsqrt : Meets lim P pSqrt (d + 1) [D] μ (18 * Nat.sqrt D + 12) fun r μ' =>
      r = Nat.sqrt D ∧ μ' = μ :=
    sqrt_meets C.hSqrt μ (by push_cast at hD ⊢; omega)
  have hsieve := sieve_meets (μ := μ) (d := d + 1) (out := dst) (fr := dst + Nat.sqrt D) C.hSieve
    ⟨hw, by push_cast at hD ⊢; omega, le_rfl, by omega⟩
  rw [Sieve.sort_primesLE, ← Sieve.length_primesBelow] at hsieve
  rw [← filter_primesBelow D, tPrimes]
  generalize Sieve.primesBelow (Nat.sqrt D + 1) = L at *
  generalize Nat.sqrt D = s at *
  -- s := sqrt(D)
  refine Ends.callToThen hsqrt ?_
  rintro _ μ₀ ⟨rfl, hμ₀⟩
  obtain rfl : μ = μ₀ := hμ₀.symm
  -- total := sieve(s, dst, dst + s)
  refine Ends.callToThen hsieve ?_
  rintro _ μ₁ ⟨rfl, seg, kept⟩
  -- the pass
  refine (pass_spec hw hD (by omega) hL seg).mono (by light_time) ?_
  rintro σ' ⟨hcount, front, same⟩
  exact ⟨hcount, front, kept.then same fun b hb => ⟨⟨by omega, by omega⟩, by omega⟩⟩

end Light.Sec3
