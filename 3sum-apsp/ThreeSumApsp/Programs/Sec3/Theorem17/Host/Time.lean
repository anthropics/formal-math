/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.FailedScans
public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Need

/-!
# The host of Theorem 17: the time of a run is within the worst case

The host procedure `et17` (Exact Triangle by Theorem 17) first computes the parameters, chooses the
prime and computes the sizes.  The time of what follows (the table of doubles, the residues, the
classes, the chunks and the loop over the instances; `hostRunTime`) depends on the data: the prime,
the number of chunks, the scans.  Here it is bounded by the corresponding summands of `hostMain`,
which depend on `n`, `U`, `D` and `g` only (`hostRunTime_le`).

* The prime is at most `√D` (`hostData_p_le`), and there are at most `4ng` instances and no more
  chunks than instances (`hostData_m_le`, `HostTime.chunkCount_le_m`).
* An instance has a piece of at most `q = ⌈s/g⌉` vertices, where `s = ⌊√D⌋`, and at most `⌊n²/√D⌋`
  query pairs, so its time without the scans is at most the worst case (`HostTime.instance_le`).
* All scans but one fail, and a failed scan belongs to a false positive of the chosen prime.  The
  proof of Theorem 17 bounds their number (`F_le_falsePositiveBound`).
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The number of false positives of the chosen prime is at most `falsePositiveBound`. -/
theorem F_le_falsePositiveBound {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ} (hpre : x.Pre μ fr)
    (h : BigCase x.n D g) :
    (triOf x.n x.AB x.BC x.AC).F (chosenPrime x.n D x.AB x.BC x.AC)
      ≤ falsePositiveBound x.n x.U D :=
  Nat.le_floor (F_chosenPrime_le h.sixteen_le h.le_n hpre.U_pos hpre.leAB hpre.leBC hpre.leAC)

namespace HostTime

/-! ## One instance -/

/-- Writing the two matrices of an instance takes longer for a longer piece. -/
private theorem tWrites_mono (n D : ℕ) {a b : ℕ} (h : a ≤ b) : tWrites n D a ≤ tWrites n D b := by
  unfold tWrites tWriteX tWriteY
  gcongr

/-- The time of the solver on an instance with at most `cap` query pairs is at most `supTime`, its
largest time on such instances. -/
private theorem le_supTime (Tn : List ℕ → ℕ) (n D : ℕ) {w cap : ℕ} (h : w ≤ cap) :
    Tn [n, D, w] ≤ supTime Tn n D cap :=
  Finset.le_sup (f := fun w => Tn [n, D, w]) (Finset.mem_range.2 (by omega))

/-- The time of an instance with a piece of `len ≤ q` vertices, `w ≤ cap` query pairs and `execs`
scans is at most the worst case for `q` and `cap` plus the time of the scans. -/
private theorem instance_le (Tn : List ℕ → ℕ) (n D execs : ℕ) {len q w cap : ℕ} (hlen : len ≤ q)
    (hw : w ≤ cap) :
    tWrites n D len + Tn [n, D, w] + tScanPairs w len execs
      ≤ tWrites n D q + supTime Tn n D cap + tAnswers cap + tScanCall q * execs := by
  have hwrites := tWrites_mono n D hlen
  have hsolver := le_supTime Tn n D hw
  have hanswers : tAnswers w ≤ tAnswers cap := by
    unfold tAnswers
    gcongr
  have hscans : tScanCall len * execs ≤ tScanCall q * execs := by
    unfold tScanCall tScan
    gcongr
  unfold tScanPairs
  omega

/-- A sum of `m ≤ M` terms `f t ≤ A + B e(t)` is at most `M A + B E` if the `e(t)` add up to at most
`E`. -/
private theorem sum_le_mul_add {m M A B E : ℕ} {f e : ℕ → ℕ} (hf : ∀ t < m, f t ≤ A + B * e t)
    (hm : m ≤ M) (he : ∑ t ∈ Finset.range m, e t ≤ E) :
    ∑ t ∈ Finset.range m, f t ≤ M * A + B * E :=
  calc ∑ t ∈ Finset.range m, f t ≤ ∑ t ∈ Finset.range m, (A + B * e t) :=
        Finset.sum_le_sum fun t ht => hf t (Finset.mem_range.1 ht)
    _ = m * A + B * ∑ t ∈ Finset.range m, e t := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
          Finset.mul_sum]
    _ ≤ M * A + B * E := Nat.add_le_add (Nat.mul_le_mul_right _ hm) (Nat.mul_le_mul_left _ he)

/-! ## The data of a run -/

variable {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ}

/-- There are at most as many chunks as instances. -/
private theorem chunkCount_le_m {X : HostData} (hv : X.Valid) : X.chunkCount ≤ X.m := by
  have hn := hv.n_pos
  have hq := hv.q_pos
  have hpieces : 1 ≤ X.h := by
    rw [HostData.h, Nat.ceilDiv_eq_add_pred_div, Nat.le_div_iff_mul_le (by omega)]
    omega
  rw [HostData.m]
  exact Nat.le_mul_of_pos_left _ hpieces

/-- All scans but one fail, and there are at most `falsePositiveBound` failed scans. -/
private theorem sum_execs_le_falsePositiveBound (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) :
    ∑ t ∈ Finset.range (hostData x D g).m, (hostData x D g).execs t
      ≤ falsePositiveBound x.n x.U D + 1 :=
  (hostData x D g).sum_execs_le.trans (Nat.add_le_add_right
    ((HostData.sum_fails_le (hostData_valid hpre hbig)).trans
      (F_le_falsePositiveBound hpre hbig)) 1)

end HostTime

open HostTime

variable {x : TriInst} {μ : ℕ → ℤ} {fr D g : ℕ}

/-- The time of the loop over the instances is within its bound.  Both sides are a sum over the
instances plus the same constant; the piece of an instance has `min q (n - c₀)` vertices. -/
private theorem tHostLoop_le (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    tHostLoop Tn (hostData x D g) ≤ hostLoopBound Tn x.n x.U D g :=
  Nat.add_le_add_right (sum_le_mul_add
    (fun _ ht => instance_le Tn x.n D _ (Nat.min_le_left _ _) ((hostData x D g).w_le_cap ht))
    (hostData_m_le hbig) (sum_execs_le_falsePositiveBound hpre hbig)) 14

/-- **The time of a run after the choice of the prime is within the worst case.** -/
theorem hostRunTime_le (hpre : x.Pre μ fr) (hbig : BigCase x.n D g) (Tn : List ℕ → ℕ) :
    hostRunTime Tn (hostData x D g) x.U
      ≤ tDblTable (bitLen x.U) + 3 * tResidues (x.n * x.n) (bitLen x.U)
        + tClasses x.n (Nat.sqrt D) + tChunks (Nat.sqrt D) (4 * x.n * g)
        + hostLoopBound Tn x.n x.U D g + 80 := by
  have hprime : (hostData x D g).p ≤ Nat.sqrt D := hostData_p_le x g hbig.sixteen_le
  have hchunks : (hostData x D g).chunkCount ≤ 4 * x.n * g :=
    (chunkCount_le_m (hostData_valid hpre hbig)).trans (hostData_m_le hbig)
  have hloop := tHostLoop_le hpre hbig Tn
  have hn : (hostData x D g).n = x.n := rfl
  unfold hostRunTime
  rw [hn]
  unfold tClasses tChunks
  omega

end Light.Sec3
