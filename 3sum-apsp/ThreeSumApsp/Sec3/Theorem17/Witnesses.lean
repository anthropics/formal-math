/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec3.Theorem17.Instances
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Theorem 17, third step: witnesses

For every query pair that the oracle accepts, the piece `C_k` of its instance is scanned for a `c`
with `S(a,b,c) = 0`, and the scans stop at the first zero triangle.  As in the paper:

* a zero triangle is always found (`TriangleInstance.exists_mem_acceptedPairs`);
* a failed scan contains a false positive of `p`
  (`TriangleInstance.exists_isFalsePositive_of_mem_failedScans`), and distinct scans contain
  distinct false positives (`TriangleInstance.eq_of_mem_acceptedPairs`), so there are at most `F(p)`
  failed scans (`TriangleInstance.card_le_F_of_distinct_scans`,
  `TriangleInstance.card_failedScans_le`);
* a scan looks at at most `⌈s/g⌉ ≤ 2√D/g` vertices (`pieceSize_le_two_mul_sqrt_div`), so the scans
  cost `O((F(p) + 1)√D/g) = O(κ n³ log n/g)` (`TriangleInstance.F_add_one_mul_pieceSize_le`).

`Theorem17.correctness` puts the first two together.

The program for Theorem 17 works on lists, and for its lists the sentences of this step are lemmas
of their own: `HostData.found_m` answers `TriangleInstance.exists_mem_acceptedPairs`,
`HostData.exists_false_positive` answers
`TriangleInstance.exists_isFalsePositive_of_mem_failedScans`, `HostData.Valid.eq_of_place_eq`
answers `TriangleInstance.eq_of_mem_acceptedPairs`, and `HostData.sum_fails_le` answers
`TriangleInstance.card_failedScans_le`.  The two proofs share `F(p)`, the first step of the
proof, the number of instances and the counting step `TriangleInstance.card_le_F_of_distinct_scans`;
no theorem about programs rests on another lemma of this file.
-/

@[expose] public section

namespace ThreeSumApsp

variable {n D g p : ℕ}

namespace TriangleInstance

variable {T : TriangleInstance ℤ n}

/-! ### Scans and accepted pairs -/

/-- Proof of Theorem 17, "scan the piece C_k of its instance for a c with S(a,b,c) = 0": a `c` that
a scan returns lies in the piece and has `S(a,b,c) = 0`. -/
theorem scanPiece_eq_some {k : ℕ} {a b c : Fin n} (h : T.scanPiece D g k a b = some c) :
    c ∈ piece n D g k ∧ T.S a b c = 0 := by
  have hmem := List.mem_of_find?_eq_some h
  rw [List.mem_filter] at hmem
  exact ⟨by simpa using hmem.2, by simpa using List.find?_some h⟩

/-- A scan fails exactly if the piece has no `c` with `S(a,b,c) = 0`. -/
theorem scanPiece_eq_none_iff {k : ℕ} {a b : Fin n} :
    T.scanPiece D g k a b = none ↔ ∀ c ∈ piece n D g k, T.S a b c ≠ 0 := by
  unfold scanPiece
  rw [List.find?_eq_none]
  simp [List.mem_filter]

variable (T) (D g)

/-- The scan that belongs to `x = ((ϱ, j, k), (a, b))`, a query pair `(a, b)` of the instance with
index `(ϱ, j, k)`: the piece `C_k` is scanned for the pair `(a, b)`. -/
noncomputable abbrev scanOf (x : InstanceIndex p × (Fin n × Fin n)) : Option (Fin n) :=
  T.scanPiece D g x.1.2.2 x.2.1 x.2.2

/-- What the scans over a list of pairs return: a triangle that is returned is a zero triangle; if
none is returned, then every scan failed; and all the scans that are carried out, except possibly
the last one, fail. -/
private theorem runScans_spec (l : List (InstanceIndex p × (Fin n × Fin n))) :
    (∀ a b c, (T.runScans D g l).1 = some (a, b, c) → T.IsZeroTriangle a b c) ∧
    ((T.runScans D g l).1 = none → ∀ x ∈ l, T.scanOf D g x = none) ∧
    (T.runScans D g l).2 ≤ (l.filter fun x => decide (T.scanOf D g x = none)).length + 1 := by
  induction l with
  | nil => simp [runScans]
  | cons x rest ih =>
    obtain ⟨ihzero, ihnone, ihcount⟩ := ih
    cases hscan : T.scanOf D g x with
    | some c =>
      -- The first scan finds `c`, and the scans stop.
      have hrun : T.runScans D g (x :: rest) = (some (x.2.1, x.2.2, c), 1) := by
        simp only [runScans, hscan]
      rw [hrun]
      refine ⟨fun a b c' h => ?_, fun h => by simp at h, by simp⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (scanPiece_eq_some hscan).2
    | none =>
      -- The first scan fails, and the scans go on with the rest of the list.
      have hrun : T.runScans D g (x :: rest)
          = ((T.runScans D g rest).1, (T.runScans D g rest).2 + 1) := by
        simp only [runScans, hscan]
      rw [hrun, List.filter_cons_of_pos (by simpa using hscan), List.length_cons]
      refine ⟨ihzero, fun h y hy => ?_, by omega⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hscan
      · exact ihnone h y hy

variable (p) (ans : InstanceIndex p → Fin n × Fin n → Bool)

/-- The hypothesis on the oracle: `ans ι` is a correct answer to the instance with index `ι`, for
every instance of the reduction. -/
def IsOracleAnswer : Prop :=
  ∀ ι ∈ T.instanceIndices D g p, (T.lopInstance D g p ι).IsDetectionAnswer (ans ι)

/-- Proof of Theorem 17: a "failed scan, of a piece C_k for a pair (a,b)": the oracle accepted the
pair in the instance, and the piece contains no `c` with `S(a,b,c) = 0`. -/
noncomputable def failedScans : Finset (InstanceIndex p × (Fin n × Fin n)) :=
  (T.acceptedPairs D g p ans).filter fun x => T.scanOf D g x = none

variable {T D g p ans}

/-- The accepted pairs: an index of an instance, a query pair of that instance, and the answer
"yes". -/
theorem mem_acceptedPairs {ι : InstanceIndex p} {q : Fin n × Fin n} :
    (ι, q) ∈ T.acceptedPairs D g p ans ↔
      ι ∈ T.instanceIndices D g p ∧ q ∈ (T.lopInstance D g p ι).W ∧ ans ι q = true := by
  simp [acceptedPairs]

/-! ### The sentences of the paragraph "Witnesses" -/

/-- Proof of Theorem 17: "A zero triangle is always found, since its c lies in some piece and makes
the oracle accept its pair." -/
theorem exists_mem_acceptedPairs (hD : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g) (hp : p ≠ 0)
    (hans : T.IsOracleAnswer D g p ans) {a b c : Fin n} (h0 : T.IsZeroTriangle a b c) :
    ∃ ϱ j k, ((ϱ, j, k), (a, b)) ∈ T.acceptedPairs D g p ans ∧ c ∈ piece n D g k := by
  -- The piece of `c`, the residue class of `(a, b)` and the chunk of `(a, b)` in it.
  obtain ⟨k, ⟨hk, hck⟩, -⟩ := existsUnique_mem_piece hD hg1 c
  obtain ⟨ϱ, hab, -⟩ := T.existsUnique_mem_residueClass hp (a, b)
  obtain ⟨j, hj, hW⟩ := Finset.mem_biUnion.mp
    ((biUnion_chunk (T.residueClass p ϱ) (one_le_queryCap (by omega) hDn)).symm ▸ hab)
  have hι : ((ϱ, j, k) : InstanceIndex p) ∈ T.instanceIndices D g p :=
    (T.mem_instanceIndices _).mpr ⟨Finset.mem_range.mp hj, hk⟩
  have hquery : (a, b) ∈ (T.lopInstance D g p (ϱ, j, k)).W := hW
  refine ⟨ϱ, j, k, mem_acceptedPairs.mpr ⟨hι, hquery, ?_⟩, hck⟩
  -- The vertex `c` makes the oracle accept the pair.
  rw [hans _ hι _ hquery, T.inTriangle_lopInstance_iff hp hquery]
  exact ⟨c, hck, by rw [show T.S a b c = 0 from h0]⟩

/-- Proof of Theorem 17: "A failed scan, of a piece C_k for a pair (a,b), contains a c ∈ C_k with
S(a,b,c) ≡ 0 (mod p) but S(a,b,c) ≠ 0, that is, a false positive (a,b,c) of p". -/
theorem exists_isFalsePositive_of_mem_failedScans (hp : p ≠ 0) (hans : T.IsOracleAnswer D g p ans)
    {ϱ : Fin p} {j k : ℕ} {a b : Fin n} (hx : ((ϱ, j, k), (a, b)) ∈ T.failedScans D g p ans) :
    ∃ c ∈ piece n D g k, T.IsFalsePositive p (a, b, c) := by
  obtain ⟨hacc, hnone⟩ := Finset.mem_filter.mp hx
  obtain ⟨hι, hquery, htrue⟩ := mem_acceptedPairs.mp hacc
  obtain ⟨c, hc, hS⟩ := (T.inTriangle_lopInstance_iff hp hquery).mp ((hans _ hι _ hquery).mp htrue)
  exact ⟨c, hc, scanPiece_eq_none_iff.mp hnone c hc, Int.modEq_zero_iff_dvd.mp hS⟩

/-- Proof of Theorem 17: "distinct scans contain distinct false positives": a triple `(a,b,c)`
belongs to the scan of at most one accepted pair. -/
theorem eq_of_mem_acceptedPairs {ϱ ϱ' : Fin p} {j j' k k' : ℕ} {q : Fin n × Fin n}
    (hx : ((ϱ, j, k), q) ∈ T.acceptedPairs D g p ans)
    (hy : ((ϱ', j', k'), q) ∈ T.acceptedPairs D g p ans) {c : Fin n} (hc : c ∈ piece n D g k)
    (hc' : c ∈ piece n D g k') : (ϱ, j, k) = (ϱ', j', k') := by
  have hp : p ≠ 0 := by
    rintro rfl
    exact ϱ.elim0
  obtain ⟨hclass, hchunk⟩ := mem_lopInstance_W (mem_acceptedPairs.mp hx).2.1
  obtain ⟨hclass', hchunk'⟩ := mem_lopInstance_W (mem_acceptedPairs.mp hy).2.1
  -- The pair determines its residue class, then its chunk; the vertex `c` determines the piece.
  obtain rfl : ϱ = ϱ' := (T.existsUnique_mem_residueClass hp q).unique hclass hclass'
  obtain rfl : j = j' := hchunk.symm.trans hchunk'
  obtain rfl : k = k' := ((mem_piece c).mp hc).symm.trans ((mem_piece c).mp hc')
  rfl

/-- Proof of Theorem 17: "distinct scans contain distinct false positives, so there are at most F(p)
failed scans", for any finite family `s` of scans and any notion "the scan `x` contains the triple
`t`".  The scans of the accepted pairs (`card_failedScans_le`) and the scans of the program
(`HostData.sum_fails_le`) are two such families. -/
theorem card_le_F_of_distinct_scans (T : TriangleInstance ℤ n) {σ : Type*} (s : Finset σ)
    (contains : σ → Fin n × Fin n × Fin n → Prop)
    (hfalse : ∀ x ∈ s, ∃ t, contains x t ∧ T.IsFalsePositive p t)
    (hdistinct : ∀ t, ∀ x ∈ s, ∀ y ∈ s, contains x t → contains y t → x = y) :
    s.card ≤ T.F p := by
  classical
  refine Finset.card_le_card_of_forall_subsingleton contains (fun x hx => ?_)
    fun t _ x hx y hy => hdistinct t x hx.1 y hy.1 hx.2 hy.2
  obtain ⟨t, ht, hfp⟩ := hfalse x hx
  exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfp⟩, ht⟩

/-- Proof of Theorem 17: "so there are at most F(p) failed scans". -/
theorem card_failedScans_le (hp : p ≠ 0) (hans : T.IsOracleAnswer D g p ans) :
    (T.failedScans D g p ans).card ≤ T.F p := by
  -- The scan of the piece `C_k` for the pair `(a, b)` contains the triples `(a, b, c)`, `c ∈ C_k`.
  refine T.card_le_F_of_distinct_scans _
    (fun x t => x.2 = (t.1, t.2.1) ∧ t.2.2 ∈ piece n D g x.1.2.2) ?_ ?_
  · rintro ⟨⟨ϱ, j, k⟩, a, b⟩ hx
    obtain ⟨c, hc, hfalse⟩ := exists_isFalsePositive_of_mem_failedScans hp hans hx
    exact ⟨(a, b, c), ⟨rfl, hc⟩, hfalse⟩
  · rintro ⟨a, b, c⟩ ⟨⟨ϱ, j, k⟩, q⟩ hx ⟨⟨ϱ', j', k'⟩, q'⟩ hy ⟨rfl, hc⟩ ⟨rfl, hc'⟩
    rw [eq_of_mem_acceptedPairs (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hc hc']

end TriangleInstance

/-- Proof of Theorem 17: the length of a scan, the `O(√D/g)` in "the scans cost O((F(p) + 1)√D/g)":
a piece has at most `⌈s/g⌉ ≤ 2√D/g` vertices. -/
theorem pieceSize_le_two_mul_sqrt_div (hg1 : 1 ≤ g) (hg : (g : ℝ) ≤ Real.sqrt D) :
    (pieceSize D g : ℝ) ≤ 2 * Real.sqrt D / (g : ℝ) := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg1
  calc (pieceSize D g : ℝ) ≤ (sOf D : ℝ) / (g : ℝ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    _ ≤ Real.sqrt D / (g : ℝ) + Real.sqrt D / (g : ℝ) :=
        add_le_add (div_le_div_of_nonneg_right (sOf_le_sqrt D) hg0.le)
          ((one_le_div hg0).mpr hg)
    _ = 2 * Real.sqrt D / (g : ℝ) := by ring

/-- Proof of Theorem 17: "the scans cost O((F(p) + 1)√D/g) = O(ν n³ log n/g)". -/
theorem TriangleInstance.F_add_one_mul_pieceSize_le {κ : ℝ} (T : TriangleInstance ℤ n)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g) (hg : (g : ℝ) ≤ Real.sqrt D) (hκ : 1 ≤ κ)
    (hT : T.WeightsPolyBounded κ) (hp : T.IsSelectedPrime D p) :
    ((T.F p : ℝ) + 1) * (pieceSize D g : ℝ)
      ≤ (2 * Hashing.falsePositiveConst + 2) * (κ * (n : ℝ) ^ 3 * Real.log n / (g : ℝ)) := by
  have hsqrt := Real.four_le_sqrt_natCast_of_sixteen_le hD
  have hn : (16 : ℝ) ≤ n := by exact_mod_cast hD.trans hDn
  have hlog : 1 ≤ Real.log n := Real.one_le_log_natCast_of_three_le (by omega)
  set B := κ * (n : ℝ) ^ 3 * Real.log n with hB
  -- The two terms: `F(p) √D = O(B)` by the bound on `F(p)`, and `√D ≤ n ≤ n³ ≤ B`.
  have hfalse : (T.F p : ℝ) * Real.sqrt D ≤ Hashing.falsePositiveConst * B := by
    have hF := Hashing.F_le_falsePositiveConst_mul hD hDn hκ T hT hp
    rwa [← mul_div_assoc, le_div_iff₀ (by linarith)] at hF
  have hone : Real.sqrt D ≤ B :=
    calc Real.sqrt D ≤ n := sqrt_le_natCast (by omega) hDn
      _ ≤ (n : ℝ) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
      _ ≤ κ * (n : ℝ) ^ 3 := le_mul_of_one_le_left (by positivity) hκ
      _ ≤ B := le_mul_of_one_le_right (by positivity) hlog
  calc ((T.F p : ℝ) + 1) * (pieceSize D g : ℝ)
      ≤ ((T.F p : ℝ) + 1) * (2 * Real.sqrt D / (g : ℝ)) := by
        gcongr
        exact pieceSize_le_two_mul_sqrt_div hg1 hg
    _ = (2 * ((T.F p : ℝ) * Real.sqrt D) + 2 * Real.sqrt D) / (g : ℝ) := by ring
    _ ≤ (2 * (Hashing.falsePositiveConst * B) + 2 * B) / (g : ℝ) := by gcongr
    _ = (2 * Hashing.falsePositiveConst + 2) * (B / (g : ℝ)) := by ring

/-! ### The output of the reduction -/

/-- **Theorem 17, correctness.**  Given any correct answers of an oracle for
Lop-AE-SparseTri to the instances of the reduction, and whatever the order `L` of the scans, the
reduction's output is correct: it is a zero triangle if one exists, and `none` otherwise.  It
carries out at most `F(p) + 1` scans ("We stop as soon as a zero triangle is found"). -/
theorem Theorem17.correctness (hD : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g)
    (T : TriangleInstance ℤ n) (hp : T.IsSelectedPrime D p)
    {ans : InstanceIndex p → Fin n × Fin n → Bool} (hans : T.IsOracleAnswer D g p ans)
    {L : List (InstanceIndex p × (Fin n × Fin n))} (hL : T.IsScanOrder D g p ans L) :
    T.IsSearchAnswer (T.runScans D g L).1 ∧ (T.runScans D g L).2 ≤ T.F p + 1 := by
  have hp0 : p ≠ 0 := (mem_primesInRange.mp hp.1).1.ne_zero
  obtain ⟨hzero, hnone, hcount⟩ := T.runScans_spec D g L
  refine ⟨⟨hzero, fun hout ⟨a, b, c, h0⟩ => ?_⟩, ?_⟩
  · -- "A zero triangle is always found": its scan cannot have failed.
    obtain ⟨ϱ, j, k, hx, hc⟩ := TriangleInstance.exists_mem_acceptedPairs hD hDn hg1 hp0 hans h0
    exact TriangleInstance.scanPiece_eq_none_iff.mp (hnone hout _ ((hL.2 _).mpr hx)) c hc h0
  · -- All the scans except possibly the last one fail, and there are at most `F(p)` failed scans.
    have hfailed : (L.filter fun x => decide (T.scanOf D g x = none)).length
        ≤ (T.failedScans D g p ans).card := by
      rw [← List.toFinset_card_of_nodup (hL.1.filter _)]
      refine Finset.card_le_card fun x hx => ?_
      obtain ⟨hxL, hxnone⟩ := List.mem_filter.mp (List.mem_toFinset.mp hx)
      exact Finset.mem_filter.mpr ⟨(hL.2 x).mp hxL, by simpa using hxnone⟩
    have hF := TriangleInstance.card_failedScans_le hp0 hans
    omega

end ThreeSumApsp
