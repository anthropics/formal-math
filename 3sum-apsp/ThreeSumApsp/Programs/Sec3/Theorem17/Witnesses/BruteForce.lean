/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Witnesses.Scan

/-!
# Brute force (the proof of Theorem 19)

In the proof of Theorem 19, "smaller instances are solved by brute force": the procedure brute
(`bruteBody`) scans all of `C` for every pair `(a, b)` (`brute_spec`, `brute_meets`).  It takes at
most `100 n³ + 100` steps (`brute_solves`).
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Brute force finds a zero triangle if and only if there is one. -/
theorem hasZero_iff (n : ℕ) (AB BC AC : List ℤ) :
    hasZero n AB BC AC = true ↔ (triOf n AB BC AC).HasZeroTriangle := by
  unfold hasZero TriangleInstance.HasZeroTriangle TriangleInstance.IsZeroTriangle TriangleInstance.S
  simp only [List.any_eq_true, List.mem_range, scanHit, decide_eq_true_eq]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, h⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, by simpa [triOf] using h⟩
  · rintro ⟨a, b, c, h⟩
    exact ⟨a, a.2, b, b.2, c, c.2, by simpa [triOf] using h⟩

/-- Some `b` below `b'` gives a zero triangle with `a`. -/
def bruteRow (n : ℕ) (AB BC AC : List ℤ) (a b' : ℕ) : Bool :=
  (List.range b').any fun b => scanHit n AB BC AC a b 0 n

/-- Some `a` below `a'` is in a zero triangle. -/
def bruteAll (n : ℕ) (AB BC AC : List ℤ) (a' : ℕ) : Bool :=
  (List.range a').any fun a => bruteRow n AB BC AC a n

theorem bruteRow_succ (n : ℕ) (AB BC AC : List ℤ) (a b : ℕ) :
    bruteRow n AB BC AC a (b + 1) = (bruteRow n AB BC AC a b || scanHit n AB BC AC a b 0 n) := by
  simp [bruteRow, List.range_succ, List.any_append]

theorem bruteAll_succ (n : ℕ) (AB BC AC : List ℤ) (a : ℕ) :
    bruteAll n AB BC AC (a + 1) = (bruteAll n AB BC AC a || bruteRow n AB BC AC a n) := by
  simp [bruteAll, List.range_succ, List.any_append]

namespace Brute

/-- The locals of `brute`.  The arguments: `n`, `U`, the addresses of the three arrays, and the free
pointer.  Then the vertices `a` and `b`, the result so far, and the result of a scan. -/
abbrev Size : ℕ := 0
@[inherit_doc Size] abbrev Bound : ℕ := 1
@[inherit_doc Size] abbrev AdrAB : ℕ := 2
@[inherit_doc Size] abbrev AdrBC : ℕ := 3
@[inherit_doc Size] abbrev AdrAC : ℕ := 4
@[inherit_doc Size] abbrev Free : ℕ := 5
@[inherit_doc Size] abbrev VtxA : ℕ := 6
@[inherit_doc Size] abbrev VtxB : ℕ := 7
@[inherit_doc Size] abbrev Hit : ℕ := 8
@[inherit_doc Size] abbrev Res : ℕ := 9

end Brute

open Brute in
/-- One pair `(a, b)`: res := scan(ab, bc, ac, n, a, b, 0, n); if res = 1 then hit := 1. -/
def brutePair (pScan : ℕ) : Stmt :=
  .call pScan [v AdrAB, v AdrBC, v AdrAC, v Size, v VtxA, v VtxB, k 0, v Size] Res ;;
  .ite (v Res =' k 1) (.set Hit (k 1)) .skip

open Brute in
/-- The inner loop of brute: all `b` for one `a`. -/
def bruteInner (pScan : ℕ) : Stmt := Stmt.for VtxB (v Size) (brutePair pScan)

open Brute in
/-- brute(n, U, ab, bc, ac, fr); the parameter is the procedure number of `scan`. -/
def bruteBody (pScan : ℕ) : Stmt :=
  .set Hit (k 0) ;; Stmt.for VtxA (v Size) (bruteInner pScan) ;; .set 0 (v Hit)

/-- The time of brute. -/
def tBrute (n : ℕ) : ℕ := 100 * n ^ 3 + 100

/-- What brute needs: sums of three weights, no cells, one call. -/
def bruteNeed (_n U : ℕ) : Need := ⟨3 * U + 1, 0, 1⟩

/-- An instance of Exact Triangle gives `scan` what it assumes. -/
theorem _root_.Light.TriInst.Pre.weights {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ} (hpre : x.Pre μ fr)
    (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Weights lim μ x.ab x.bc x.ac x.n x.U x.AB x.BC x.AC where
  hw := hok.space
  hU := by exact_mod_cast hok.word
  arrAB := ⟨hpre.lenAB, hpre.segAB, hpre.leAB, hpre.belowAB.trans hok.cells⟩
  arrBC := ⟨hpre.lenBC, hpre.segBC, hpre.leBC, hpre.belowBC.trans hok.cells⟩
  arrAC := ⟨hpre.lenAC, hpre.segAC, hpre.leAC, hpre.belowAC.trans hok.cells⟩

section

variable {pScan : ℕ} {μ : ℕ → ℤ} {ab bc ac n a U fr : ℕ} {AB BC AC : List ℤ}

/-- One pair: the result so far takes the scan for `(a, b)` in. -/
theorem brutePair_spec {b : ℕ} {hit : Bool} {r : ℤ} (hP : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (hd : d < lim.depth) (ha : a < n) (hb : b < n) :
    Ends lim P d (brutePair pScan) ⟨frame [n, U, ab, bc, ac, fr, a, b, bit hit, r], μ⟩
      (tScan n + 16) fun σ' => ∃ r', σ' = ⟨frame [n, U, ab, bc, ac, fr, a, b,
        bit (hit || scanHit n AB BC AC a b 0 n), r'], μ⟩ := by
  light_facts C C.arrAB C.arrBC C.arrAC
  -- res := scan(ab, bc, ac, n, a, b, 0, n)
  light_call (scan_meets hP C ha hb (c0 := 0) (Nat.zero_add n).le) with _ _ ⟨rfl, rfl⟩
  rw [flag_eq_bit]
  -- if res = 1 then hit := 1
  cases hscan : scanHit n AB BC AC a b 0 n
  · exact Ends.iteLast (fun h => absurd h (by simp [bit])) fun _ => Ends.skip ⟨bit false, by simp⟩
  · exact Ends.iteLast (fun _ => Ends.setTo 1 ⟨bit true, by simp [bit]⟩)
      fun h => absurd h (by simp [bit])

/-- The inner loop: all `b` for one `a`. -/
theorem bruteInner_spec {b₀ r₀ : ℤ} (hP : P[pScan]? = some scanBody)
    (C : Weights lim μ ab bc ac n U AB BC AC) (hd : d < lim.depth) (hn : n ≤ lim.space)
    (ha : a < n) :
    Ends lim P d (bruteInner pScan)
      ⟨frame [n, U, ab, bc, ac, fr, a, b₀, bit (bruteAll n AB BC AC a), r₀], μ⟩
      (n * (24 * n + 59) + 6) fun σ' => ∃ r, σ' = ⟨frame [n, U, ab, bc, ac, fr, a, n,
        bit (bruteAll n AB BC AC (a + 1)), r], μ⟩ := by
  have hw := C.hw
  -- for b < n
  refine Ends.for (fun b σ => ∃ r, σ = ⟨frame [n, U, ab, bc, ac, fr, a, b,
    bit (bruteAll n AB BC AC a || bruteRow n AB BC AC a b), r], μ⟩) n (tScan n + 16)
    ?start ?round ?done ?bound (hT := by simp [tScan]; ring_nf; omega)
  case start => exact ⟨r₀, by simp [update_frame_setLocal, bruteRow]⟩
  case bound =>
    rintro b _ - - ⟨r, rfl⟩
    simp
  case round =>
    rintro b _ hb - ⟨r, rfl⟩
    refine (brutePair_spec hP C hd ha hb).mono le_rfl ?_
    rintro _ ⟨r', rfl⟩
    exact ⟨by simp, r', by simp [update_frame_setLocal, bruteRow_succ, Bool.or_assoc]⟩
  case done =>
    rintro _ - ⟨r, rfl⟩
    exact ⟨r, by rw [bruteAll_succ]⟩

end

/-- The steps of the two loops of brute are within its time. -/
theorem tBrute_ge (n : ℕ) : n * (1 + (n * (24 * n + 59) + 6) + 7) + 10 ≤ tBrute n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tBrute]
  · have hsq : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn (by omega)
    have hlin : n ≤ n ^ 3 := Nat.le_self_pow (by omega) n
    rw [show n * (1 + (n * (24 * n + 59) + 6) + 7) = 24 * n ^ 3 + 59 * n ^ 2 + 14 * n by ring,
      tBrute]
    omega

/-- **The brute force.**  In any program that holds `scanBody` as its procedure number `pScan`,
`bruteBody pScan` ends within `tBrute n` steps, decides whether the instance has a zero triangle,
and changes no cell. -/
theorem brute_spec {pScan : ℕ} (hP : P[pScan]? = some scanBody) (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ)
    (hpre : x.Pre μ fr) (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Ends lim P d (bruteBody pScan) ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr], μ⟩ (tBrute x.n)
      fun σ' => σ'.loc 0 = flag (triOf x.n x.AB x.BC x.AC).HasZeroTriangle ∧ σ'.mem = μ := by
  have C := hpre.weights hok
  have hw := C.hw
  have hd : d < lim.depth := hok.depth
  have hn : x.n ≤ lim.space :=
    (Nat.le_mul_of_pos_left _ hpre.n_pos).trans ((Nat.le_add_left _ _).trans C.arrAB.below)
  have htime := tBrute_ge x.n
  -- hit := 0
  light_set (0 : ℕ)
  -- for a < n
  refine Ends.next _ (Ends.for (fun a σ => ∃ b r, σ = ⟨frame [x.n, x.U, x.ab, x.bc, x.ac, fr, a, b,
    bit (bruteAll x.n x.AB x.BC x.AC a), r], μ⟩) x.n (x.n * (24 * x.n + 59) + 6)
    ?start ?round ?done ?bound (hT := le_rfl)) (by simp; omega)
  case start =>
    exact ⟨0, 0, by simpa [update_frame_setLocal, bruteAll, bit] using
      (frame_append_zeros [(x.n : ℤ), x.U, x.ab, x.bc, x.ac, fr, 0, 0, 0] 1).symm⟩
  case bound =>
    rintro a _ - - ⟨b, r, rfl⟩
    simp
  case round =>
    rintro a _ ha - ⟨b, r, rfl⟩
    refine (bruteInner_spec hP C hd hn ha).mono le_rfl ?_
    rintro _ ⟨r', rfl⟩
    exact ⟨by simp, x.n, r', by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ - ⟨b, r, rfl⟩
    -- return hit
    refine Ends.setTo (bit (hasZero x.n x.AB x.BC x.AC)) ⟨?_, rfl⟩
      (by simp [bruteAll, hasZero, bruteRow]) (by simp; omega)
    exact (flag_eq_bit _).symm.trans (flag_congr (hasZero_iff x.n x.AB x.BC x.AC))

/-- The specification of `brute`, for its callers. -/
theorem brute_meets {p pScan : ℕ} (hB : P[p]? = some (bruteBody pScan))
    (hP : P[pScan]? = some scanBody) (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) (hpre : x.Pre μ fr)
    (hok : (bruteNeed x.n x.U).Ok lim fr d) :
    Meets lim P p d [x.n, x.U, x.ab, x.bc, x.ac, fr] μ (tBrute x.n) fun r μ' =>
      r = flag (triOf x.n x.AB x.BC x.AC).HasZeroTriangle ∧ μ' = μ :=
  Meets.of_body hB (brute_spec hP x μ fr hpre hok)

/-- **brute** solves Exact Triangle. -/
theorem brute_solves : Solves etTask [bruteBody 1, scanBody] 0 (fun n _ => tBrute n) bruteNeed :=
  ⟨bruteBody 1, rfl, fun _ _ _ x μ fr hpre hok =>
    (brute_spec rfl x μ fr hpre hok).mono le_rfl fun _ h => ⟨h.1, fun y _ => by rw [h.2]⟩⟩

end Light.Sec3
