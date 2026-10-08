/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Instance
public import ThreeSumApsp.Programs.Sec2.Theorem5.Stages
public import ThreeSumApsp.Programs.Sec2.Theorem5.Time

/-!
# Theorem 5: the solver

thm5(N, D, w, U, x, y, wi, wj, out, fr) is the algorithm of Section 2.4.4: find m with D = 4^m; the
shared stage (tables, encodings of all row bands and column bands); the tile, the output string and
its digits for every wanted position; the sort by tile and string; the strings in sorted order; the
pruned recursion on every tile that has a wanted position; the report.  The work area begins at the
free pointer fr.

The result is thm5_spec: on an instance of the thin matrix product in the regime of Theorem 5, the
wanted entries of XY end up in the cells from out on, nothing else below fr changes, and the run
takes at most 2 c + 100 times thm5Shape steps, where c is the constant with which the called
procedures meet their entries.  findM_spec treats the search for m; everything after it is
fromShared_ends, which is stated for arbitrary parameters.  tilesShape_le gives the shape of the
time of the pruned recursions, whatever the sorting permutation, and thm5_time compares the sum of
the times with the shape.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

open ThinArg Solver

/-- The search for m with D = 4^m. -/
def findM : Stmt :=
  .while (v Pow4 <' v Cols) (
    .set Pow4 (v Pow4 *' k 4) ;;
    .set Expo (v Expo +' k 1))

/-- thm5(N, D, w, U, x, y, wi, wj, out, fr): the search for m, then the six stages.  Locals 0 to 9
are the arguments.  Everything that is not in a local is read from the directory, which the shared
stage leaves in the 32 cells from fr on. -/
def thm5Body : Stmt :=
  .set Pow4 (k 1) ;;
  findM ;;
  fromShared

/-- What the solver asks of the limits, when it is called at depth d with the free pointer fr: what
the stages ask, for the parameters and the matrices of the instance, and room for 7^{L+1} U. A
bounds the encoded numbers. -/
structure SolverLimits (lim : Limits) (x : ThinInst) (m fr d : ℕ) (A : ℤ) : Prop
  extends StageLimits lim (thm5Par m x.N) (show m ≤ 19 * m by omega) (ThinX x m) (ThinY x m) x.w fr
    d A where
  seven : 7 ^ (19 * m + 1) * (x.U : ℤ) ≤ lim.word

/-- The work of the pruned recursions on all the tiles, for the wanted positions of an instance. -/
def thinWork (x : ThinInst) (m : ℕ) : ℕ :=
  work5 (Spec.stdLayout (show m ≤ 19 * m by omega)) (ThinW x)

/-- The local variables after i rounds of the search for m. -/
def searchLocals (x : ThinInst) (fr : ℕ) (u : ℤ) (i : ℕ) : List ℤ :=
  [(x.N : ℤ), (x.D : ℤ), (x.w : ℤ), u, (x.x : ℤ), (x.y : ℤ), (x.wi : ℤ), (x.wj : ℤ), (x.out : ℤ),
    (fr : ℤ), (i : ℤ), ((4 ^ i : ℕ) : ℤ)]

variable {lim : Limits} {P : Program} {c d : ℕ}

/-- **The search for m**: after i rounds local 10 holds i and local 11 holds 4^i. -/
theorem findM_spec (std : Std lim) (x : ThinInst) (μ : ℕ → ℤ) (fr m : ℕ) (u : ℤ)
    (hD : x.D = 4 ^ m) (hsp : x.D ≤ lim.space) :
    Ends lim P d findM ⟨frame (searchLocals x fr u 0), μ⟩ (12 * m + 4) fun σ' =>
      σ' = ⟨frame (searchLocals x fr u m), μ⟩ := by
  have hw := std.space_le
  have h100 := std.const_le
  unfold findM
  refine Ends.whileBlock (fun i σ => σ = ⟨frame (searchLocals x fr u i), μ⟩) m rfl ?round ?done
  case round =>
    rintro i _ hi rfl
    have hpow : (4 : ℤ) ^ i * 4 ≤ x.D := by
      rw [hD, ← pow_succ]
      exact_mod_cast Nat.pow_le_pow_right (by norm_num) hi
    have hil : (i : ℤ) < 4 ^ i := by exact_mod_cast Nat.lt_pow_self (n := i) (by norm_num : 1 < 4)
    refine ⟨by simp, by simp [searchLocals]; omega, by light_side [searchLocals], ?_⟩
    simp [searchLocals, update_frame_setLocal, pow_succ]
  case done =>
    rintro _ rfl
    exact ⟨by simp, by simp [searchLocals, hD], rfl⟩

/-- The sum of the times of the statements is within the bound. -/
theorem thm5_time (c w : ℕ) (p : Par) (W : ℕ) :
    2 + (12 * p.m + 4 + timeFromShared c p w (p.nB * p.nB + p.nB + 1 + W))
      ≤ (2 * c + 100) * thm5Shape p w W := by
  unfold timeFromShared timeFromWanted timeFromSort timeFromGather timeFromTiles timeReport
    thm5Shape Par.nT
  have hnB : p.nB ≤ p.nB * p.nB + 1 := by
    rcases Nat.eq_zero_or_pos p.nB with h | h
    · omega
    · exact (Nat.le_mul_of_pos_left p.nB h).trans (Nat.le_succ _)
  have hc := Nat.mul_le_mul_left c hnB
  generalize sharedShape p = S, (w + 1) * (p.L + 1) = a, (p.L + 1) * (w + 10) = b,
    p.nB * p.nB = t at *
  have hsort : c * (b + t + 1) = c * b + c * t + c := by ring
  have htiles : c * (t + p.nB + 1 + W) = c * t + c * p.nB + c + c * W := by ring
  have hlist : c * (w + 1) = c * w + c := by ring
  have hc' : c * (t + 1) = c * t + c := by ring
  have hright : (2 * c + 100) * (S + a + (b + t + 1) + (W + t + 1) + (w + 1) + (p.m + 1))
      = 2 * (c * S) + 2 * (c * a) + 2 * (c * b) + 4 * (c * t) + 2 * (c * W) + 2 * (c * w)
        + 2 * (c * p.m) + 8 * c + 100 * (S + a + b + 2 * t + W + w + p.m + 4) := by ring
  omega

/-- The shape of the time of the pruned recursions is nB² + nB + 1 plus thinWork, whatever the
sorting permutation. -/
theorem tilesShape_le {x : ThinInst} {m fr : ℕ} {μ : ℕ → ℤ} (hpre : x.Pre μ fr) (π : List ℕ)
    (h : SortedPre (thm5Par m x.N) x.w (thinI x) (thinJ x) π) :
    tilesShape (thm5Par m x.N).nB (thm5Par m x.N).L
      (tileCodes (thm5Par m x.N) x.w (thinI x) (thinJ x) π)
      ≤ (thm5Par m x.N).nB * (thm5Par m x.N).nB + (thm5Par m x.N).nB + 1 + thinWork x m := by
  refine Nat.add_le_add_left (le_of_eq ?_) _
  refine Finset.sum_congr rfl fun β hβ => Finset.sum_congr rfl fun β' hβ' => ?_
  rw [h.tileCodes_eq_codesOf (Finset.mem_range.mp hβ'),
    thinW_eq_wantedSet hpre]
  rfl

/-- What the shared stage assumes holds for an instance in the regime of Theorem 5. -/
theorem SolverLimits.sharedPre {x : ThinInst} {m fr d : ℕ} {A : ℤ} {μ : ℕ → ℤ}
    (hl : SolverLimits lim x m fr d A) (hpre : x.Pre μ fr) (reg : Regime5 x m) :
    SharedPre lim (thm5Par m x.N) x.x x.y fr (ThinX x m) (ThinY x m) x.U μ := by
  have hpD : (thm5Par m x.N).D = x.D := by rw [reg.hD]; rfl
  exact
    { space := by
        have hsp := hl.space
        have hplaces5 := (thm5Par m x.N).places5 fr x.w
        omega
      matX := matAt_thinX reg.hD hpre
      matY := matAt_thinY reg.hD hpre
      belowX := by rw [hpD]; exact hpre.belowX
      belowY := by rw [hpD]; exact hpre.belowY
      absX := abs_thinX_le hpre
      absY := abs_thinY_le hpre
      seven := hl.seven
      ten := hl.ten }

/-- What the solver of Theorem 5 does in the program P: in the regime of the theorem it leaves the
wanted entries of the product in the cells from out on, changes nothing else below the free pointer,
and takes at most K · thm5Shape steps.  It does not read its fourth argument u (the bound on the
entries). -/
def Solver5 (P : Program) (K : ℕ) : Prop :=
  ∀ (lim : Limits), Std lim → ∀ (d m : ℕ) (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (A u : ℤ),
    x.Pre μ fr → Regime5 x m → SolverLimits lim x m fr d A →
    Ends lim P d thm5Body
      ⟨frame [(x.N : ℤ), (x.D : ℤ), (x.w : ℤ), u, (x.x : ℤ), (x.y : ℤ), (x.wi : ℤ), (x.wj : ℤ),
        (x.out : ℤ), (fr : ℤ)], μ⟩
      (K * thm5Shape (thm5Par m x.N) x.w (thinWork x m)) fun σ' =>
        thinTask.Post x μ fr (σ'.loc 0) σ'.mem

/-- **Theorem 5, the solver**, with the constant 2 c + 100, where c is the constant with which the
called procedures meet their entries. -/
theorem thm5_spec (C : ∀ lim, Std lim → MainCallees lim P c) : Solver5 P (2 * c + 100) := by
  intro lim std d m x μ fr A u hpre reg hl
  have C := C lim std
  have h100 := std.const_le
  have hmL : (thm5Par m x.N).m ≤ (thm5Par m x.N).L := show m ≤ 19 * m by omega
  have hpD : (thm5Par m x.N).D = x.D := by rw [reg.hD]; rfl
  have hpm : (thm5Par m x.N).m = m := rfl
  have hDsp : x.D ≤ lim.space := by
    have hbelow := hpre.belowX
    have hDle : x.D ≤ x.N * x.D := Nat.le_mul_of_pos_left _ hpre.N_pos
    have hsp := hl.space
    have hplaces := (thm5Par m x.N).places fr
    have hplaces5 := (thm5Par m x.N).places5 fr x.w
    omega
  have lims : StageLimits lim (thm5Par m x.N) hmL (ThinX x m) (ThinY x m) x.w fr d A :=
    hl.toStageLimits
  have job : WantedJob (thm5Par m x.N) (ThinX x m) (ThinY x m) x.w x.out fr (thinI x) (thinJ x)
      fun i => thinEntry x.N x.D x.X x.Y (thinI x i) (thinJ x i) :=
    ⟨fun i hi => thinI_lt hpre hi, fun i hi => thinJ_lt hpre hi, thin_inj hpre,
      fun i hi => thinEntry_eq_mul reg.hD ⟨thinI x i, thinI_lt hpre hi⟩
        ⟨thinJ x i, thinJ_lt hpre hi⟩,
      hpre.belowOut⟩
  unfold thm5Body
  refine Ends.mono ?_ (thm5_time c x.w (thm5Par m x.N) (thinWork x m)) fun _ h => h
  -- pow := 1, and the search for m
  light_set 1
  refine Ends.next (12 * m + 4) ((findM_spec std x μ fr m u reg.hD hDsp).mono le_rfl ?_)
  rintro _ rfl
  -- the six stages; the further locals are 0
  have hlocs : frame (searchLocals x fr u m) =
      frame (solverLocals (thm5Par m x.N) x.w u ((thm5Par m x.N).D : ℕ) ((4 ^ m : ℕ) : ℤ) x.x x.y
        x.wi x.wj x.out fr 0 0 0 0 0 0 0) := by
    rw [hpD]
    exact (frame_append_zeros _ 15).symm
  rw [hlocs]
  light_piece (fromShared_ends std C rfl lims job (tilesShape_le hpre) (hl.sharedPre hpre reg)
    (fun i hi => mem_thinI hpre hi) (fun i hi => mem_thinJ hpre hi) hpre.belowWI hpre.belowWJ)
    with σ' ⟨hout, hkept⟩
  refine ⟨fun j hj => ?_, hkept⟩
  have hjw : j < x.w := by rwa [length_thinOut hpre] at hj
  rw [hout j hjw]
  beta_reduce
  rw [← getD_thinOut hpre hjw, List.getD_eq_getElem _ _ hj]

end Light.Sec2
