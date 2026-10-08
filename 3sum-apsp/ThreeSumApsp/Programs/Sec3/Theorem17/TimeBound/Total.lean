/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec3.Theorem17.Host.Text
public import ThreeSumApsp.Programs.Sec3.Theorem17.TimeBound.Terms

/-!
# The time of the host of Theorem 17 obeys the bound of Theorem 17

Theorem 17 reduces Exact Triangle to at most `4ng` instances "plus O(ν n³ log n/g + n^{ω+o(1)}
D^{3/2} + n² D g) additional time".  The form for programs, `Claim.Theorem_17`, has, here,
Strassen's exponent in the second term; its right side is `bound17`.  The time
function of the host is the time of `4ng` calls of the solver plus a rest, its time over a solver
that takes no time (`hostTime_eq`), and the rest is bounded term by term, up to a constant.

* The parameters, the choice of the prime, the residues, the classes and the chunks are within the
  three terms of the bound (`steps_hostSetup`, `steps_chooseTime`, `steps_tResidues`,
  `steps_tClasses`, `steps_tChunks`).
* Writing the matrices of the instances takes `O(ng) · O(nD)` steps, the third term
  (`steps_instances_mul_tWrites`).
* Reading the answers takes a constant number of steps for each of the at most `n²/√D` query pairs
  of an instance (`steps_tAnswers`).  This is the term `C n²/√D` beside the time of the solver.
* There are at most `F(p) + 1 = O(κ n³ log n/√D)` scans, where `F(p)` is the number of false
  positives of the chosen prime, of `O(√D/g)` steps each: the first term
  (`steps_falsePositiveBound`, `steps_tScanCall`, `steps_scans`).

The sum is `steps_hostRest`, and `obeysBound17_hostTime` puts it into the form of `bound17`.
-/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-! ## The scans -/

/-- One scan looks at the `⌈s/g⌉ ≤ 2√D/g` vertices of a piece, where `s = ⌊√D⌋`, so it takes
`O(√D/g)` steps. -/
private theorem steps_tScanCall :
    Steps (fun θ => tScanCall (pieceSizeNat θ.D θ.g)) fun θ => Real.sqrt θ.D / θ.g := by
  have hone : ∀ θ : CostParams, θ.Hyp → 1 ≤ Real.sqrt θ.D / θ.g := fun θ hθ =>
    (one_le_div hθ.g_pos).2 hθ.hgD
  have hpiece : Steps (fun θ => pieceSizeNat θ.D θ.g) fun θ => Real.sqrt θ.D / θ.g := by
    refine Dominated.of_le_const_mul (C := 2) (by norm_num) fun θ hθ => ?_
    have hlt : (pieceSizeNat θ.D θ.g : ℝ) * θ.g < (Nat.sqrt θ.D : ℝ) + θ.g := by
      exact_mod_cast Nat.ceilDiv_mul_lt (a := Nat.sqrt θ.D) hθ.hg
    rw [← mul_div_assoc, le_div_iff₀ hθ.g_pos]
    -- `⌈s/g⌉ g < s + g ≤ √D + √D`.
    linarith [hlt, Real.nat_sqrt_le_real_sqrt (a := θ.D), hθ.hgD]
  exact (hpiece.const_mul.add (.const hone)).add (.const hone)

/-- The exponent that the host's bound on the false positives uses is at most `κ`. -/
private theorem kappaOf_le_of_hyp {θ : CostParams} (hθ : θ.Hyp) : kappaOf θ.n θ.U ≤ θ.κ := by
  rcases Nat.eq_zero_or_pos θ.U with hU | hU
  · simp [kappaOf, hU, hθ.hκ]
  · exact kappaOf_le ((by norm_num : 2 ≤ 16).trans hθ.sixteen_le_n) hU hθ.hκ hθ.hUn

/-- Proof of Theorem 17: there are at most `F(p) + 1 = O(κ n³ log n/√D)` scans, where `F(p)` is the
number of false positives of the chosen prime `p`.  The host bounds it by `falsePositiveBound`. -/
private theorem steps_falsePositiveBound :
    Steps (fun θ => falsePositiveBound θ.n θ.U θ.D + 1) fun θ =>
      θ.κ * (θ.n : ℝ) ^ 3 * Real.log θ.n / Real.sqrt θ.D := by
  have hconst : 0 ≤ Hashing.falsePositiveConst :=
    zero_le_one.trans Hashing.one_le_falsePositiveConst
  refine Steps.add ?_ (.const fun θ hθ => ?_)
  · -- `falsePositiveBound` is the constant of the false positives times `κ' n³ log n/√D`, rounded
    -- down, where `κ' = kappaOf n U ≤ κ`.
    refine Dominated.of_le_const_mul hconst fun θ hθ => (Nat.floor_le ?_).trans ?_
    · have hκ' : 0 ≤ kappaOf θ.n θ.U := zero_le_one.trans (one_le_kappaOf θ.n θ.U)
      positivity
    · gcongr
      exact kappaOf_le_of_hyp hθ
  · rw [one_le_div hθ.sqrt_pos]
    calc Real.sqrt θ.D ≤ mon 1 0 0 θ := by simpa [mon_eq] using hθ.sqrt_le_n
      _ ≤ mon 3 0 1 θ := Scale.mon_le_mon (by decide) hθ
      _ = θ.κ * (θ.n : ℝ) ^ 3 * Real.log θ.n := by
          rw [mon_eq]
          ring

/-- **The scans**: `O(√D/g) · O(κ n³ log n/√D)` is within the first term of the bound. -/
private theorem steps_scans :
    Steps (fun θ => tScanCall (pieceSizeNat θ.D θ.g) * (falsePositiveBound θ.n θ.U θ.D + 1))
      budget := by
  refine (steps_tScanCall.mul steps_falsePositiveBound).mono_right fun θ hθ =>
    le_trans (le_of_eq ?_) (termScans_le_budget θ)
  have hr : 0 < Real.sqrt θ.D := hθ.sqrt_pos
  have hg : (0 : ℝ) < θ.g := hθ.g_pos
  unfold termScans
  field_simp

/-! ## What is done for each instance -/

/-- The bound `4ng` on the number of instances is `O(ng)`. -/
private theorem steps_instances : Steps (fun θ => 4 * θ.n * θ.g) fun θ => (θ.n : ℝ) * θ.g :=
  (Steps.const_mul (Dominated.refl _ _)).mul (Dominated.refl _ _)

/-- Writing the two matrices of an instance takes `O(nD)` steps. -/
private theorem steps_tWrites :
    StepsMon (fun θ => tWrites θ.n θ.D (pieceSizeNat θ.D θ.g)) 1 2 0 := by
  unfold tWrites
  growth [steps_tWriteX, steps_tWriteY]

/-- Writing the matrices of all instances, `O(ng) · O(nD)`, is within the third term of the bound.
-/
private theorem steps_instances_mul_tWrites :
    Steps (fun θ => 4 * θ.n * θ.g * tWrites θ.n θ.D (pieceSizeNat θ.D θ.g)) budget :=
  (steps_instances.mul (steps_of_softO steps_tWrites)).mono_right fun θ hθ =>
    le_trans (le_of_eq (by
      simp only [termBuild, mon_eq, pow_zero, mul_one, pow_one, Real.sq_sqrt θ.D.cast_nonneg]
      ring)) (termBuild_le_budget hθ)

/-- Reading the answers of one instance takes `O(n²/√D)` steps, a constant number for each query
pair. -/
private theorem steps_tAnswers :
    Steps (fun θ => tAnswers (queryCapNat θ.n θ.D)) fun θ => (θ.n : ℝ) ^ 2 / Real.sqrt θ.D := by
  refine Steps.add (Steps.const_mul (Dominated.of_le fun θ hθ => cast_queryCapNat_le hθ))
    (.const fun θ hθ => ?_)
  rw [one_le_div hθ.sqrt_pos]
  exact hθ.sqrt_le_n.trans (le_self_pow₀ hθ.one_le_n two_ne_zero)

/-! ## The sum -/

/-- The time of the host without the calls of the solver: its time over a solver that takes no time.
-/
private noncomputable def hostRest (tD tG : ℕ → ℕ) (θ : CostParams) : ℕ :=
  hostSetup tD tG θ.n θ.D + hostMain (fun _ => 0) θ.n θ.U θ.D θ.g

private theorem supTime_zero (n D cap : ℕ) : supTime (fun _ => 0) n D cap = 0 := by
  simp [supTime]

/-- Under the hypotheses of Theorem 17 the host does not fall back on the brute force. -/
private theorem not_smallCase_of_hyp {θ : CostParams} (hθ : θ.Hyp) : ¬ SmallCase θ.n θ.D θ.g := by
  have hg : θ.g ≤ Nat.sqrt θ.D := by
    rw [Nat.le_sqrt']
    exact_mod_cast (Real.le_sqrt θ.g.cast_nonneg θ.D.cast_nonneg).1 hθ.hgD
  have hD16 := hθ.hD16
  have hDn := hθ.hDn
  have hg1 := hθ.hg
  unfold SmallCase
  omega

/-- The time of the host is the time of `4ng` calls of the solver plus the rest. -/
private theorem hostTime_eq {θ : CostParams} (hθ : θ.Hyp) {Dfun Gfun : ℕ → ℕ} (tD tG : ℕ → ℕ)
    (Tn : List ℕ → ℕ) (hD : Dfun θ.n = θ.D) (hG : Gfun θ.D = θ.g) :
    hostTime Dfun Gfun tD tG Tn θ.n θ.U
      = 4 * θ.n * θ.g * supTime Tn θ.n θ.D (queryCapNat θ.n θ.D) + hostRest tD tG θ := by
  rw [hostTime, hD, hG, if_neg (not_smallCase_of_hyp hθ), hostRest, hostMain, hostMain,
    hostLoopBound, hostLoopBound, supTime_zero]
  ring

/-- What bounds the time of the host without the calls of the solver: `ng · n²/√D`, for reading the
answers of the instances, plus the three terms of the bound of Theorem 17. -/
private noncomputable def restBound (θ : CostParams) : ℝ :=
  (θ.n : ℝ) * θ.g * ((θ.n : ℝ) ^ 2 / Real.sqrt θ.D) + budget θ

/-- What is within the three terms is within `restBound`. -/
private theorem Steps.toRest {t : CostParams → ℕ} (h : Steps t budget) : Steps t restBound :=
  h.mono_right fun θ _ => le_add_of_nonneg_left (by positivity)

/-- The parameters, the square root of `D` and the tests at the beginning are within the bound, if
the routines that compute `D` and `g` are. -/
private theorem steps_hostSetup {tD tG : ℕ → ℕ} (hD : Steps (fun θ => tD θ.n) budget)
    (hG : Steps (fun θ => tG θ.D) budget) : Steps (fun θ => hostSetup tD tG θ.n θ.D) budget :=
  hD.add hG
  |>.add (by growth [steps_sqrt] : StepsMon _ 0 1 0).withinBuild
  |>.add (Scale.SoftO.const _).withinBuild

/-- The loop over the instances, without the calls of the solver, is within the bound: writing the
matrices, no time for the solver, reading the answers, and the scans. -/
private theorem steps_hostLoopBound :
    Steps (fun θ => hostLoopBound (fun _ => 0) θ.n θ.U θ.D θ.g) restBound :=
  steps_instances_mul_tWrites.toRest
  |>.mul_add ((Scale.SoftO.const 0).withinBuild.toRest.mono_left fun θ _ => by
    rw [supTime_zero, Nat.mul_zero])
  |>.mul_add ((steps_instances.mul steps_tAnswers).mono_right fun _ hθ =>
    le_add_of_nonneg_right (budget_nonneg hθ))
  |>.add steps_scans.toRest
  |>.add (Scale.SoftO.const _).withinBuild.toRest

/-- **Everything but the calls of the solver** is within the bound, if the routines that compute `D`
and `g` are.  The summands stand in the order of `hostMain`. -/
private theorem steps_hostRest {tD tG : ℕ → ℕ} (hD : Steps (fun θ => tD θ.n) budget)
    (hG : Steps (fun θ => tG θ.D) budget) : Steps (hostRest tD tG) restBound :=
  (steps_hostSetup hD hG).toRest.add <|
    steps_chooseTime.toRest
    |>.add steps_tQueryCapNat.withinBuild.toRest
    |>.add steps_tCeilDiv_piece.withinBuild.toRest
    |>.add steps_tCeilDiv_num.withinBuild.toRest
    |>.add steps_tBitLen.withinScans.toRest
    |>.add steps_tDblTable.withinScans.toRest
    |>.add ((Scale.SoftO.const _).mul steps_tResidues).withinScans.toRest
    |>.add steps_tClasses.withinBuild.toRest
    |>.add steps_tChunks.withinBuild.toRest
    |>.add steps_hostLoopBound
    |>.add (Scale.SoftO.const _).withinBuild.toRest

/-- A bound `T` on the time of the solver that is monotone in the number of query pairs bounds its
largest time on the instances of the host. -/
private theorem cast_supTime_le {Tn : List ℕ → ℕ} {T : ℕ → ℕ → ℕ → ℝ}
    (hT : ∀ n D w w' : ℕ, 1 ≤ n → 1 ≤ D → w ≤ w' → (Tn [n, D, w] : ℝ) ≤ T n D w') {n D : ℕ}
    (hn : 1 ≤ n) (hD : 1 ≤ D) (cap : ℕ) : ((supTime Tn n D cap : ℕ) : ℝ) ≤ T n D cap := by
  obtain ⟨w, hw, hsup⟩ : ∃ w ∈ Finset.range (cap + 1),
      (Finset.range (cap + 1)).sup (fun w => Tn [n, D, w]) = Tn [n, D, w] :=
    Finset.exists_mem_eq_sup _ ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ _
  rw [supTime, hsup]
  exact hT n D w cap hn hD (Nat.lt_succ_iff.1 (Finset.mem_range.1 hw))

/-- **The bound of Theorem 17 for the host.**  The parameter routines compute `Dfun n` from `n` and
`Gfun D` from `D`.  These agree with the parameters `D n` and `g n` of the claim, which are defined
with real powers, and the routines run within the bound. -/
theorem obeysBound17_hostTime (D g : ℕ → ℕ) {Dfun Gfun tD tG : ℕ → ℕ} (hDf : ∀ n, Dfun n = D n)
    (hGf : ∀ n, 1 ≤ n → Gfun (D n) = g n) (hD : Steps (fun θ => tD θ.n) budget)
    (hG : Steps (fun θ => tG θ.D) budget) :
    ObeysBound17 strassen D g (hostTime Dfun Gfun tD tG) := by
  obtain ⟨C, hC, hsteps⟩ := steps_hostRest hD hG
  refine ⟨C, hC, fun Tn T hT n U κ h16 hDn hg1 hg hκ hU => ?_⟩
  have hθ : CostParams.Hyp ⟨n, D n, g n, U, κ⟩ := ⟨h16, hDn, hg1, hg, hκ, hU⟩
  have hn1 : 1 ≤ n := hθ.one_le_n_nat
  have hD1 : 1 ≤ D n := hθ.one_le_D_nat
  have hsolver := cast_supTime_le hT hn1 hD1 (queryCapNat n (D n))
  have hrest : (hostRest tD tG ⟨n, D n, g n, U, κ⟩ : ℝ)
      ≤ C * ((n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n)) + budget ⟨n, D n, g n, U, κ⟩) :=
    hsteps _ hθ
  have hquery : 0 ≤ C * ((n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n))) := by positivity
  rw [hostTime_eq hθ tD tG Tn (hDf n) (hGf n hn1)]
  rw [queryCapNat_eq n hD1] at hsolver ⊢
  push_cast
  -- The calls cost `4ng T`; in the rest, `C ng · n²/√D ≤ 4ng · C n²/√D`.
  calc 4 * (n : ℝ) * g n * (supTime Tn n (D n) (queryCap n (D n)) : ℝ)
        + (hostRest tD tG ⟨n, D n, g n, U, κ⟩ : ℝ)
      ≤ 4 * (n : ℝ) * g n * T n (D n) (queryCap n (D n))
        + C * ((n : ℝ) * g n * ((n : ℝ) ^ 2 / Real.sqrt (D n)) + budget ⟨n, D n, g n, U, κ⟩) := by
        gcongr
    _ ≤ bound17 strassen D g C T n κ := by
        unfold bound17 budget
        linarith [hquery]

end Light.Sec3
