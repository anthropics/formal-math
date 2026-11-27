import Zeta23.ThmD.Sextuple.PieceCert
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

namespace Zeta23.ThmD.Sextuple.MacroPrototype

open Zeta23.ThmD.Sextuple

abbrev θ : ℝ := Real.sqrt 2 / 2

def mtNum (x : ℝ) : ℝ :=
  (Real.sqrt 2 * Real.cos θ * x) * Real.sin (x / 2) -
    2 * Real.sin θ * Real.cos (x / 2)

def mtNumDeriv (x : ℝ) : ℝ :=
  (Real.sqrt 2 * Real.cos θ + Real.sin θ) * Real.sin (x / 2) +
    ((1 / 2) * (Real.sqrt 2 * Real.cos θ * x)) * Real.cos (x / 2)

def mtNumSecond (x : ℝ) : ℝ :=
  (Real.sqrt 2 * Real.cos θ + (1 / 2) * Real.sin θ) * Real.cos (x / 2) -
    ((1 / 4) * (Real.sqrt 2 * Real.cos θ * x)) * Real.sin (x / 2)

def mtDen (x : ℝ) : ℝ := (x ^ 2 - 2) * Real.sin θ

def mtDenDeriv (x : ℝ) : ℝ := 2 * x * Real.sin θ

def mtDenSecond (_x : ℝ) : ℝ := 2 * Real.sin θ

def mtClosedDeriv (x : ℝ) : ℝ :=
  (mtNumDeriv x * mtDen x - mtNum x * mtDenDeriv x) / mtDen x ^ 2

def mtClosedSecond (x : ℝ) : ℝ :=
  mtNumSecond x / mtDen x - mtNum x * mtDenSecond x / mtDen x ^ 2 -
    2 * mtNumDeriv x * mtDenDeriv x / mtDen x ^ 2 +
    2 * mtNum x * mtDenDeriv x ^ 2 / mtDen x ^ 3

lemma hasDerivAt_mtNum (x : ℝ) : HasDerivAt mtNum (mtNumDeriv x) x := by
  have hhalf : HasDerivAt (fun y : ℝ => y / 2) (1 / 2 : ℝ) x := by
    simpa only [id_eq] using (hasDerivAt_id x).div_const 2
  have hs := hhalf.sin
  have hc := hhalf.cos
  have hxs := (hasDerivAt_id x).mul hs
  have hfirst := hxs.const_mul (Real.sqrt 2 * Real.cos θ)
  have hsecond := hc.const_mul (2 * Real.sin θ)
  have h := (hfirst.sub hsecond).congr_of_eventuallyEq (f₁ := mtNum) (by
    filter_upwards with y
    dsimp [mtNum, θ]
    ring)
  apply h.congr_deriv
  dsimp [mtNumDeriv, θ]
  ring

lemma hasDerivAt_mtNumDeriv (x : ℝ) : HasDerivAt mtNumDeriv (mtNumSecond x) x := by
  have hhalf : HasDerivAt (fun y : ℝ => y / 2) (1 / 2 : ℝ) x := by
    simpa only [id_eq] using (hasDerivAt_id x).div_const 2
  have hs := hhalf.sin
  have hc := hhalf.cos
  have hone := hs.const_mul (Real.sqrt 2 * Real.cos θ + Real.sin θ)
  have hxc := (hasDerivAt_id x).mul hc
  have htwo := hxc.const_mul (Real.sqrt 2 * Real.cos θ / 2)
  have h := (hone.add htwo).congr_of_eventuallyEq (f₁ := mtNumDeriv) (by
    filter_upwards with y
    dsimp [mtNumDeriv, θ]
    ring)
  apply h.congr_deriv
  dsimp [mtNumSecond, θ]
  ring

lemma hasDerivAt_mtDen (x : ℝ) : HasDerivAt mtDen (mtDenDeriv x) x := by
  have hsquare := (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hsub := hsquare.sub (hasDerivAt_const x 2)
  have hraw := hsub.mul_const (Real.sin θ)
  have h := hraw.congr_of_eventuallyEq (f₁ := mtDen) (by
    filter_upwards with y
    dsimp [mtDen, θ]
    ring)
  apply h.congr_deriv
  dsimp [mtDenDeriv, θ]
  ring

lemma hasDerivAt_mtDenDeriv (x : ℝ) : HasDerivAt mtDenDeriv (mtDenSecond x) x := by
  have hraw := (hasDerivAt_id x).const_mul (2 * Real.sin θ)
  have h := hraw.congr_of_eventuallyEq (f₁ := mtDenDeriv) (by
    filter_upwards with y
    dsimp [mtDenDeriv, θ]
    ring)
  apply h.congr_deriv
  dsimp [mtDenSecond, θ]
  ring

lemma sin_θ_pos : 0 < Real.sin θ := by
  have hpos : 0 < θ := by dsimp [θ]; positivity
  have hlt : θ < Real.pi := by
    have hsqrt : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    dsimp [θ]
    nlinarith [Real.pi_gt_three]
  exact Real.sin_pos_of_pos_of_lt_pi hpos hlt

lemma mtDen_ne_zero {x : ℝ} (hx : x ^ 2 ≠ 2) : mtDen x ≠ 0 := by
  exact mul_ne_zero (sub_ne_zero.mpr hx) sin_θ_pos.ne'

lemma hasDerivAt_mtKernelClosed {x : ℝ} (hx : x ^ 2 ≠ 2) :
    HasDerivAt mtKernelClosed (mtClosedDeriv x) x := by
  have hraw := (hasDerivAt_mtNum x).div (hasDerivAt_mtDen x) (mtDen_ne_zero hx)
  have h := hraw.congr_of_eventuallyEq (f₁ := mtKernelClosed) (by
    filter_upwards with y
    dsimp [mtKernelClosed, mtNum, mtDen, θ]
    congr 1
    ring)
  exact h

lemma hasDerivAt_mtClosedDeriv {x : ℝ} (hx : x ^ 2 ≠ 2) :
    HasDerivAt mtClosedDeriv (mtClosedSecond x) x := by
  have hN := hasDerivAt_mtNum x
  have hNp := hasDerivAt_mtNumDeriv x
  have hD := hasDerivAt_mtDen x
  have hDp := hasDerivAt_mtDenDeriv x
  have hU := (hNp.mul hD).sub (hN.mul hDp)
  have hV := hD.mul hD
  have hraw := hU.div hV (mul_ne_zero (mtDen_ne_zero hx) (mtDen_ne_zero hx))
  have h := hraw.congr_of_eventuallyEq (f₁ := mtClosedDeriv) (by
    filter_upwards with y
    dsimp [mtClosedDeriv]
    ring)
  apply h.congr_deriv
  dsimp [mtClosedSecond]
  field_simp [mtDen_ne_zero hx]
  ring

lemma hasDerivAt_mtKernel_of_two_lt {x : ℝ} (hx : 2 < x) :
    HasDerivAt mtKernel (mtClosedDeriv x) x := by
  have hx2 : x ^ 2 ≠ 2 := by nlinarith [sq_nonneg (x - 2)]
  have h := hasDerivAt_mtKernelClosed hx2
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  have hy' : 2 < y := hy
  exact (mtKernel_eq_closed (x := y) (by
    intro hsq
    nlinarith [sq_nonneg y]))


open RatInterval

def mtNumRange (i : RatInterval) (turn : ℕ) : RatInterval :=
  let xt := trigRange (scale (1/2) i) turn
  let a := mul rootTwoInterval thetaTrig.2
  let b := scale 2 thetaTrig.1
  sub (mul (mul a i) xt.1) (mul b xt.2)

def mtNumDerivRange (i : RatInterval) (turn : ℕ) : RatInterval :=
  let xt := trigRange (scale (1/2) i) turn
  let a := mul rootTwoInterval thetaTrig.2
  let first := mul (add a thetaTrig.1) xt.1
  let second := mul (scale (1/2) (mul a i)) xt.2
  add first second

def mtNumSecondRange (i : RatInterval) (turn : ℕ) : RatInterval :=
  let xt := trigRange (scale (1/2) i) turn
  let a := mul rootTwoInterval thetaTrig.2
  let first := mul (add a (scale (1/2) thetaTrig.1)) xt.2
  let second := mul (scale (1/4) (mul a i)) xt.1
  sub first second

def mtDenDerivRange (i : RatInterval) : RatInterval :=
  mul (scale 2 i) thetaTrig.1

def mtDenSecondRange : RatInterval := scale 2 thetaTrig.1

def mtClosedDerivRange (i : RatInterval) (turn : ℕ) : RatInterval :=
  let n := mtNumRange i turn
  let np := mtNumDerivRange i turn
  let d := kernelDenRange i
  let dp := mtDenDerivRange i
  let di := invPos d
  mul (sub (mul np d) (mul n dp)) (mul di di)

def mtClosedSecondRange (i : RatInterval) (turn : ℕ) : RatInterval :=
  let n := mtNumRange i turn
  let np := mtNumDerivRange i turn
  let npp := mtNumSecondRange i turn
  let d := kernelDenRange i
  let dp := mtDenDerivRange i
  let dpp := mtDenSecondRange
  let di := invPos d
  let di2 := mul di di
  let di3 := mul di2 di
  add (sub (sub (mul npp di) (mul (mul n dpp) di2))
      (mul (scale 2 (mul np dp)) di2))
    (mul (scale 2 (mul n (sq dp))) di3)

lemma half_mem {i : RatInterval} {x : ℝ} (hx : Holds i x) :
    Holds (scale (1/2) i) (x/2) := by
  simpa [div_eq_mul_inv, mul_comm] using holds_scale (q := (1/2 : ℚ)) hx

lemma mtNumRange_sound {i : RatInterval} {x : ℝ} (turn : ℕ)
    (hord : i.lo ≤ i.hi)
    (hred : |reducedMid (((scale (1/2) i).lo + (scale (1/2) i).hi)/2) turn| ≤ 1)
    (hx : Holds i x) : Holds (mtNumRange i turn) (mtNum x) := by
  have hhalf := half_mem hx
  have hhalfOrd : (scale (1/2) i).lo ≤ (scale (1/2) i).hi := by
    simp only [scale]
    norm_num
    linarith
  obtain ⟨hsx,hcx⟩ := trigRange_sound turn hhalfOrd hred hhalf
  obtain ⟨hst,hct⟩ := thetaTrig_sound
  have ha := holds_mul rootTwo_mem hct
  have hfirst := holds_mul (holds_mul ha hx) hsx
  have hsecond := holds_mul (holds_scale (q := (2 : ℚ)) hst) hcx
  simpa [mtNumRange, mtNum, θ] using holds_sub hfirst hsecond

lemma mtNumDerivRange_sound {i : RatInterval} {x : ℝ} (turn : ℕ)
    (hord : i.lo ≤ i.hi)
    (hred : |reducedMid (((scale (1/2) i).lo + (scale (1/2) i).hi)/2) turn| ≤ 1)
    (hx : Holds i x) : Holds (mtNumDerivRange i turn) (mtNumDeriv x) := by
  have hhalf := half_mem hx
  have hhalfOrd : (scale (1/2) i).lo ≤ (scale (1/2) i).hi := by
    simp only [scale]
    norm_num
    linarith
  obtain ⟨hsx,hcx⟩ := trigRange_sound turn hhalfOrd hred hhalf
  obtain ⟨hst,hct⟩ := thetaTrig_sound
  have ha := holds_mul rootTwo_mem hct
  have hfirst := holds_mul (holds_add ha hst) hsx
  have hsecond := holds_mul (holds_scale (q := (1/2 : ℚ)) (holds_mul ha hx)) hcx
  simpa [mtNumDerivRange, mtNumDeriv, θ] using holds_add hfirst hsecond

lemma mtNumSecondRange_sound {i : RatInterval} {x : ℝ} (turn : ℕ)
    (hord : i.lo ≤ i.hi)
    (hred : |reducedMid (((scale (1/2) i).lo + (scale (1/2) i).hi)/2) turn| ≤ 1)
    (hx : Holds i x) : Holds (mtNumSecondRange i turn) (mtNumSecond x) := by
  have hhalf := half_mem hx
  have hhalfOrd : (scale (1/2) i).lo ≤ (scale (1/2) i).hi := by
    simp only [scale]
    norm_num
    linarith
  obtain ⟨hsx,hcx⟩ := trigRange_sound turn hhalfOrd hred hhalf
  obtain ⟨hst,hct⟩ := thetaTrig_sound
  have ha := holds_mul rootTwo_mem hct
  have hfirst := holds_mul (holds_add ha (holds_scale (q := (1/2 : ℚ)) hst)) hcx
  have hsecond := holds_mul (holds_scale (q := (1/4 : ℚ)) (holds_mul ha hx)) hsx
  simpa [mtNumSecondRange, mtNumSecond, θ] using holds_sub hfirst hsecond

lemma mtDenDerivRange_sound {i : RatInterval} {x : ℝ} (hx : Holds i x) :
    Holds (mtDenDerivRange i) (mtDenDeriv x) := by
  obtain ⟨hst,_hct⟩ := thetaTrig_sound
  simpa [mtDenDerivRange, mtDenDeriv, θ] using
    holds_mul (holds_scale (q := (2 : ℚ)) hx) hst

lemma mtDenSecondRange_sound : Holds mtDenSecondRange (mtDenSecond 0) := by
  obtain ⟨hst,_hct⟩ := thetaTrig_sound
  simpa [mtDenSecondRange, mtDenSecond, θ] using holds_scale (q := (2 : ℚ)) hst


lemma mtDenRange_sound {i : RatInterval} {x : ℝ} (hx : Holds i x) :
    Holds (kernelDenRange i) (mtDen x) := by
  obtain ⟨hst,_hct⟩ := thetaTrig_sound
  have hx2 := holds_sq hx
  have htwo : Holds (⟨2,2⟩ : RatInterval) (2 : ℝ) := holds_point 2
  simpa [kernelDenRange, mtDen, θ] using holds_mul (holds_sub hx2 htwo) hst

lemma mtClosedDerivRange_sound {i : RatInterval} {x : ℝ} (turn : ℕ)
    (hord : i.lo ≤ i.hi)
    (hred : |reducedMid (((scale (1/2) i).lo + (scale (1/2) i).hi)/2) turn| ≤ 1)
    (hden : (0 : ℚ) < (kernelDenRange i).lo) (hx : Holds i x) :
    Holds (mtClosedDerivRange i turn) (mtClosedDeriv x) := by
  have hn := mtNumRange_sound turn hord hred hx
  have hnp := mtNumDerivRange_sound turn hord hred hx
  have hd := mtDenRange_sound hx
  have hdp := mtDenDerivRange_sound hx
  have hdi := holds_invPos hden hd
  have hu := holds_sub (holds_mul hnp hd) (holds_mul hn hdp)
  have hout := holds_mul hu (holds_mul hdi hdi)
  simpa [mtClosedDerivRange, mtClosedDeriv, div_eq_mul_inv, pow_two] using hout

lemma mtClosedSecondRange_sound {i : RatInterval} {x : ℝ} (turn : ℕ)
    (hord : i.lo ≤ i.hi)
    (hred : |reducedMid (((scale (1/2) i).lo + (scale (1/2) i).hi)/2) turn| ≤ 1)
    (hden : (0 : ℚ) < (kernelDenRange i).lo) (hx : Holds i x) :
    Holds (mtClosedSecondRange i turn) (mtClosedSecond x) := by
  have hn := mtNumRange_sound turn hord hred hx
  have hnp := mtNumDerivRange_sound turn hord hred hx
  have hnpp := mtNumSecondRange_sound turn hord hred hx
  have hd := mtDenRange_sound hx
  have hdp := mtDenDerivRange_sound hx
  have hdpp : Holds mtDenSecondRange (mtDenSecond x) := by
    simpa [mtDenSecond] using mtDenSecondRange_sound
  have hdi := holds_invPos hden hd
  have hdi2 := holds_mul hdi hdi
  have hdi3 := holds_mul hdi2 hdi
  have hfirst := holds_mul hnpp hdi
  have hsecond := holds_mul (holds_mul hn hdpp) hdi2
  have hthird := holds_mul (holds_scale (q := (2 : ℚ)) (holds_mul hnp hdp)) hdi2
  have hfourth := holds_mul (holds_scale (q := (2 : ℚ)) (holds_mul hn (holds_sq hdp))) hdi3
  have hout := holds_add (holds_sub (holds_sub hfirst hsecond) hthird) hfourth
  convert hout using 1
  · simp [mtClosedSecondRange]
  · simp [mtClosedSecond, div_eq_mul_inv, pow_succ]
    ring


lemma left_affine_square_sound {lo hi q σ v m x : ℝ}
    (hlo : 2 < lo) (hxlo : lo ≤ x) (hxhi : x ≤ hi) (hq : q = hi)
    (hv : 0 ≤ v) (hm : 0 ≤ m) (hσ : σ = 1 ∨ σ = -1)
    (hend : v ≤ σ * mtKernel q)
    (hderiv : ∀ y ∈ Set.Icc x q, σ * mtClosedDeriv y ≤ -m) :
    2 * (v + m * (q - x)) ^ 2 ≤ 2 * mtKernel x ^ 2 := by
  have hxq : x ≤ q := by rw [hq]; exact hxhi
  let g : ℝ → ℝ := fun y => σ * mtKernel y + m * y
  have hgHas : ∀ y ∈ Set.Icc x q, HasDerivAt g (σ * mtClosedDeriv y + m) y := by
    intro y hy
    have hy2 : 2 < y := hlo.trans_le (hxlo.trans hy.1)
    have hk := (hasDerivAt_mtKernel_of_two_lt hy2).const_mul σ
    have hid := (hasDerivAt_id y).const_mul m
    have hraw := hk.add hid
    have h := hraw.congr_of_eventuallyEq (f₁ := g) (by
      filter_upwards with z
      dsimp [g])
    apply h.congr_deriv
    ring
  have hgcont : ContinuousOn g (Set.Icc x q) := by
    intro y hy
    exact (hgHas y hy).continuousAt.continuousWithinAt
  have hgdiff : DifferentiableOn ℝ g (interior (Set.Icc x q)) := by
    intro y hy
    exact (hgHas y (interior_subset hy)).differentiableAt.differentiableWithinAt
  have hgder : ∀ y ∈ interior (Set.Icc x q), deriv g y ≤ 0 := by
    intro y hy
    rw [(hgHas y (interior_subset hy)).deriv]
    linarith [hderiv y (interior_subset hy)]
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc x q) hgcont hgdiff hgder
  have hgineq := hanti ⟨le_rfl, hxq⟩ ⟨hxq, le_rfl⟩ hxq
  have hlinear : v + m * (q - x) ≤ |mtKernel x| := by
    dsimp [g] at hgineq
    rcases hσ with rfl | rfl
    · have : v + m * (q - x) ≤ mtKernel x := by linarith
      exact this.trans (le_abs_self _)
    · have : v + m * (q - x) ≤ -mtKernel x := by linarith
      exact this.trans (neg_le_abs _)
  have hnonneg : 0 ≤ v + m * (q - x) := by positivity
  have hsq := (sq_le_sq₀ hnonneg (abs_nonneg _)).2 hlinear
  rw [sq_abs] at hsq
  nlinarith

lemma right_affine_square_sound {lo hi q σ v m x : ℝ}
    (hlo : 2 < lo) (hxlo : lo ≤ x) (_hxhi : x ≤ hi) (hq : q = lo)
    (hv : 0 ≤ v) (hm : 0 ≤ m) (hσ : σ = 1 ∨ σ = -1)
    (hend : v ≤ σ * mtKernel q)
    (hderiv : ∀ y ∈ Set.Icc q x, m ≤ σ * mtClosedDeriv y) :
    2 * (v + m * (x - q)) ^ 2 ≤ 2 * mtKernel x ^ 2 := by
  have hqx : q ≤ x := by rw [hq]; exact hxlo
  let g : ℝ → ℝ := fun y => σ * mtKernel y - m * y
  have hgHas : ∀ y ∈ Set.Icc q x, HasDerivAt g (σ * mtClosedDeriv y - m) y := by
    intro y hy
    have hy2 : 2 < y := by
      apply hlo.trans_le
      rw [← hq]
      exact hy.1
    have hk := (hasDerivAt_mtKernel_of_two_lt hy2).const_mul σ
    have hid := (hasDerivAt_id y).const_mul m
    have hraw := hk.sub hid
    have h := hraw.congr_of_eventuallyEq (f₁ := g) (by
      filter_upwards with z
      dsimp [g])
    apply h.congr_deriv
    ring
  have hgcont : ContinuousOn g (Set.Icc q x) := by
    intro y hy
    exact (hgHas y hy).continuousAt.continuousWithinAt
  have hgdiff : DifferentiableOn ℝ g (interior (Set.Icc q x)) := by
    intro y hy
    exact (hgHas y (interior_subset hy)).differentiableAt.differentiableWithinAt
  have hgder : ∀ y ∈ interior (Set.Icc q x), 0 ≤ deriv g y := by
    intro y hy
    rw [(hgHas y (interior_subset hy)).deriv]
    linarith [hderiv y (interior_subset hy)]
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc q x) hgcont hgdiff hgder
  have hgineq := hmono ⟨le_rfl, hqx⟩ ⟨hqx, le_rfl⟩ hqx
  have hlinear : v + m * (x - q) ≤ |mtKernel x| := by
    dsimp [g] at hgineq
    rcases hσ with rfl | rfl
    · have : v + m * (x - q) ≤ mtKernel x := by linarith
      exact this.trans (le_abs_self _)
    · have : v + m * (x - q) ≤ -mtKernel x := by linarith
      exact this.trans (neg_le_abs _)
  have hnonneg : 0 ≤ v + m * (x - q) := by positivity
  have hsq := (sq_le_sq₀ hnonneg (abs_nonneg _)).2 hlinear
  rw [sq_abs] at hsq
  nlinarith


def absUpper (i : RatInterval) : ℚ := max |i.lo| |i.hi|

lemma abs_le_absUpper {i : RatInterval} {x : ℝ} (hx : Holds i x) :
    |x| ≤ (absUpper i : ℚ) := by
  rw [abs_le]
  constructor
  · have hmax : |i.lo| ≤ absUpper i := le_max_left _ _
    have hcast : ((|i.lo| : ℚ) : ℝ) ≤ (absUpper i : ℚ) := by exact_mod_cast hmax
    have habs : (-(|i.lo| : ℚ) : ℝ) ≤ (i.lo : ℚ) := by
      exact_mod_cast (neg_abs_le i.lo)
    linarith [hx.1]
  · have hmax : |i.hi| ≤ absUpper i := le_max_right _ _
    have hcast : ((|i.hi| : ℚ) : ℝ) ≤ (absUpper i : ℚ) := by exact_mod_cast hmax
    have habs : ((i.hi : ℚ) : ℝ) ≤ (|i.hi| : ℚ) := by
      exact_mod_cast (le_abs_self i.hi)
    linarith [hx.2]

lemma mtClosedDeriv_lipschitz_on {i : RatInterval} (turn : ℕ)
    (hlo : (2 : ℚ) < i.lo) (hord : i.lo ≤ i.hi)
    (hred : |reducedMid (((scale (1/2) i).lo + (scale (1/2) i).hi)/2) turn| ≤ 1)
    (hden : (0 : ℚ) < (kernelDenRange i).lo)
    {x y : ℝ} (hx : Holds i x) (hy : Holds i y) :
    |mtClosedDeriv y - mtClosedDeriv x| ≤
      (absUpper (mtClosedSecondRange i turn) : ℚ) * |y - x| := by
  let s : Set ℝ := Set.Icc (i.lo : ℝ) (i.hi : ℝ)
  have hz2 : ∀ z ∈ s, z ^ 2 ≠ 2 := by
    intro z hz hsq
    have hloR : 2 < (i.lo : ℝ) := by exact_mod_cast hlo
    have hzlo : (i.lo : ℝ) ≤ z := hz.1
    nlinarith [sq_nonneg z]
  have hdiffer : ∀ z ∈ s, DifferentiableAt ℝ mtClosedDeriv z := by
    intro z hz
    exact (hasDerivAt_mtClosedDeriv (hz2 z hz)).differentiableAt
  have hbound : ∀ z ∈ s, ‖deriv mtClosedDeriv z‖ ≤
      (absUpper (mtClosedSecondRange i turn) : ℚ) := by
    intro z hz
    have hzholds : Holds i z := hz
    have hrange := mtClosedSecondRange_sound turn hord hred hden hzholds
    rw [(hasDerivAt_mtClosedDeriv (hz2 z hz)).deriv, Real.norm_eq_abs]
    exact abs_le_absUpper hrange
  have hconv : Convex ℝ s := convex_Icc _ _
  have h := hconv.norm_image_sub_le_of_norm_deriv_le hdiffer hbound hx hy
  simpa only [Real.norm_eq_abs] using h


def boolSign (positive : Bool) : ℝ := if positive then 1 else -1

def orientedLower (positive : Bool) (i : RatInterval) : ℚ :=
  if positive then i.lo else -i.hi

lemma orientedLower_le {positive : Bool} {i : RatInterval} {x : ℝ} (hx : Holds i x) :
    (orientedLower positive i : ℚ) ≤ boolSign positive * x := by
  cases positive with
  | false => simpa [orientedLower, boolSign] using neg_le_neg hx.2
  | true => simpa [orientedLower, boolSign] using hx.1

inductive WellSide where
  | left
  | right
  deriving DecidableEq, Repr

structure WellCert where
  box : RatInterval
  side : WellSide
  positive : Bool
  q : ℚ
  v : ℚ
  m : ℚ
  turn : ℕ
  deriving DecidableEq, Repr

namespace WellCert

def midpoint (p : WellCert) : ℚ := (p.box.lo + p.box.hi) / 2

def radius (p : WellCert) : ℚ := (p.box.hi - p.box.lo) / 2

def point (x : ℚ) : RatInterval := ⟨x,x⟩

def analyticPrereq (i : RatInterval) (turn : ℕ) : Bool :=
  decide (2 < i.lo) && (decide (i.lo ≤ i.hi) &&
  (decide (|reducedMid (((scale (1/2) i).lo + (scale (1/2) i).hi)/2) turn| ≤ 1) &&
  decide (0 < (kernelDenRange i).lo)))

def derivativePositive (p : WellCert) : Bool :=
  match p.side with
  | .left => !p.positive
  | .right => p.positive

def check (p : WellCert) : Bool :=
  analyticPrereq p.box p.turn &&
  (analyticPrereq (point p.midpoint) p.turn &&
  (analyticPrereq (point p.q) p.turn &&
  (decide (0 ≤ p.v) && (decide (0 ≤ p.m) &&
  ((match p.side with
    | .left => decide (p.q = p.box.hi)
    | .right => decide (p.q = p.box.lo)) &&
  (decide (p.v ≤ orientedLower p.positive (kernelRange (point p.q) p.turn)) &&
  decide (p.m + absUpper (mtClosedSecondRange p.box p.turn) * p.radius ≤
    orientedLower p.derivativePositive (mtClosedDerivRange (point p.midpoint) p.turn))))))))

def model (p : WellCert) (x : ℝ) : ℝ :=
  match p.side with
  | .left => 2 * (p.v + p.m * (p.q - x)) ^ 2
  | .right => 2 * (p.v + p.m * (x - p.q)) ^ 2

end WellCert


namespace WellCert

def AnalyticValid (i : RatInterval) (turn : ℕ) : Prop :=
  2 < i.lo ∧ i.lo ≤ i.hi ∧
  |reducedMid (((scale (1/2) i).lo + (scale (1/2) i).hi)/2) turn| ≤ 1 ∧
  0 < (kernelDenRange i).lo

def Valid (p : WellCert) : Prop :=
  AnalyticValid p.box p.turn ∧
  AnalyticValid (point p.midpoint) p.turn ∧
  AnalyticValid (point p.q) p.turn ∧
  0 ≤ p.v ∧ 0 ≤ p.m ∧
  (match p.side with | .left => p.q = p.box.hi | .right => p.q = p.box.lo) ∧
  p.v ≤ orientedLower p.positive (kernelRange (point p.q) p.turn) ∧
  p.m + absUpper (mtClosedSecondRange p.box p.turn) * p.radius ≤
    orientedLower p.derivativePositive (mtClosedDerivRange (point p.midpoint) p.turn)

lemma check_iff_valid (p : WellCert) : p.check = true ↔ p.Valid := by
  rcases p with ⟨box, side, positive, q, v, m, turn⟩
  cases side <;>
    simp [check, Valid, analyticPrereq, AnalyticValid, derivativePositive] <;>
    intros <;> exact decide_eq_true_iff

end WellCert


lemma midpoint_holds {i : RatInterval} (hord : i.lo ≤ i.hi) :
    Holds i ((((i.lo + i.hi) / 2 : ℚ) : ℝ)) := by
  have hlo : i.lo ≤ (i.lo + i.hi) / 2 := by linarith
  have hhi : (i.lo + i.hi) / 2 ≤ i.hi := by linarith
  constructor <;> exact_mod_cast ‹_›

lemma abs_sub_midpoint_le {i : RatInterval} {x : ℝ} (hx : Holds i x) :
    |x - (((i.lo + i.hi) / 2 : ℚ) : ℝ)| ≤ (((i.hi - i.lo) / 2 : ℚ) : ℝ) := by
  rcases hx with ⟨hxlo, hxhi⟩
  rw [abs_le]
  constructor <;> norm_num <;> linarith

lemma absUpper_nonneg (i : RatInterval) : 0 ≤ absUpper i := by
  exact (abs_nonneg i.lo).trans (le_max_left _ _)


namespace WellCert

lemma check_sound {p : WellCert} (hp : p.check = true) {x : ℝ} (hx : Holds p.box x) :
    p.model x ≤ 2 * mtKernel x ^ 2 := by
  have hvalid := (check_iff_valid p).mp hp
  rcases hvalid with ⟨hbox, hmid, hqpoint, hv, hm, hside, hend, hslope⟩
  rcases hbox with ⟨hboxlo, hboxord, hboxred, hboxden⟩
  rcases hmid with ⟨hmidlo, hmidord, hmidred, hmidden⟩
  rcases hqpoint with ⟨hqlo, hqord, hqred, hqden⟩
  have hqholds : Holds (point p.q) (p.q : ℝ) := by
    simp [point]
  have hkq := kernelRange_sound p.turn (le_of_lt hqlo) hqord hqred hqden hqholds
  have hendCast : (p.v : ℝ) ≤ (orientedLower p.positive
      (kernelRange (point p.q) p.turn) : ℚ) := by
    exact_mod_cast hend
  have hendReal : (p.v : ℝ) ≤ boolSign p.positive * mtKernel (p.q : ℝ) :=
    hendCast.trans (orientedLower_le hkq)
  have hmidholds : Holds (point p.midpoint) (p.midpoint : ℝ) := by
    simp [point]
  have hdmid := mtClosedDerivRange_sound p.turn hmidord hmidred hmidden hmidholds
  have hslopeCast : ((p.m + absUpper (mtClosedSecondRange p.box p.turn) * p.radius : ℚ) : ℝ) ≤
      (orientedLower p.derivativePositive
        (mtClosedDerivRange (point p.midpoint) p.turn) : ℚ) := by
    exact_mod_cast hslope
  have hcenter : ((p.m + absUpper (mtClosedSecondRange p.box p.turn) * p.radius : ℚ) : ℝ) ≤
      boolSign p.derivativePositive * mtClosedDeriv (p.midpoint : ℝ) :=
    hslopeCast.trans (orientedLower_le hdmid)
  have hmidbox : Holds p.box (p.midpoint : ℝ) := by
    simpa [midpoint] using midpoint_holds hboxord
  have hM : (0 : ℝ) ≤ (absUpper (mtClosedSecondRange p.box p.turn) : ℚ) := by
    exact_mod_cast absUpper_nonneg (mtClosedSecondRange p.box p.turn)
  have hvR : (0 : ℝ) ≤ (p.v : ℚ) := by exact_mod_cast hv
  have hmR : (0 : ℝ) ≤ (p.m : ℚ) := by exact_mod_cast hm
  have hloR : (2 : ℝ) < (p.box.lo : ℚ) := by exact_mod_cast hboxlo
  cases hsideEq : p.side with
  | left =>
      have hqEq : p.q = p.box.hi := by simpa [hsideEq] using hside
      have hqEqR : (p.q : ℝ) = (p.box.hi : ℚ) := by exact_mod_cast hqEq
      have hσ : boolSign p.positive = 1 ∨ boolSign p.positive = -1 := by
        cases p.positive <;> simp [boolSign]
      have hder : ∀ y ∈ Set.Icc x (p.q : ℝ),
          boolSign p.positive * mtClosedDeriv y ≤ -(p.m : ℝ) := by
        intro y hy
        have hybox : Holds p.box y := by
          constructor
          · exact hx.1.trans hy.1
          · rw [hqEqR] at hy
            exact hy.2
        have hlip := mtClosedDeriv_lipschitz_on p.turn hboxlo hboxord hboxred hboxden hmidbox hybox
        have hdist : |y - (p.midpoint : ℝ)| ≤ (p.radius : ℚ) := by
          simpa [midpoint, radius] using abs_sub_midpoint_le hybox
        have hlip' := hlip.trans (mul_le_mul_of_nonneg_left hdist hM)
        rw [abs_le] at hlip'
        cases hpos : p.positive <;>
          simp [derivativePositive, hsideEq, hpos, boolSign] at hcenter ⊢ <;>
          linarith
      have hsquare := left_affine_square_sound
        (lo := (p.box.lo : ℝ)) (hi := (p.box.hi : ℝ)) (q := (p.q : ℝ))
        (σ := boolSign p.positive) (v := (p.v : ℝ)) (m := (p.m : ℝ))
        hloR hx.1 hx.2 hqEqR hvR hmR hσ hendReal hder
      simpa [model, hsideEq] using hsquare
  | right =>
      have hqEq : p.q = p.box.lo := by simpa [hsideEq] using hside
      have hqEqR : (p.q : ℝ) = (p.box.lo : ℚ) := by exact_mod_cast hqEq
      have hσ : boolSign p.positive = 1 ∨ boolSign p.positive = -1 := by
        cases p.positive <;> simp [boolSign]
      have hder : ∀ y ∈ Set.Icc (p.q : ℝ) x,
          (p.m : ℝ) ≤ boolSign p.positive * mtClosedDeriv y := by
        intro y hy
        have hybox : Holds p.box y := by
          constructor
          · rw [hqEqR] at hy
            exact hy.1
          · exact hy.2.trans hx.2
        have hlip := mtClosedDeriv_lipschitz_on p.turn hboxlo hboxord hboxred hboxden hmidbox hybox
        have hdist : |y - (p.midpoint : ℝ)| ≤ (p.radius : ℚ) := by
          simpa [midpoint, radius] using abs_sub_midpoint_le hybox
        have hlip' := hlip.trans (mul_le_mul_of_nonneg_left hdist hM)
        rw [abs_le] at hlip'
        cases hpos : p.positive <;>
          simp [derivativePositive, hsideEq, hpos, boolSign] at hcenter ⊢ <;>
          linarith
      have hsquare := right_affine_square_sound
        (lo := (p.box.lo : ℝ)) (hi := (p.box.hi : ℝ)) (q := (p.q : ℝ))
        (σ := boolSign p.positive) (v := (p.v : ℝ)) (m := (p.m : ℝ))
        hloR hx.1 hx.2 hqEqR hvR hmR hσ hendReal hder
      simpa [model, hsideEq] using hsquare

end WellCert


inductive MacroPiece where
  | base (p : LowerPiece)
  | well (p : WellCert)
  deriving DecidableEq, Repr

namespace MacroPiece

def box : MacroPiece → RatInterval
  | .base p => p.box
  | .well p => p.box

def model : MacroPiece → ℝ → ℝ
  | .base p => p.model
  | .well p => p.model

def check : MacroPiece → Bool
  | .base p => p.check
  | .well p => p.check

lemma check_sound {p : MacroPiece} (hp : p.check = true) {x : ℝ} (hx : Holds p.box x) :
    p.model x ≤ 2 * mtKernel x ^ 2 := by
  cases p with
  | base p => exact LowerPiece.check_sound hp hx
  | well p => exact WellCert.check_sound hp hx

end MacroPiece

def macroCoverFrom (cur last : ℚ) : List MacroPiece → Bool
  | [] => decide (cur = last)
  | p :: ps => decide (p.box.lo = cur) && decide (p.box.lo ≤ p.box.hi) &&
      macroCoverFrom p.box.hi last ps

def checkMacroPieces (first last : ℚ) (ps : List MacroPiece) : Bool :=
  decide (ps ≠ []) && macroCoverFrom first last ps && ps.all MacroPiece.check

lemma macroCoverFrom_sound {cur last : ℚ} {ps : List MacroPiece} {x : ℝ}
    (hne : ps ≠ []) (hc : macroCoverFrom cur last ps = true)
    (hxlo : (cur : ℝ) ≤ x) (_hxhi : x ≤ (last : ℝ)) :
    ∃ p ∈ ps, Holds p.box x := by
  induction ps generalizing cur with
  | nil => exact (hne rfl).elim
  | cons p ps ih =>
      simp only [macroCoverFrom, Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hfirst, hord⟩, hrest⟩ := hc
      subst cur
      by_cases hx : x ≤ (p.box.hi : ℝ)
      · exact ⟨p, by simp, hxlo, hx⟩
      · cases ps with
        | nil =>
            simp only [macroCoverFrom, decide_eq_true_eq] at hrest
            have hlast : ((p.box.hi : ℚ) : ℝ) = (last : ℝ) := by exact_mod_cast hrest
            exact (hx (by rw [hlast]; assumption)).elim
        | cons next rest =>
            obtain ⟨found, hmem, hholds⟩ := ih (by simp) hrest (le_of_not_ge hx)
            exact ⟨found, by simp [hmem], hholds⟩

theorem checkMacroPieces_sound {first last : ℚ} {ps : List MacroPiece}
    (hc : checkMacroPieces first last ps = true) {x : ℝ}
    (hxlo : (first : ℝ) ≤ x) (hxhi : x ≤ (last : ℝ)) :
    ∃ p ∈ ps, Holds p.box x ∧ p.model x ≤ 2 * mtKernel x ^ 2 := by
  simp only [checkMacroPieces, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨hne, hcover⟩, hall⟩ := hc
  obtain ⟨p, hmem, hp⟩ := macroCoverFrom_sound hne hcover hxlo hxhi
  exact ⟨p, hmem, hp, MacroPiece.check_sound (hall p hmem) hp⟩


end Zeta23.ThmD.Sextuple.MacroPrototype
