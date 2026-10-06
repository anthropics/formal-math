/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ZeroSide.SextuplePenalty
import Zeta23.Assembly
import Zeta23.Tail

/-!
# Ordered simple zeros in the interior of the dyadic window

This file indexes the simple critical-line zeros with ordinates in
`(T + 1, 2 * T - 1]`, orders them by ordinate, and records the finite gap and
endpoint bookkeeping used by the sextuple argument.
-/

noncomputable section

open Finset Filter Asymptotics Topology Real
open scoped BigOperators

namespace Zeta23
namespace ThmD
namespace Sextuple

/-- The global simple-zero column index of the concrete Gram matrix. -/
abbrev GlobalSimpleIndex (Z : ZeroConfig) (T : ℝ) (P : Params) :=
  (ZeroSide.sextupleBlockData Z T P).S₁

/-- The simple critical-line columns whose ordinates lie in the strict
one-unit interior `(T + 1, 2T - 1]`. -/
def interiorSimpleIndices (Z : ZeroConfig) (T : ℝ) (P : Params) :
    Finset (GlobalSimpleIndex Z T P) :=
  Finset.univ.filter fun z => T + 1 < (z.1 : ℂ).im ∧ (z.1 : ℂ).im ≤ 2 * T - 1

/-- Number of simple critical-line columns in the one-unit interior. -/
def sInterior (Z : ZeroConfig) (T : ℝ) (P : Params) : ℕ :=
  (interiorSimpleIndices Z T P).card

/-- The global simple Gram index has the expected zero-count cardinality. -/
theorem globalSimpleIndex_card (Z : ZeroConfig) (T : ℝ) (P : Params) :
    Fintype.card (GlobalSimpleIndex Z T P) = Z.s1 T := by
  have hs : Z.s1 T = (ZeroSide.sextupleBlockData Z T P).s₁ := by
    change Z.s1 T = (ZeroSide.mkData Z T (ZeroSide.evalVec Z T P)
      (ZeroSide.evalVec_reflect (fun z => GzGp.phiHat_conj P T z))).s₁
    exact ZeroSide.s1_eq_mk Z T _ _
  simpa only [GlobalSimpleIndex, Fintype.card_coe,
    ZeroSide.ZeroBlockData.s₁] using hs.symm

private lemma globalSimple_re_eq_half (Z : ZeroConfig) (T : ℝ) (P : Params)
    (z : GlobalSimpleIndex Z T P) : (z.1 : ℂ).re = 1 / 2 := by
  have hz' : (ZeroSide.sextupleBlockData Z T P).σ z.1 = z.1 ∧
      (ZeroSide.sextupleBlockData Z T P).m z.1 = 1 := by
    simpa only [ZeroSide.ZeroBlockData.S₁, Finset.mem_filter,
      Finset.mem_univ, true_and] using z.2
  have hz : (ZeroSide.sextupleBlockData Z T P).σ z.1 = z.1 := hz'.1
  change (ZeroSide.mkData Z T (ZeroSide.evalVec Z T P)
    (ZeroSide.evalVec_reflect (fun w => GzGp.phiHat_conj P T w))).σ z.1 = z.1 at hz
  exact (ZeroSide.mkData_σ_eq_iff Z T _ _ z.1).mp hz

/-- Distinct global simple critical-line columns have distinct ordinates. -/
theorem globalSimple_ordinate_injective (Z : ZeroConfig) (T : ℝ) (P : Params) :
    Function.Injective (fun z : GlobalSimpleIndex Z T P => (z.1 : ℂ).im) := by
  intro z w hzw
  apply Subtype.ext
  apply Subtype.ext
  exact Complex.ext (by rw [globalSimple_re_eq_half Z T P z,
    globalSimple_re_eq_half Z T P w]) hzw

/-- The ordinate map on the global simple Gram index, as an embedding. -/
def globalSimpleOrdinateEmbedding (Z : ZeroConfig) (T : ℝ) (P : Params) :
    GlobalSimpleIndex Z T P ↪ ℝ where
  toFun z := (z.1 : ℂ).im
  inj' := globalSimple_ordinate_injective Z T P

/-- The finite set of real ordinates in the one-unit interior. -/
def interiorOrdinates (Z : ZeroConfig) (T : ℝ) (P : Params) : Finset ℝ :=
  (interiorSimpleIndices Z T P).map (globalSimpleOrdinateEmbedding Z T P)

/-- The canonical increasing order on the finite interior ordinate set. -/
def interiorOrder (Z : ZeroConfig) (T : ℝ) (P : Params) :
    Fin (sInterior Z T P) ≃o ↥(interiorOrdinates Z T P) :=
  Finset.orderIsoOfFin (interiorOrdinates Z T P) (by
    simp [sInterior, interiorOrdinates])

/-- The `i`-th interior ordinate in increasing order. -/
def orderedOrdinate (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : Fin (sInterior Z T P)) : ℝ :=
  (interiorOrder Z T P i : ℝ)

/-- The `i`-th ordered interior zero, still carrying its global Gram index. -/
def orderedInteriorZero (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : Fin (sInterior Z T P)) : ↥(interiorSimpleIndices Z T P) :=
  (Finset.equivMap (globalSimpleOrdinateEmbedding Z T P)
    (interiorSimpleIndices Z T P)).symm (interiorOrder Z T P i)

@[simp] theorem orderedInteriorZero_ordinate (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : Fin (sInterior Z T P)) :
    ((orderedInteriorZero Z T P i).1.1 : ℂ).im = orderedOrdinate Z T P i := by
  have h := (Finset.equivMap (globalSimpleOrdinateEmbedding Z T P)
    (interiorSimpleIndices Z T P)).apply_symm_apply (interiorOrder Z T P i)
  exact congrArg Subtype.val h

/-- The ordered interior points embedded into the global simple Gram index. -/
def interiorGramEmbedding (Z : ZeroConfig) (T : ℝ) (P : Params) :
    Fin (sInterior Z T P) ↪ GlobalSimpleIndex Z T P where
  toFun i := (orderedInteriorZero Z T P i).1
  inj' := fun i j h => by
    apply (interiorOrder Z T P).injective
    apply (Finset.equivMap (globalSimpleOrdinateEmbedding Z T P)
      (interiorSimpleIndices Z T P)).symm.injective
    exact Subtype.ext h

@[simp] theorem interiorGramEmbedding_ordinate (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : Fin (sInterior Z T P)) :
    ((interiorGramEmbedding Z T P i).1 : ℂ).im = orderedOrdinate Z T P i :=
  orderedInteriorZero_ordinate Z T P i

/-- The ordered ordinate list is strictly increasing. -/
theorem orderedOrdinate_strictMono (Z : ZeroConfig) (T : ℝ) (P : Params) :
    StrictMono (orderedOrdinate Z T P) := by
  intro i j hij
  exact (interiorOrder Z T P).lt_iff_lt.mpr hij

/-- In particular, the ordered ordinate map is injective. -/
theorem orderedOrdinate_injective (Z : ZeroConfig) (T : ℝ) (P : Params) :
    Function.Injective (orderedOrdinate Z T P) :=
  (orderedOrdinate_strictMono Z T P).injective

/-- Every ordered ordinate lies above the lower interior endpoint. -/
theorem orderedOrdinate_lower (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : Fin (sInterior Z T P)) : T + 1 < orderedOrdinate Z T P i := by
  have hi := (orderedInteriorZero Z T P i).2
  simp only [interiorSimpleIndices, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi
  simpa using hi.1

/-- Every ordered ordinate lies at or below the upper interior endpoint. -/
theorem orderedOrdinate_upper (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : Fin (sInterior Z T P)) : orderedOrdinate Z T P i ≤ 2 * T - 1 := by
  have hi := (orderedInteriorZero Z T P i).2
  simp only [interiorSimpleIndices, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi
  simpa using hi.2

/-- The left endpoint of an adjacent gap, viewed as a point index. -/
def gapLeftIndex {s : ℕ} (i : Fin (s - 1)) : Fin s :=
  ⟨i, by have := i.isLt; omega⟩

/-- The right endpoint of an adjacent gap, viewed as a point index. -/
def gapRightIndex {s : ℕ} (i : Fin (s - 1)) : Fin s :=
  ⟨i + 1, by have := i.isLt; omega⟩

/-- The normalized adjacent gap `L(T) (γ_{i+1} - γ_i)`. -/
def adjacentGap (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : Fin (sInterior Z T P - 1)) : ℝ :=
  P.L T * (orderedOrdinate Z T P (gapRightIndex i) -
    orderedOrdinate Z T P (gapLeftIndex i))

/-- Every adjacent ordinate difference is positive. -/
theorem adjacentOrdinateDiff_pos (Z : ZeroConfig) (T : ℝ) (P : Params)
    (i : Fin (sInterior Z T P - 1)) :
    0 < orderedOrdinate Z T P (gapRightIndex i) -
      orderedOrdinate Z T P (gapLeftIndex i) := by
  rw [sub_pos]
  apply orderedOrdinate_strictMono Z T P
  exact Fin.mk_lt_mk.mpr (by omega)

/-- Normalized adjacent gaps are nonnegative when `L(T)` is nonnegative. -/
theorem adjacentGap_nonneg (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hL : 0 ≤ P.L T) (i : Fin (sInterior Z T P - 1)) :
    0 ≤ adjacentGap Z T P i :=
  mul_nonneg hL (adjacentOrdinateDiff_pos Z T P i).le

/-- The final point index of a nonempty finite list. -/
def lastPointIndex {s : ℕ} (hs : 0 < s) : Fin s :=
  ⟨s - 1, Nat.sub_lt hs (by norm_num)⟩

private theorem sum_adjacent_diff {s : ℕ} (hs : 0 < s) (γ : Fin s → ℝ) :
    (∑ i : Fin (s - 1),
      (γ (gapRightIndex i) - γ (gapLeftIndex i))) =
      γ (lastPointIndex hs) - γ ⟨0, hs⟩ := by
  let f : ℕ → ℝ := fun i => if hi : i < s then γ ⟨i, hi⟩ else 0
  calc
    (∑ i : Fin (s - 1),
        (γ (gapRightIndex i) - γ (gapLeftIndex i))) =
        ∑ i ∈ Finset.range (s - 1), (f (i + 1) - f i) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < s - 1 := Finset.mem_range.mp hi
      have his : i < s := by omega
      have hisucc : i + 1 < s := by omega
      simp only [dif_pos hi', f, dif_pos his, dif_pos hisucc, gapLeftIndex,
        gapRightIndex]
    _ = f (s - 1) - f 0 := Finset.sum_range_sub f (s - 1)
    _ = γ (lastPointIndex hs) - γ ⟨0, hs⟩ := by
      have hlast : s - 1 < s := Nat.sub_lt hs (by norm_num)
      simp only [f, dif_pos hlast, dif_pos hs]
      congr 2

/-- For a nonempty interior list, the adjacent gaps telescope exactly from the
first to the last ordinate.  This includes the one-point case. -/
theorem sum_adjacentGap_eq (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hs : 0 < sInterior Z T P) :
    (∑ i : Fin (sInterior Z T P - 1), adjacentGap Z T P i) =
      P.L T * (orderedOrdinate Z T P (lastPointIndex hs) -
        orderedOrdinate Z T P ⟨0, hs⟩) := by
  simp_rw [adjacentGap]
  rw [← Finset.mul_sum]
  exact congrArg (P.L T * ·)
    (sum_adjacent_diff hs (orderedOrdinate Z T P))

/-- The total normalized adjacent-gap length is at most `L(T) T`, with the
empty and one-point cases handled without extra cardinality assumptions. -/
theorem sum_adjacentGap_le (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hL : 0 ≤ P.L T) (hT : 0 ≤ T) :
    (∑ i : Fin (sInterior Z T P - 1), adjacentGap Z T P i) ≤ P.L T * T := by
  by_cases hs : 0 < sInterior Z T P
  · rw [sum_adjacentGap_eq Z T P hs]
    apply mul_le_mul_of_nonneg_left _ hL
    have hlo := orderedOrdinate_lower Z T P (⟨0, hs⟩ : Fin (sInterior Z T P))
    have hup := orderedOrdinate_upper Z T P (lastPointIndex hs)
    linarith
  · have hs0 : sInterior Z T P = 0 := by omega
    have hempty : ∀ i : Fin (sInterior Z T P - 1), False := by
      intro i
      have := i.isLt
      omega
    have hsum : (∑ i : Fin (sInterior Z T P - 1), adjacentGap Z T P i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact (hempty i).elim
    rw [hsum]
    exact mul_nonneg hL hT

/-! ## Interior count and endpoint bookkeeping -/

/-- The same interior simple zeros, represented directly as a finset of
complex numbers. -/
def interiorSimpleZeros (Z : ZeroConfig) (T : ℝ) : Finset ℂ :=
  (ZeroSide.ZI Z T).filter fun ρ =>
    T + 1 < ρ.im ∧ ρ.im ≤ 2 * T - 1 ∧ ρ.re = 1 / 2 ∧ Z.mult ρ = 1

/-- Forgetting the Gram-index proofs identifies the two finite interior
index sets. -/
theorem card_interiorSimpleIndices_eq (Z : ZeroConfig) (T : ℝ) (P : Params) :
    (interiorSimpleIndices Z T P).card = (interiorSimpleZeros Z T).card := by
  apply Finset.card_bij (fun z _ => (z.1 : ℂ))
  · intro z hz
    simp only [interiorSimpleIndices, Finset.mem_filter, Finset.mem_univ,
      true_and] at hz
    have hzS := z.2
    simp only [ZeroSide.ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ,
      true_and] at hzS
    have hm := hzS.2
    change Z.mult (z.1 : ℂ) = 1 at hm
    exact Finset.mem_filter.mpr ⟨z.1.2, hz.1, hz.2,
      globalSimple_re_eq_half Z T P z, hm⟩
  · intro z _ w _ h
    exact Subtype.ext (Subtype.ext h)
  · intro ρ hρ
    simp only [interiorSimpleZeros, Finset.mem_filter] at hρ
    let zI : ZeroSide.ZI Z T := ⟨ρ, hρ.1⟩
    have hzσ : (ZeroSide.sextupleBlockData Z T P).σ zI = zI := by
      change (ZeroSide.mkData Z T (ZeroSide.evalVec Z T P)
        (ZeroSide.evalVec_reflect (fun w => GzGp.phiHat_conj P T w))).σ zI = zI
      exact (ZeroSide.mkData_σ_eq_iff Z T _ _ zI).mpr hρ.2.2.2.1
    have hzm : (ZeroSide.sextupleBlockData Z T P).m zI = 1 := by
      change Z.mult ρ = 1
      exact hρ.2.2.2.2
    let z : GlobalSimpleIndex Z T P := ⟨zI, by
      simp only [ZeroSide.ZeroBlockData.S₁, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact ⟨hzσ, hzm⟩⟩
    refine ⟨z, ?_, rfl⟩
    simp only [interiorSimpleIndices, Finset.mem_filter, Finset.mem_univ,
      true_and, z, zI]
    exact ⟨hρ.2.1, hρ.2.2.1⟩

/-- The direct interior finset is exactly the simple critical-line window
`(T+1, 2T-1]`. -/
theorem coe_interiorSimpleZeros (Z : ZeroConfig) (T : ℝ) :
    (↑(interiorSimpleZeros Z T) : Set ℂ) =
      Z.window (T + 1) (2 * T - 1) ∩ ZeroConfig.onLine ∩ Z.simple := by
  ext ρ
  constructor
  · intro hρ
    simp only [interiorSimpleZeros, Finset.coe_filter, Set.mem_ofPred_eq] at hρ
    rcases hρ with ⟨hZI, hlo, hup, hre, hm⟩
    have hcar := ZeroSide.mem_carrier_of_mem_ZI Z T hZI
    exact ⟨⟨⟨hcar, ⟨hlo, hup⟩⟩, hre⟩, hm⟩
  · intro hρ
    rcases hρ with ⟨⟨⟨hcar, hlo, hup⟩, hre⟩, hm⟩
    have hD0 := Assembly.D0_nonneg (T := T)
    have hZIprime : ρ ∈ Z.ZIprime T :=
      (ZeroSide.mem_ZIprime_iff Z T).mpr ⟨hcar, by linarith, by linarith⟩
    simp only [interiorSimpleZeros, Finset.coe_filter, Set.mem_ofPred_eq]
    exact ⟨(ZeroSide.mem_ZI Z T).mpr hZIprime, hlo, hup, hre, hm⟩

/-- The interior cardinality is the standard simple-zero count on the smaller
physical window. -/
theorem sInterior_eq_N0s (Z : ZeroConfig) (T : ℝ) (P : Params) :
    sInterior Z T P = Z.N0s (T + 1) (2 * T - 1) := by
  rw [sInterior, card_interiorSimpleIndices_eq Z T P, ZeroConfig.N0s,
    ← coe_interiorSimpleZeros Z T, Set.ncard_coe_finset]

/-- The global simple Gram columns omitted from the one-unit interior. -/
def omittedSimpleIndices (Z : ZeroConfig) (T : ℝ) (P : Params) :
    Finset (GlobalSimpleIndex Z T P) :=
  Finset.univ \ interiorSimpleIndices Z T P

/-- Number of global simple Gram columns omitted from the one-unit interior. -/
def omittedSimpleCount (Z : ZeroConfig) (T : ℝ) (P : Params) : ℕ :=
  Z.s1 T - sInterior Z T P

/-- `omittedSimpleCount` is the cardinality of the actual complementary
finset of Gram columns. -/
theorem card_omittedSimpleIndices (Z : ZeroConfig) (T : ℝ) (P : Params) :
    (omittedSimpleIndices Z T P).card = omittedSimpleCount Z T P := by
  rw [omittedSimpleIndices, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ]
  rw [globalSimpleIndex_card Z T P]
  rfl

/-- The omitted simple columns are covered by the two endpoint unit layers and
the part of `I'` outside the physical dyadic interval. -/
theorem omittedSimpleCount_le (Z : ZeroConfig) (T : ℝ) (P : Params)
    (hT : 2 ≤ T) :
    omittedSimpleCount Z T P ≤ Assembly.NII Z T +
      Z.N T (T + 1) + Z.N (2 * T - 1) (2 * T) := by
  have hT0 : 0 ≤ T := by linarith
  have h₁ : T ≤ T + 1 := by linarith
  have h₂ : T + 1 ≤ 2 * T - 1 := by linarith
  have h₃ : 2 * T - 1 ≤ 2 * T := by linarith
  have hs1 := Assembly.s1_le Z hT0
  have hsplit₁ := Assembly.N0s_add Z h₁ (h₂.trans h₃)
  have hsplit₂ := Assembly.N0s_add Z h₂ h₃
  have hmiddle := sInterior_eq_N0s Z T P
  have hleft : Z.N0s T (T + 1) ≤ Z.N T (T + 1) :=
    ((Z.trivial_chain T (T + 1)).1.trans
      (Z.trivial_chain T (T + 1)).2.1).trans
        (Z.trivial_chain T (T + 1)).2.2.1
  have hright : Z.N0s (2 * T - 1) (2 * T) ≤ Z.N (2 * T - 1) (2 * T) :=
    ((Z.trivial_chain (2 * T - 1) (2 * T)).1.trans
      (Z.trivial_chain (2 * T - 1) (2 * T)).2.1).trans
        (Z.trivial_chain (2 * T - 1) (2 * T)).2.2.1
  unfold omittedSimpleCount
  omega

/-- Under H-RvM, the simple columns lost at the two unit endpoints and outside
the physical interval form `o(N(T,2T))`. -/
theorem omittedSimpleCount_isLittleO (Z : ZeroConfig) (P : Params)
    (H : PaperInputs Z) :
    (fun T => (omittedSimpleCount Z T P : ℝ)) =o[atTop]
      fun T => (Z.N T (2 * T) : ℝ) := by
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  obtain ⟨CII, hII⟩ := Tail.eventually_NII_le Z hA₀ hloc
  have hO : (fun T => (omittedSimpleCount Z T P : ℝ)) =O[atTop]
      (fun T => Real.sqrt T * l T) := by
    refine IsBigO.of_bound (|CII| + 4 * A₀) ?_
    filter_upwards [hII, eventually_ge_atTop Tail.T₀,
      eventually_ge_atTop (2 : ℝ), Assembly.eventually_l_pos]
        with T hII_T hT₀ hT2 hl
    have hT0 : 0 ≤ T := by linarith
    have hcover := omittedSimpleCount_le Z T P hT2
    have hcoverR : (omittedSimpleCount Z T P : ℝ) ≤
        (Assembly.NII Z T : ℝ) + (Z.N T (T + 1) : ℝ) +
          (Z.N (2 * T - 1) (2 * T) : ℝ) := by
      exact_mod_cast hcover
    have habsT : |T| = T := abs_of_nonneg hT0
    have habs2T : |2 * T - 1| = 2 * T - 1 := abs_of_nonneg (by linarith)
    have hlogLeft : Real.log (|T| + 3) ≤ Real.log (4 * T) := by
      apply Real.log_le_log (by positivity)
      rw [habsT]
      linarith
    have hlogRight : Real.log (|2 * T - 1| + 3) ≤ Real.log (4 * T) := by
      apply Real.log_le_log (by positivity)
      rw [habs2T]
      linarith
    have hlog4 := Tail.log_four_mul_le_two_mul_l hT₀
    have hleft : (Z.N T (T + 1) : ℝ) ≤ 2 * A₀ * l T := by
      calc
        (Z.N T (T + 1) : ℝ) ≤ A₀ * Real.log (|T| + 3) := hloc T
        _ ≤ A₀ * Real.log (4 * T) :=
          mul_le_mul_of_nonneg_left hlogLeft (by linarith)
        _ ≤ A₀ * (2 * l T) :=
          mul_le_mul_of_nonneg_left hlog4 (by linarith)
        _ = 2 * A₀ * l T := by ring
    have hrightRaw := hloc (2 * T - 1)
    have hrightEndpoint : 2 * T - 1 + 1 = 2 * T := by ring
    have hrightLocal : (Z.N (2 * T - 1) (2 * T) : ℝ) ≤
        A₀ * Real.log (|2 * T - 1| + 3) := by
      simpa only [hrightEndpoint] using hrightRaw
    have hright : (Z.N (2 * T - 1) (2 * T) : ℝ) ≤ 2 * A₀ * l T := by
      calc
        (Z.N (2 * T - 1) (2 * T) : ℝ) ≤
            A₀ * Real.log (|2 * T - 1| + 3) := hrightLocal
        _ ≤ A₀ * Real.log (4 * T) :=
          mul_le_mul_of_nonneg_left hlogRight (by linarith)
        _ ≤ A₀ * (2 * l T) :=
          mul_le_mul_of_nonneg_left hlog4 (by linarith)
        _ = 2 * A₀ * l T := by ring
    have hfactor : 0 ≤ Real.sqrt T * l T := mul_nonneg (Real.sqrt_nonneg T) hl.le
    have hIIabs : (Assembly.NII Z T : ℝ) ≤ |CII| * (Real.sqrt T * l T) := by
      calc
        (Assembly.NII Z T : ℝ) ≤ CII * Real.sqrt T * l T := hII_T
        _ = CII * (Real.sqrt T * l T) := by ring
        _ ≤ |CII| * (Real.sqrt T * l T) :=
          mul_le_mul_of_nonneg_right (le_abs_self CII) hfactor
    have hsqrt : 1 ≤ Real.sqrt T := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by linarith)
    have hl_sqrt : l T ≤ Real.sqrt T * l T := by
      calc
        l T = 1 * l T := by ring
        _ ≤ Real.sqrt T * l T := mul_le_mul_of_nonneg_right hsqrt hl.le
    have hend : (Z.N T (T + 1) : ℝ) + (Z.N (2 * T - 1) (2 * T) : ℝ) ≤
        4 * A₀ * (Real.sqrt T * l T) := by
      calc
        (Z.N T (T + 1) : ℝ) + (Z.N (2 * T - 1) (2 * T) : ℝ) ≤
            2 * A₀ * l T + 2 * A₀ * l T := add_le_add hleft hright
        _ = 4 * A₀ * l T := by ring
        _ ≤ 4 * A₀ * (Real.sqrt T * l T) :=
          mul_le_mul_of_nonneg_left hl_sqrt (by positivity)
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg (omittedSimpleCount Z T P)),
      abs_of_nonneg hfactor]
    calc
      (omittedSimpleCount Z T P : ℝ) ≤
          (Assembly.NII Z T : ℝ) + (Z.N T (T + 1) : ℝ) +
            (Z.N (2 * T - 1) (2 * T) : ℝ) := hcoverR
      _ = (Assembly.NII Z T : ℝ) +
          ((Z.N T (T + 1) : ℝ) + (Z.N (2 * T - 1) (2 * T) : ℝ)) := by ring
      _ ≤ |CII| * (Real.sqrt T * l T) + 4 * A₀ * (Real.sqrt T * l T) :=
        add_le_add hIIabs hend
      _ = (|CII| + 4 * A₀) * (Real.sqrt T * l T) := by ring
  exact hO.trans_isLittleO
    (Assembly.isLittleO_N_of_isLittleO_Tl Z H.RvM
      Assembly.isLittleO_sqrt_mul_l_Tl)


end Sextuple
end ThmD
end Zeta23
