/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Sec2.Theorem5.WordSize

/-!
# The encodings of all bands of one matrix (Section 2.4.1)

Section 2.4.1: "We compute the encodings of the input arrays of all row bands and all column bands
[...], and every tile reads its two encodings from these."  encodeBands does this for one of the two
matrices: for each band β it calls bandArray, which forms the input array of the band at arr, and
encode, which leaves its encoding in the T = 10^L cells from enc + β T.

The loop is treated once, for callees that are described by what they do here (`encodeBands_proc`).
The two entries, for the row bands of X and for the column bands of Y, put in the specifications of
bandArray and encode for their side.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program}

namespace Bands

/-- The local variables of `encodeBands`.  The arguments: `Levels` = L, `Size` = m, `Rows` = N,
`Cols` = D, `NumBlocks` = K0, `Width` = N0, `Cells` = S7 = 7^L, `Leaves` = T = 10^L and `NumBands` =
nB are the sizes of the layout; `Side` says which of the two matrices stands at `Source`, with the
steps `StepRow` and `StepCol`; `MaskTable`, `Digits3` and `Digits4` are the tables that
`bandArray` reads, `Table`, `Pow7` and `Pow10` those that `encode` reads; `Arr` and `Scratch` are
scratch areas, and the encodings are written from `Enc` on.  Then `BandNo` = β, and `Res` takes the
results of the calls. -/
abbrev Levels : ℕ := 0
@[inherit_doc Levels] abbrev Size : ℕ := 1
@[inherit_doc Levels] abbrev Rows : ℕ := 2
@[inherit_doc Levels] abbrev Cols : ℕ := 3
@[inherit_doc Levels] abbrev NumBlocks : ℕ := 4
@[inherit_doc Levels] abbrev Width : ℕ := 5
@[inherit_doc Levels] abbrev Cells : ℕ := 6
@[inherit_doc Levels] abbrev Leaves : ℕ := 7
@[inherit_doc Levels] abbrev NumBands : ℕ := 8
@[inherit_doc Levels] abbrev Side : ℕ := 9
@[inherit_doc Levels] abbrev Source : ℕ := 10
@[inherit_doc Levels] abbrev StepRow : ℕ := 11
@[inherit_doc Levels] abbrev StepCol : ℕ := 12
@[inherit_doc Levels] abbrev MaskTable : ℕ := 13
@[inherit_doc Levels] abbrev Digits3 : ℕ := 14
@[inherit_doc Levels] abbrev Digits4 : ℕ := 15
@[inherit_doc Levels] abbrev Arr : ℕ := 16
@[inherit_doc Levels] abbrev Scratch : ℕ := 17
@[inherit_doc Levels] abbrev Table : ℕ := 18
@[inherit_doc Levels] abbrev Pow7 : ℕ := 19
@[inherit_doc Levels] abbrev Pow10 : ℕ := 20
@[inherit_doc Levels] abbrev Enc : ℕ := 21
@[inherit_doc Levels] abbrev BandNo : ℕ := 22
@[inherit_doc Levels] abbrev Res : ℕ := 23

end Bands

open Bands in
/-- encodeBands(L, m, N, D, K0, N0, S7, T, nB, side, aA, sI, sK, mask, dig3, dig4, arr, zs, tab, p7,
p10, enc): for each band, the input array is formed at arr and encoded into the T cells from
enc + β T. -/
def encodeBandsBody : Stmt :=
  .for BandNo (v NumBands) (
    .call pBandArray [v Levels, v Size, v Rows, v Cols, v NumBlocks, v Width, v Cells, v BandNo,
      v Side, v Source, v StepRow, v StepCol, v MaskTable, v Digits3, v Digits4, v Arr] Res ;;
    .call pEncode [v Levels, v Arr, v Enc +' v BandNo *' v Leaves, v Scratch, v Table, v Pow7,
      v Pow10] Res)

/-- The time of the loop is at most the constant cB + cE + 50 times the shape of the entries. -/
theorem encodeBands_time (p : Par) (cB cE : ℕ) :
    p.nB * (cB * bandArrayShape p + cE * 10 ^ p.L + 50) + 6
      ≤ (cB + cE + 50) * (p.nB * (p.T + bandArrayShape p) + 1) := by
  have hT : 1 ≤ p.T := Nat.one_le_pow _ _ (by norm_num)
  have hfifty : p.nB * 50 ≤ p.nB * (50 * p.T) := Nat.mul_le_mul_left _ (by omega)
  change p.nB * (cB * bandArrayShape p + cE * p.T + 50) + 6 ≤ _
  calc p.nB * (cB * bandArrayShape p + cE * p.T + 50) + 6
      = p.nB * (cB * bandArrayShape p) + p.nB * (cE * p.T) + p.nB * 50 + 6 := by ring
    _ ≤ p.nB * (cB * bandArrayShape p) + p.nB * (cE * p.T) + p.nB * (50 * p.T) + 6
        + (p.nB * (cB * p.T) + p.nB * ((cE + 50) * bandArrayShape p) + (cB + cE + 44)) := by omega
    _ = (cB + cE + 50) * (p.nB * (p.T + bandArrayShape p) + 1) := by ring

/-! ## The arguments, and what is assumed about them -/

/-- The addresses that encodeBands gets besides that of the matrix.  mask, dig3 and dig4 are the
tables that bandArray reads, tab, p7 and p10 those that encode reads.  arr and zs are scratch, and
the encodings are written from enc on. -/
structure BandsArgs where
  (mask dig3 dig4 arr zs tab p7 p10 enc : ℕ)

/-- The arguments of encodeBands at the sizes of p, for the matrix at aA with the strides sI and
sK. -/
@[simp] def BandsArgs.vals (x : BandsArgs) (p : Par) (side aA sI sK : ℕ) : List ℤ :=
  [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, p.T, p.nB, side, aA, sI, sK, x.mask, x.dig3, x.dig4,
    x.arr, x.zs, x.tab, x.p7, x.p10, x.enc]

/-- What encodeBands assumes besides the matrix.  Everything that is read lies below enc: the tables
of bandArray, the 70 coefficients coefs of the side, and the powers of 7 and of 10.  From enc on
follow the encodings and the two scratch areas.  V bounds the entries of the matrix. -/
structure BandsPre (lim : Limits) (p : Par) (μ : ℕ → ℤ) (x : BandsArgs) (coefs : List ℤ) (V : ℤ) :
    Prop where
  tables : BandTables p μ x.mask x.dig3 x.dig4 x.enc
  coef : Seg μ x.tab coefs
  coef_le : x.tab + 70 ≤ x.enc
  p7 : Seg μ x.p7 (powList 7 (p.L + 1))
  p7_le : x.p7 + (p.L + 1) ≤ x.enc
  p10 : Seg μ x.p10 (powList 10 (p.L + 1))
  p10_le : x.p10 + (p.L + 1) ≤ x.enc
  enc_le : x.enc + p.nB * p.T ≤ x.arr
  arr_le : x.arr + p.S7 ≤ x.zs
  zs_le : x.zs + p.S7 ≤ lim.space
  V_nonneg : 0 ≤ V
  word : 7 ^ (p.L + 1) * V ≤ lim.word

variable {p : Par} {x : BandsArgs} {coefs : List ℤ} {V : ℤ} {μ μ' : ℕ → ℤ}

/-- **encodeBands**, at the sizes of `p`, for callees described by what they do here: `HB` says that
`bandArray` leaves the list `A β` at `arr`, within `cB bandArrayShape` steps, `HE` that `encode`
turns it into the list `E β` at `enc + β T`, within `cE 10^L` steps; both in any memory that agrees
with `μ` below `enc`.  Then the lists `E β` stand from `enc` on. -/
theorem encodeBands_proc (std : Std lim) (hP : P[pEncodeBands]? = some encodeBandsBody)
    {d side aA sI sK cB cE : ℕ} {A E : ℕ → List ℤ} (pre : BandsPre lim p μ x coefs V)
    (hd : d < lim.depth) (hE : ∀ β, (E β).length = p.T)
    (HB : ∀ β < p.nB, ∀ μ' : ℕ → ℤ, Kept μ μ' x.enc →
      Meets lim P pBandArray (d + 1)
        [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, β, side, aA, sI, sK, x.mask, x.dig3, x.dig4, x.arr]
        μ' (cB * bandArrayShape p) fun _ μ'' =>
          Seg μ'' x.arr (A β) ∧ SameOutside μ' μ'' x.arr p.S7)
    (HE : ∀ β < p.nB, ∀ μ' : ℕ → ℤ, Kept μ μ' x.enc → Seg μ' x.arr (A β) →
      Meets lim P pEncode (d + 1) [p.L, x.arr, (x.enc + β * p.T : ℕ), x.zs, x.tab, x.p7, x.p10] μ'
        (cE * 10 ^ p.L) fun _ μ'' => Seg μ'' (x.enc + β * p.T) (E β) ∧
          SameOutside2 μ' μ'' (x.enc + β * p.T) (10 ^ p.L) x.zs (7 ^ p.L)) :
    Meets lim P pEncodeBands d (x.vals p side aA sI sK) μ
      ((cB + cE + 50) * (p.nB * (p.T + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, Seg μ' (x.enc + β * p.T) (E β)) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc) := by
  refine .of_body hP (Ends.mono (T := p.nB * (cB * bandArrayShape p + cE * 10 ^ p.L + 50) + 6) ?_
    (encodeBands_time p cB cE) fun _ h => h)
  light_facts pre std
  have hT : p.T = 10 ^ p.L := rfl
  have hS7 : p.S7 = 7 ^ p.L := rfl
  have hnB : p.nB ≤ p.nB * p.T := Nat.le_mul_of_pos_right _ p.one_le_T
  -- for β < nB: the encodings of the bands below β are in place
  refine Ends.forShape
    (fun β r μ' => ⟨frame [p.L, p.m, p.N, p.D, p.K0, p.N0, p.S7, p.T, p.nB, side, aA, sI, sK,
      x.mask, x.dig3, x.dig4, x.arr, x.zs, x.tab, x.p7, x.p10, x.enc, β, r], μ'⟩)
    (fun β μ' => (∀ β' < β, Seg μ' (x.enc + β' * p.T) (E β')) ∧
      SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc))
    p.nB (cB * bandArrayShape p + cE * 10 ^ p.L + 42) 0 ⟨fun β' h => absurd h (by omega), .refl⟩
    ?round (fun _ _ h => h) (by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
  rintro β r μ' hβ ⟨hdone, same⟩
  have hβT : β * p.T + p.T ≤ p.nB * p.T := Nat.mul_add_le_mul hβ le_rfl
  -- bandArray(L, m, N, D, K0, N0, S7, β, side, aA, sI, sK, mask, dig3, dig4, arr)
  light_call (HB β hβ μ' (by light_keep)) with r₁ μ₁ ⟨hA, same₁⟩
  -- encode(L, arr, enc + β T, zs, tab, p7, p10)
  light_call (HE β hβ μ₁ (by light_keep) hA) with r₂ μ₂ ⟨hEβ, same₂⟩
  refine ⟨r₂, μ₂, rfl, fun β' hβ' => ?_, by light_keep⟩
  rcases Nat.lt_or_ge β' β with h | h
  · -- The encodings of the earlier bands lie below enc + β T and have not been touched.
    have hβ'T : β' * p.T + p.T ≤ β * p.T := Nat.mul_add_le_mul h le_rfl
    have hlen := hE β'
    exact (hdone β' h).keep
  · obtain rfl : β' = β := by omega
    exact hEβ

/-! ## What is read does not change -/

/-- The tables that bandArray reads, in a memory that agrees below their bound. -/
theorem BandTables.congr_below {p : Par} {μ μ' : ℕ → ℤ} {mask dig3 dig4 e : ℕ}
    (h : BandTables p μ mask dig3 dig4 e) (hlow : ∀ x < e, μ' x = μ x) :
    BandTables p μ' mask dig3 dig4 e where
  hmask := fun s hs => (h.hmask s hs).congr fun i hi => hlow _ (by
    have hrow : s * p.L + p.L ≤ p.KK * p.L := Nat.mul_add_le_mul hs le_rfl
    have hend := h.mask_le
    simp at hi
    omega)
  hdig3 := fun I hI => (h.hdig3 I hI).congr fun i hi => hlow _ (by
    have hrow : I * p.Lo + p.Lo ≤ p.N * p.Lo := Nat.mul_add_le_mul hI le_rfl
    have hend := h.dig3_le
    simp at hi
    omega)
  hdig4 := fun x hx => (h.hdig4 x hx).congr fun i hi => hlow _ (by
    have hrow : x * p.m + p.m ≤ p.D * p.m := Nat.mul_add_le_mul hx le_rfl
    have hend := h.dig4_le
    simp at hi
    omega)
  mask_le := h.mask_le
  dig3_le := h.dig3_le
  dig4_le := h.dig4_le

/-- The tables also lie below every larger bound. -/
theorem BandTables.mono {p : Par} {μ : ℕ → ℤ} {mask dig3 dig4 e e' : ℕ}
    (h : BandTables p μ mask dig3 dig4 e) (hle : e ≤ e') : BandTables p μ mask dig3 dig4 e' :=
  { h with
    mask_le := h.mask_le.trans hle
    dig3_le := h.dig3_le.trans hle
    dig4_le := h.dig4_le.trans hle }

/-- The places of the call of encode for the band β, in a memory that agrees with μ below enc. -/
theorem BandsPre.encodePlaces (pre : BandsPre lim p μ x coefs V) {β : ℕ} (hβ : β < p.nB)
    (hlow : ∀ b < x.enc, μ' b = μ b) :
    EncodePlaces lim p.L p.L x.arr (x.enc + β * p.T) x.zs x.tab x.p7 x.p10 μ' := by
  light_facts pre
  exact
    { n_le := le_rfl
      hp7 := pre.p7.congr fun i hi => hlow _ (by simp at hi; omega)
      hp10 := pre.p10.congr fun i hi => hlow _ (by simp at hi; omega)
      tab_le := by omega
      p7_le := by omega
      p10_le := by omega
      dst_le := by
        have hβT : β * p.T + p.T ≤ p.nB * p.T := Nat.mul_add_le_mul hβ le_rfl
        change x.enc + β * p.T + p.T ≤ x.arr
        omega
      src_le := pre.arr_le
      scr_le := pre.zs_le }

/-! ## The two entries -/

/-- encodeBands for the row bands of X: side = 0, the coefficients φ at tab. -/
def EncodeBandsLSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (x : BandsArgs) (aX : ℕ) (μ : ℕ → ℤ)
    (X : Matrix (Fin p.N) (Fin (ThreeSumApsp.D p.m)) ℤ) (V : ℤ),
    BandsPre lim p μ x Spec.phiFlat V → MatAt μ aX X → aX + p.N * p.D ≤ x.enc →
    (∀ i j, |X i j| ≤ V) →
    ∀ d, d + (p.L + 2) ≤ lim.depth → Meets lim P pEncodeBands d (x.vals p 0 aX p.D 1) μ
      (c * (p.nB * (p.T + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, Seg μ' (x.enc + β * p.T)
          (Spec.arrT (encodingL (bandArrayL (Spec.stdLayout hmL) X β)))) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc)

/-- **encodeBands** meets this entry, with every constant from cB + cE + 50 on. -/
theorem encodeBandsL_entry (std : Std lim) (hP : P[pEncodeBands]? = some encodeBandsBody)
    {cB cE c : ℕ} (hB : BandArrayLSpec lim P cB) (hE : EncodeLSpec lim P cE)
    (hc : cB + cE + 50 ≤ c) : EncodeBandsLSpec lim P c := by
  intro p hmL x aX μ X V pre hM hMle hV d hd
  light_facts pre
  refine .mono_const ?_ hc
  refine encodeBands_proc std hP pre (by omega) (fun β => Spec.length_arrT _)
    (A := fun β => Spec.arrL (bandArrayL (Spec.stdLayout hmL) X β))
    (fun β hβ μ' hlow => ?_) fun β hβ μ' hlow hA => ?_
  · simpa using hB p hmL β aX x.mask x.dig3 x.dig4 x.arr μ' X (by omega)
      (hM.congr_below hlow hMle) (by omega) ((pre.tables.congr_below hlow).mono (by omega)) hβ
      _ (by omega)
  · exact hE p.L p.L x.arr (x.enc + β * p.T) x.zs x.tab x.p7 x.p10 μ' _ V
      (pre.encodePlaces hβ hlow)
      (pre.coef.congr fun i hi => hlow _ (by
        have := Spec.length_phiFlat
        omega))
      hA (abs_bandArrayL_le (Spec.stdLayout hmL) pre.V_nonneg hV β) pre.word _ (by omega)

/-- encodeBands for the column bands of Y: side = 1, the coefficients ψ at tab. -/
def EncodeBandsRSpec (lim : Limits) (P : Program) (c : ℕ) : Prop :=
  ∀ (p : Par) (hmL : p.m ≤ p.L) (x : BandsArgs) (aY : ℕ) (μ : ℕ → ℤ)
    (Y : Matrix (Fin (ThreeSumApsp.D p.m)) (Fin p.N) ℤ) (V : ℤ),
    BandsPre lim p μ x Spec.psiFlat V → MatAt μ aY Y → aY + p.D * p.N ≤ x.enc →
    (∀ i j, |Y i j| ≤ V) →
    ∀ d, d + (p.L + 2) ≤ lim.depth → Meets lim P pEncodeBands d (x.vals p 1 aY 1 p.N) μ
      (c * (p.nB * (p.T + bandArrayShape p) + 1)) fun _ μ' =>
        (∀ β < p.nB, Seg μ' (x.enc + β * p.T)
          (Spec.arrT (encodingR (bandArrayR (Spec.stdLayout hmL) Y β)))) ∧
          SameOutside μ μ' x.enc (x.zs + p.S7 - x.enc)

/-- **encodeBands** meets this entry, with every constant from cB + cE + 50 on. -/
theorem encodeBandsR_entry (std : Std lim) (hP : P[pEncodeBands]? = some encodeBandsBody)
    {cB cE c : ℕ} (hB : BandArrayRSpec lim P cB) (hE : EncodeRSpec lim P cE)
    (hc : cB + cE + 50 ≤ c) : EncodeBandsRSpec lim P c := by
  intro p hmL x aY μ Y V pre hM hMle hV d hd
  light_facts pre
  refine .mono_const ?_ hc
  refine encodeBands_proc std hP pre (by omega) (fun β => Spec.length_arrT _)
    (A := fun β => Spec.arrR (bandArrayR (Spec.stdLayout hmL) Y β))
    (fun β hβ μ' hlow => ?_) fun β hβ μ' hlow hA => ?_
  · simpa using hB p hmL β aY x.mask x.dig3 x.dig4 x.arr μ' Y (by omega)
      (hM.congr_below hlow hMle) (by omega) ((pre.tables.congr_below hlow).mono (by omega)) hβ
      _ (by omega)
  · exact hE p.L p.L x.arr (x.enc + β * p.T) x.zs x.tab x.p7 x.p10 μ' _ V
      (pre.encodePlaces hβ hlow)
      (pre.coef.congr fun i hi => hlow _ (by
        have := Spec.length_psiFlat
        omega))
      hA (abs_bandArrayR_le (Spec.stdLayout hmL) pre.V_nonneg hV β) pre.word _ (by omega)

end Light.Sec2
