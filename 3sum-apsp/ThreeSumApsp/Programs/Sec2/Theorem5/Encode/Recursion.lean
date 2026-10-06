/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Step

/-!
# The encoding of an array by the recursion of Section 2.4.1

"To compute it, we run Full with b left out and without step (4)" (Section 2.4.1).  If L = 0 the
leaf stores its number.  Otherwise, for each term λ, step (2) writes A_λ to a scratch area and the
recursive call of step (3) encodes it into the part of the output that belongs to the leaves below
λ.  The language has no division, so the lengths 7^{L-1} and 10^{L-1} of the parts are read from two
tables of powers.

`encIdx` is what `encode` computes, in terms of positions in arrays.  `encode` writes it to the
output within `encTime L = O(10^L)` steps (`encTime_le`), using `scrSize L` scratch cells.  The
proof is by induction on `L`:

* the hypotheses of `encode` at level `L + 1` give those of `encStep` (`EncodePre.toStep`) and,
  after it, those of the recursive call (`EncodePre.toRec`);
* the two calls for the term `λ` fill the part of the output below `λ` (`TermsDone.step`,
  `encodeTerm_spec`);
* `encode_leaf` is the case `L = 0`, `encode_node` the loop over the ten terms, and `encode_spec`
  the induction.
-/

@[expose] public section

namespace Light.Sec2

open Finset ThreeSumApsp

namespace Encode

/-- The local variables of encode: the arguments L, src, out, scr, tab, p7, p10; the lengths 7^{L-1}
and 10^{L-1}; the number of the term; the result of a call, which is not used. -/
abbrev Level : ℕ := 0
@[inherit_doc Level] abbrev Src : ℕ := 1
@[inherit_doc Level] abbrev Out : ℕ := 2
@[inherit_doc Level] abbrev Scr : ℕ := 3
@[inherit_doc Level] abbrev Table : ℕ := 4
@[inherit_doc Level] abbrev Pow7 : ℕ := 5
@[inherit_doc Level] abbrev Pow10 : ℕ := 6
@[inherit_doc Level] abbrev Len7 : ℕ := 7
@[inherit_doc Level] abbrev Len10 : ℕ := 8
@[inherit_doc Level] abbrev TermNo : ℕ := 9
@[inherit_doc Level] abbrev Res : ℕ := 10

end Encode

open Encode

/-- The two calls for one term: step (2) into the scratch area, and step (3) from there into the
part of the output that belongs to the term. -/
def encodeTerm (pS pE : ℕ) : Stmt :=
  .call pS [v Src, v Scr, v Len7, v TermNo, v Table] Res ;;
  .call pE [v Level -' k 1, v Scr, v Out +' v TermNo *' v Len10, v Scr +' v Len7, v Table, v Pow7,
    v Pow10] Res

/-- encode(L, src, out, scr, tab, p7, p10).  pS and pE are the numbers that the procedures encStep
and encode have in the program. -/
def encodeBody (pS pE : ℕ) : Stmt :=
  .ite (v Level =' k 0)
    (.store (v Out) (M (v Src)))
    (.set Len7 (M (v Pow7 +' v Level -' k 1)) ;;
     .set Len10 (M (v Pow10 +' v Level -' k 1)) ;;
     .for TermNo (k 10) (encodeTerm pS pE))

/-! ## What encode computes, how much room and how much time it needs -/

/-- The array A_lam of step (2), in terms of positions in arrays: a is the input array (7^{L+1}
numbers, seven slices of 7^L) and c the table of the coefficients (c (7 lam + s) is the coefficient
of slice number s in the term number lam). -/
def encSlice (c a : ℕ → ℤ) (L lam : ℕ) : ℕ → ℤ :=
  fun j => ∑ s ∈ range 7, c (7 * lam + s) * a (s * 7 ^ L + j)

/-- What encode computes, in terms of positions in arrays: a is the input array (7^L numbers), c the
table of the coefficients, and i < 10^L the position of a leaf. -/
def encIdx (c : ℕ → ℤ) : (L : ℕ) → (ℕ → ℤ) → ℕ → ℤ
  | 0, a, _ => a 0
  | L + 1, a, i => encIdx c L (encSlice c a L (i / 10 ^ L)) (i % 10 ^ L)

/-- The part of the encoding below the term number lam is the encoding of A_lam. -/
private theorem encIdx_succ (c a : ℕ → ℤ) (L lam : ℕ) {i : ℕ} (hi : i < 10 ^ L) :
    encIdx c (L + 1) a (lam * 10 ^ L + i) = encIdx c L (encSlice c a L lam) i := by
  rw [encIdx, Nat.mul_add_div_of_lt hi, Nat.mul_add_mod_of_lt hi]

/-- The number of scratch cells that encode uses: 7^{L-1} + ⋯ + 7 + 1. -/
def scrSize : ℕ → ℕ
  | 0 => 0
  | L + 1 => 7 ^ L + scrSize L

/-- A bound on the number of steps of `encode`: at level `L + 1`, ten times the two calls for a
term, and 104 steps. -/
def encTime : ℕ → ℕ
  | 0 => 8
  | L + 1 => 104 + 10 * (24 + tEncStep (7 ^ L) + encTime L)

/-- The time of the two calls for one term. -/
def tTerm (L : ℕ) : ℕ := 24 + tEncStep (7 ^ L) + encTime L

/-- The constant of the running time of `encode`. -/
def cEncode : ℕ := 777

/-- The number of steps is `O(10^L)`.  The two further terms on the left make the induction go
through. -/
theorem encTime_le (L : ℕ) : encTime L + 724 * 7 ^ L + 45 ≤ cEncode * 10 ^ L := by
  unfold cEncode
  induction L with
  | zero => simp [encTime]
  | succ L ih =>
    simp only [encTime, tEncStep, pow_succ]
    omega

/-! ## The hypotheses -/

/-- Where the arrays of `encode` lie: the three tables, then the output, the input and the scratch
area, one behind the other. -/
structure EncodeLayout (lim : Limits) (src out scr tab p7 p10 L : ℕ) : Prop where
  std : Std lim
  tab_le : tab + 70 ≤ out
  p7_le : p7 + L ≤ out
  p10_le : p10 + L ≤ out
  out_le : out + 10 ^ L ≤ src
  src_le : src + 7 ^ L ≤ scr
  scr_le : scr + scrSize L ≤ lim.space

/-- The hypotheses of `encode`: the layout, what the cells hold, and how large the numbers are. -/
structure EncodePre (lim : Limits) (μ : ℕ → ℤ) (src out scr tab p7 p10 : ℕ) (V : ℤ) (L : ℕ)
    (a c : ℕ → ℤ) : Prop where
  lay : EncodeLayout lim src out scr tab p7 p10 L
  srcV : ∀ j < 7 ^ L, μ (src + j) = a j
  src_bound : ∀ j < 7 ^ L, -V ≤ a j ∧ a j ≤ V
  tabV : ∀ i < 70, μ (tab + i) = c i
  coef_bound : ∀ i < 70, -1 ≤ c i ∧ c i ≤ 1
  p7V : ∀ i < L, μ (p7 + i) = ((7 ^ i : ℕ) : ℤ)
  p10V : ∀ i < L, μ (p10 + i) = ((10 ^ i : ℕ) : ℤ)
  word_bound : ((7 ^ L : ℕ) : ℤ) * V ≤ lim.word

/-- What `encode` guarantees: the encoding is in `out`, and only the `10^L` cells of `out` and the
`scrSize L` cells of the scratch area have changed. -/
def EncodePost (μ : ℕ → ℤ) (out scr L : ℕ) (a c : ℕ → ℤ) (μ' : ℕ → ℤ) : Prop :=
  (∀ i < 10 ^ L, μ' (out + i) = encIdx c L a i) ∧ SameOutside2 μ μ' out (10 ^ L) scr (scrSize L)

variable {lim : Limits} {P : Program} {d : ℕ} {μ μ' μ₁ μ₂ : ℕ → ℤ}
  {src out scr tab p7 p10 L lam : ℕ} {V : ℤ} {a c : ℕ → ℤ}

/-- The layout at level `L + 1`, with the sizes in terms of `10^L`, `7^L` and `scrSize L`. -/
theorem EncodeLayout.places_succ (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1)) :
    tab + 70 ≤ out ∧ p7 + (L + 1) ≤ out ∧ p10 + (L + 1) ≤ out ∧ out + 10 * 10 ^ L ≤ src ∧
      src + 7 * 7 ^ L ≤ scr ∧ scr + (7 ^ L + scrSize L) ≤ lim.space ∧
      (lim.space : ℤ) ≤ lim.word ∧ (100 : ℤ) ≤ lim.word := by
  simpa only [pow_succ', scrSize] using And.intro lay.tab_le <| And.intro lay.p7_le <|
    And.intro lay.p10_le <| And.intro lay.out_le <| And.intro lay.src_le <|
    And.intro lay.scr_le <| And.intro lay.std.space_le lay.std.const_le

/-- What has not changed at level `L + 1`, with the sizes in terms of `10^L`, `7^L` and
`scrSize L`. -/
private theorem sameOutside2_succ (h : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))) :
    SameOutside2 μ μ' out (10 * 10 ^ L) scr (7 ^ L + scrSize L) := by
  simpa only [pow_succ', scrSize] using h

/-- The layout of the recursive call for the term number `lam`: it reads the first `7^L` cells of
the scratch area, writes the part of the output below the term, and has the rest of the scratch
area. -/
private theorem EncodeLayout.toRec (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1))
    (hlam : lam < 10) :
    EncodeLayout lim scr (out + lam * 10 ^ L) (scr + 7 ^ L) tab p7 p10 L := by
  have hplaces := lay.places_succ
  have hpart : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  exact ⟨lay.std, by omega, by omega, by omega, by omega, by omega, by omega⟩

namespace EncodePre

/-- The bound `V` is not negative. -/
private theorem V_nonneg (pre : EncodePre lim μ src out scr tab p7 p10 V L a c) : 0 ≤ V := by
  have := pre.src_bound 0 (by positivity)
  omega

/-- In the course of `encode` at level `L + 1`, the hypotheses of `encStep` hold for every term. -/
private theorem toStep (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c)
    (hlam : lam < 10) (same : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))) :
    EncStepPre lim μ' src scr (7 ^ L) lam tab V := by
  have hplaces := pre.lay.places_succ
  have hkept := sameOutside2_succ same
  have hV := pre.V_nonneg
  have hword := pre.word_bound
  have hone : (1 : ℤ) ≤ 7 ^ L := one_le_pow₀ (by norm_num)
  rw [pow_succ'] at hword
  push_cast at hword
  exact
    { std := pre.lay.std, tab_le := by omega, src_le := by omega, dst_le := by omega
      coef := fun i hi => by
        rw [Nat.add_assoc, hkept _ (by omega), pre.tabV _ (by omega)]
        exact pre.coef_bound _ (by omega)
      vals := fun i hi => by
        rw [hkept _ (by omega), pre.srcV i (by rw [pow_succ']; omega)]
        exact pre.src_bound i (by rw [pow_succ']; omega)
      word_bound := (mul_le_mul_of_nonneg_right (by omega) hV).trans hword }

/-- After `encStep` has written `A_lam` to the scratch area, the hypotheses of `encode` hold at
level `L` for the recursive call. -/
private theorem toRec (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c) (hlam : lam < 10)
    (same : SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1)))
    (hstep : ∀ j < 7 ^ L, μ₁ (scr + j) = encStepVal μ' src lam tab (7 ^ L) j 7)
    (same₁ : SameOutside μ' μ₁ scr (7 ^ L)) :
    EncodePre lim μ₁ scr (out + lam * 10 ^ L) (scr + 7 ^ L) tab p7 p10 (7 * V) L
      (encSlice c a L lam) c := by
  have hplaces := pre.lay.places_succ
  have hkept := sameOutside2_succ same
  have hword := pre.word_bound
  have hsrc : ∀ j < 7 * 7 ^ L, μ' (src + j) = a j := fun j hj => by
    rw [hkept _ (by omega)]
    exact pre.srcV j (by rw [pow_succ']; omega)
  have htab : ∀ i < 70, μ' (tab + i) = c i := fun i hi => by
    rw [hkept _ (by omega)]
    exact pre.tabV i hi
  exact
    { lay := pre.lay.toRec hlam
      srcV := fun j hj => by
        rw [hstep j hj]
        refine Finset.sum_congr rfl fun s hs => ?_
        have hs7 : s < 7 := Finset.mem_range.mp hs
        rw [Nat.add_assoc tab, htab (7 * lam + s) (by omega), Nat.add_assoc src,
          hsrc _ (Nat.mul_add_lt_mul hs7 hj)]
      src_bound := fun j hj => by
        simpa [encSlice] using enc_sum_bound 7 fun s hs =>
          enc_coef_mul_bound (pre.coef_bound (7 * lam + s) (by omega))
            (pre.src_bound (s * 7 ^ L + j) (by rw [pow_succ']; exact Nat.mul_add_lt_mul hs hj))
      tabV := fun i hi => by rw [same₁ _ (by omega), htab i hi]
      coef_bound := pre.coef_bound
      p7V := fun i hi => by rw [same₁ _ (by omega), hkept _ (by omega), pre.p7V i (by omega)]
      p10V := fun i hi => by rw [same₁ _ (by omega), hkept _ (by omega), pre.p10V i (by omega)]
      word_bound := by
        rw [pow_succ'] at hword
        push_cast at hword ⊢
        rwa [show (7 : ℤ) ^ L * (7 * V) = 7 * 7 ^ L * V by ring] }

end EncodePre

/-! ## One term -/

/-- The memory before the round of the term number `lam`: the parts of the output below the earlier
terms are filled, and only the output and the scratch area have changed. -/
def TermsDone (μ : ℕ → ℤ) (out scr L : ℕ) (a c : ℕ → ℤ) (lam : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ i < lam * 10 ^ L, μ' (out + i) = encIdx c (L + 1) a i) ∧
    SameOutside2 μ μ' out (10 ^ (L + 1)) scr (scrSize (L + 1))

/-- The two calls for the term number `lam` fill the part of the output below it. -/
theorem TermsDone.step (lay : EncodeLayout lim src out scr tab p7 p10 (L + 1)) (hlam : lam < 10)
    (h : TermsDone μ out scr L a c lam μ') (same₁ : SameOutside μ' μ₁ scr (7 ^ L))
    (hpost : EncodePost μ₁ (out + lam * 10 ^ L) (scr + 7 ^ L) L (encSlice c a L lam) c μ₂) :
    TermsDone μ out scr L a c (lam + 1) μ₂ := by
  have hplaces := lay.places_succ
  have hpart : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  obtain ⟨hdone, same⟩ := h
  obtain ⟨hnew, same₂⟩ := hpost
  have hkept := sameOutside2_succ same
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [Nat.succ_mul] at hi
    by_cases hold : i < lam * 10 ^ L
    · -- The parts below the earlier terms are not touched.
      rw [same₂ _ (by omega), same₁ _ (by omega), hdone i hold]
    · -- The part below this term.
      obtain ⟨i, rfl⟩ : ∃ i', i = lam * 10 ^ L + i' := ⟨i - lam * 10 ^ L, by omega⟩
      rw [← Nat.add_assoc, hnew i (by omega), encIdx_succ c a L lam (by omega)]
  · simp only [pow_succ', scrSize]
    clear same
    light_keep

/-- The list of the local variables at level L + 1. -/
abbrev Encode.locals (L src out scr tab p7 p10 lam : ℕ) (r : ℤ) : List ℤ :=
  [(L + 1 : ℕ), src, out, scr, tab, p7, p10, (7 ^ L : ℕ), (10 ^ L : ℕ), lam, r]

/-- The specification of encode at level L, for a caller at depth d. -/
def EncodeMeets (lim : Limits) (P : Program) (pE d tab p7 p10 L : ℕ) (c : ℕ → ℤ) : Prop :=
  ∀ (μ : ℕ → ℤ) (src out scr : ℕ) (V : ℤ) (a : ℕ → ℤ),
    EncodePre lim μ src out scr tab p7 p10 V L a c →
    Meets lim P pE (d + 1) [L, src, out, scr, tab, p7, p10] μ (encTime L) fun _ μ' =>
      EncodePost μ out scr L a c μ'

variable {pS pE : ℕ}

/-- **One term**: step (2) and step (3) fill the part of the output below the term number `lam`. -/
theorem encodeTerm_spec (hS : P[pS]? = some encStepBody)
    (hrec : EncodeMeets lim P pE d tab p7 p10 L c)
    (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c) (hd : d < lim.depth)
    (hlam : lam < 10) (h : TermsDone μ out scr L a c lam μ') (r : ℤ) :
    Ends lim P d (encodeTerm pS pE) ⟨frame (locals L src out scr tab p7 p10 lam r), μ'⟩ (tTerm L)
      fun σ' => ∃ (r' : ℤ) (μ'' : ℕ → ℤ),
        σ' = ⟨frame (locals L src out scr tab p7 p10 lam r'), μ''⟩ ∧
          TermsDone μ out scr L a c (lam + 1) μ'' := by
  have hplaces := pre.lay.places_succ
  -- The arguments of the two calls fit in a word, by the layout and the next three facts.
  have hpart : lam * 10 ^ L + 10 ^ L ≤ 10 * 10 ^ L := Nat.mul_add_le_mul hlam le_rfl
  have hprod : ((lam * 10 ^ L : ℕ) : ℤ) = lam * 10 ^ L := by push_cast; rfl
  have hpow : ((7 ^ L : ℕ) : ℤ) = 7 ^ L := by push_cast; rfl
  unfold encodeTerm tTerm
  -- Res := encStep(src, scr, 7^L, lam, tab)
  light_call (encStep_meets hS (pre.toStep hlam h.2)) with r₁ μ₁ ⟨hstep, same₁⟩
  -- Res := encode(L, scr, out + lam 10^L, scr + 7^L, tab, p7, p10)
  refine Ends.callTo (hrec _ _ _ _ _ _ (pre.toRec hlam h.2 hstep same₁)) ?_
  exact fun r₂ μ₂ hpost => ⟨r₂, μ₂, rfl, h.step pre.lay hlam same₁ hpost⟩

/-! ## The recursion -/

/-- **A leaf**: the number is copied. -/
theorem encode_leaf (pre : EncodePre lim μ src out scr tab p7 p10 V 0 a c) :
    Ends lim P d (encodeBody pS pE) ⟨frame [(0 : ℕ), src, out, scr, tab, p7, p10], μ⟩ (encTime 0)
      fun σ' => EncodePost μ out scr 0 a c σ'.mem := by
  light_facts pre.lay pre.lay.std
  have hread : μ src = a 0 := pre.srcV 0 (by norm_num)
  -- if Level = 0 then mem[Out] := mem[Src]
  refine Ends.iteLast (fun _ => ?_) (fun h => absurd (by simp) h) (hT := by simp [encTime])
  refine Ends.storeTo out (a 0) ⟨fun i hi => ?_, by light_keep⟩
    (by light_side [hread]) (by simp [encTime])
  obtain rfl : i = 0 := by simpa using hi
  exact Function.update_self ..

/-- **An inner vertex**: the two lengths are read from the tables, and the loop runs through the ten
terms. -/
theorem encode_node (hS : P[pS]? = some encStepBody)
    (hrec : EncodeMeets lim P pE d tab p7 p10 L c)
    (pre : EncodePre lim μ src out scr tab p7 p10 V (L + 1) a c) (hd : d < lim.depth) :
    Ends lim P d (encodeBody pS pE) ⟨frame [(L + 1 : ℕ), src, out, scr, tab, p7, p10], μ⟩
      (encTime (L + 1)) fun σ' => EncodePost μ out scr (L + 1) a c σ'.mem := by
  have hplaces := pre.lay.places_succ
  have haddr7 : ((p7 : ℤ) + ((L : ℤ) + 1) - 1).toNat = p7 + L := by omega
  have haddr10 : ((p10 : ℤ) + ((L : ℤ) + 1) - 1).toNat = p10 + L := by omega
  have hread7 := pre.p7V L (by omega)
  have hread10 := pre.p10V L (by omega)
  rw [encTime]
  -- if Level = 0
  refine Ends.iteLast (fun h => absurd h (by simp; omega)) (fun _ => ?_)
  -- Len7 := mem[Pow7 + Level - 1]; Len10 := mem[Pow10 + Level - 1]
  light_set (7 ^ L : ℕ) using haddr7, hread7
  light_set (10 ^ L : ℕ) using haddr10, hread10
  -- for TermNo < 10: the parts of the output below the earlier terms are filled
  refine Ends.forShape (fun lam r μ' => ⟨frame (locals L src out scr tab p7 p10 lam r), μ'⟩)
    (TermsDone μ out scr L a c) 10 (tTerm L) 0 ⟨fun i hi => absurd hi (by omega), .refl⟩
    (fun lam r μ' hlam h => encodeTerm_spec hS hrec pre hd hlam h r)
    (fun _ μ' h => ⟨fun i hi => h.1 i (by rwa [pow_succ'] at hi), h.2⟩)
    (by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
    (hT := by simp [tTerm]; omega)

/-- **encode** is correct and takes at most `encTime L` steps, in every program whose procedures
number pS and pE are encStep and encode.  It nests calls at most L deep. -/
theorem encode_spec (hS : P[pS]? = some encStepBody) (hE : P[pE]? = some (encodeBody pS pE))
    (hd : d + L ≤ lim.depth) (pre : EncodePre lim μ src out scr tab p7 p10 V L a c) :
    Ends lim P d (encodeBody pS pE) ⟨frame [L, src, out, scr, tab, p7, p10], μ⟩ (encTime L)
      fun σ' => EncodePost μ out scr L a c σ'.mem := by
  induction L generalizing d μ src out scr V a with
  | zero => exact encode_leaf pre
  | succ L ih =>
    exact encode_node hS (fun _ _ _ _ _ _ pre' => Meets.of_body hE (ih (by omega) pre')) pre
      (by omega)

end Light.Sec2
