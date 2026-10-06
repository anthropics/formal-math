/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# Cutting an increasing list of codes into its ten slices (step (2) of Pruned, Section 2.4.2)

segBounds goes once through an increasing list of codes of n + 1 digits.  The codes with first digit
z are consecutive; it notes where they start, and writes every code without its first digit.

* The list.  `SegInv` says where the pass stands: i codes are copied, z is the current first digit,
  and lo = z 10^n.  A code below lo + 10^n is copied (`SegInv.copy`); otherwise the pass goes on to
  the next first digit (`SegInv.advance`), and the position reached is the start of the next slice
  (`SegInv.segStart_succ`).
* The memory.  `SegMem` says what has been written, `SegMem.copy` and `SegMem.advance` what a round
  adds, and `SegMem.slices` that in the end the ten slices stand in the memory.
* The program.  `segCopy_ends` and `segAdvance_ends` treat the two kinds of rounds, and
  `segBounds_entry` the loop.  The result: a call takes at most `cSegBounds` steps for each code and
  each of the eleven bounds; afterwards the cells bnd to bnd + 10 hold the starts of the slices, the
  slice at z stands at bnd + 11 + segStart n codes z, and no other cell has changed.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

/-! ## The program -/

namespace SegLocal

/-- The list of the codes. -/
abbrev PL : ℕ := 0
/-- The length of the list. -/
abbrev LEN : ℕ := 1
/-- 10^n. -/
abbrev PW : ℕ := 2
/-- Where the bounds are written; the codes without first digits follow 11 cells later. -/
abbrev BND : ℕ := 3
/-- The position i in the list. -/
abbrev CI : ℕ := 4
/-- The first digit z. -/
abbrev CZ : ℕ := 5
/-- z 10^n. -/
abbrev LO : ℕ := 6
/-- (z + 1) 10^n. -/
abbrev HI : ℕ := 7

end SegLocal

open SegLocal

/-- The code at position i has first digit z: it is written without that digit. -/
def segCopy : Stmt :=
  .store (v BND +' k 11 +' v CI) (M (v PL +' v CI) -' v LO) ;; .set CI (v CI +' k 1)

/-- The next first digit: z := z + 1, the position reached is noted at bnd + z, and the two
thresholds move up. -/
def segAdvance : Stmt :=
  .set CZ (v CZ +' k 1) ;;
  .store (v BND +' v CZ) (v CI) ;;
  .set LO (v HI) ;;
  .set HI (v HI +' v PW)

/-- segBounds(l, len, pw, bnd). -/
def segBoundsBody : Stmt :=
  .set CI (k 0) ;;
  .set CZ (k 0) ;;
  .set LO (k 0) ;;
  .set HI (v PW) ;;
  .store (v BND) (k 0) ;;
  .while (v CZ <' k 10) (
    .ite (v CI <' v LEN)
      (.ite (M (v PL +' v CI) <' v HI) segCopy segAdvance)
      segAdvance)

/-- The constant of the running time: a call takes at most cSegBounds (codes.length + 11) steps. -/
def cSegBounds : ℕ := 32

/-! ## The list -/

/-- The number of codes below a, for a list in which the codes below a come first. -/
theorem length_takeWhile_lt_eq {l : List ℕ} {a i : ℕ} (hi : i ≤ l.length)
    (hbelow : ∀ i' < i, l.getD i' 0 < a) (habove : ∀ i', i ≤ i' → i' < l.length → a ≤ l.getD i' 0) :
    (l.takeWhile fun c => c < a).length = i := by
  have htake : ∀ x ∈ l.take i, (decide (x < a)) = true := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
    have ht' : t < i := by simp at ht; omega
    have hlt := hbelow t ht'
    rw [List.getD_eq_getElem _ _ (by omega)] at hlt
    simpa [List.getElem_take] using hlt
  have hdrop : (l.drop i).takeWhile (fun c => decide (c < a)) = [] := by
    rcases Nat.lt_or_ge i l.length with hlt | hge
    · have hle := habove i le_rfl hlt
      rw [List.getD_eq_getElem _ _ hlt] at hle
      rw [List.drop_eq_getElem_cons hlt, List.takeWhile_cons_of_neg (by simpa using hle)]
    · rw [List.drop_eq_nil_of_le hge]
      rfl
  rw [← List.take_append_drop i l, List.takeWhile_append_of_pos htake, hdrop, List.append_nil,
    List.length_take]
  omega

/-- The start of the slice at z is the number of codes below z 10^n. -/
theorem segStart_eq_length_takeWhile {n : ℕ} {l : List ℕ} (h : l.Pairwise (· < ·)) (z : ℕ) :
    segStart n l z = (l.takeWhile fun c => c < z * 10 ^ n).length := by
  rw [← Spec.flatMap_sliceList_eq_takeWhile h z, List.length_flatMap, segStart]
  congr 1
  exact List.map_congr_left fun t _ => by simp

/-- The codes of the slice at z, in the list. -/
theorem getD_segStart_add {n : ℕ} {l : List ℕ} (h : l.Pairwise (· < ·)) (z t : ℕ)
    (ht : t < (Spec.sliceList n z l).length) :
    segStart n l z + t < l.length ∧
      l.getD (segStart n l z + t) 0 = z * 10 ^ n + (Spec.sliceList n z l).getD t 0 ∧
      (Spec.sliceList n z l).getD t 0 < 10 ^ n := by
  -- The codes below (z + 1) 10^n are those below z 10^n, followed by the slice at z.
  have hsplit := Spec.flatMap_sliceList_eq_takeWhile (n := n) h (z + 1)
  rw [List.range_succ, List.flatMap_append, Spec.flatMap_sliceList_eq_takeWhile h z] at hsplit
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hsplit
  have hstart := segStart_eq_length_takeWhile (n := n) h z
  have hprefix : (l.takeWhile fun c => c < (z + 1) * 10 ^ n) <+: l := List.takeWhile_prefix _
  have hpos : segStart n l z + t < (l.takeWhile fun c => c < (z + 1) * 10 ^ n).length := by
    rw [← hsplit, List.length_append, List.length_map, ← hstart]
    omega
  have hl : segStart n l z + t < l.length := hpos.trans_le hprefix.length_le
  have hmem : (Spec.sliceList n z l).getD t 0 ∈ Spec.sliceList n z l := by
    rw [List.getD_eq_getElem _ _ ht]
    exact List.getElem_mem ht
  refine ⟨hl, ?_, ((Spec.mem_sliceList h).1 hmem).1⟩
  rw [List.getD_eq_getElem _ _ hl, List.getD_eq_getElem _ _ ht, ← hprefix.getElem hpos]
  simp only [← hsplit]
  rw [List.getElem_append_right (by rw [← hstart]; omega)]
  simp [← hstart]

/-- A code between z pw and (z + 1) pw, without its first digit. -/
theorem mod_eq_sub_mul_of_lt {c z pw : ℕ} (hge : z * pw ≤ c) (hlt : c < (z + 1) * pw) :
    c % pw = c - z * pw := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hge
  rw [Nat.add_mul, Nat.one_mul] at hlt
  rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt (by omega), Nat.add_sub_cancel_left]

variable {n pw l bnd i z lo : ℕ} {codes : List ℕ} {μ μ' : ℕ → ℤ}

/-- Where the pass stands: the first i codes are below lo + pw, the others are at least
lo = z pw. -/
structure SegInv (pw : ℕ) (codes : List ℕ) (i z lo : ℕ) : Prop where
  i_le : i ≤ codes.length
  hz : z ≤ 10
  lo_eq : lo = z * pw
  below : ∀ i' < i, codes.getD i' 0 < lo + pw
  above : ∀ i', i ≤ i' → i' < codes.length → lo ≤ codes.getD i' 0

/-- The code at position i has first digit z. -/
theorem SegInv.copy (h : SegInv pw codes i z lo) (hi : i < codes.length)
    (hlt : codes.getD i 0 < lo + pw) : SegInv pw codes (i + 1) z lo := by
  refine ⟨hi, h.hz, h.lo_eq, fun i' hi' => ?_, fun i' h₁ h₂ => h.above i' (by omega) h₂⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt' | rfl
  · exact h.below i' hlt'
  · exact hlt

/-- No code that is left has first digit z. -/
theorem SegInv.advance (h : SegInv pw codes i z lo) (hz : z < 10)
    (hge : ∀ i', i ≤ i' → i' < codes.length → lo + pw ≤ codes.getD i' 0) :
    SegInv pw codes i (z + 1) (lo + pw) :=
  ⟨h.i_le, hz, by rw [h.lo_eq, Nat.succ_mul], fun i' hi' => by have := h.below i' hi'; omega, hge⟩

/-- Then the position reached is the start of the slice at z + 1. -/
theorem SegInv.segStart_succ (h : SegInv (10 ^ n) codes i z lo) (hsort : codes.Pairwise (· < ·))
    (hge : ∀ i', i ≤ i' → i' < codes.length → lo + 10 ^ n ≤ codes.getD i' 0) :
    segStart n codes (z + 1) = i := by
  rw [segStart_eq_length_takeWhile hsort, Nat.succ_mul, ← h.lo_eq]
  exact length_takeWhile_lt_eq h.i_le h.below hge

/-- The code at position i without its first digit. -/
theorem SegInv.mod_eq (h : SegInv pw codes i z lo) (hi : i < codes.length)
    (hlt : codes.getD i 0 < lo + pw) : codes.getD i 0 % pw + lo = codes.getD i 0 := by
  have hge := h.above i le_rfl hi
  rw [mod_eq_sub_mul_of_lt (z := z) (by rw [← h.lo_eq]; exact hge)
    (by rw [Nat.succ_mul, ← h.lo_eq]; exact hlt), ← h.lo_eq]
  omega

/-! ## The memory -/

/-- What has been written: the starts of the slices up to z, and the first i codes without their
first digits. -/
structure SegMem (n bnd : ℕ) (codes : List ℕ) (μ μ' : ℕ → ℤ) (i z : ℕ) : Prop where
  bounds : ∀ t ≤ z, μ' (bnd + t) = segStart n codes t
  copied : ∀ i' < i, μ' (bnd + 11 + i') = ((codes.getD i' 0 % 10 ^ n : ℕ) : ℤ)
  rest : SameOutside μ μ' bnd (11 + codes.length)

/-- One more code is copied. -/
theorem SegMem.copy (m : SegMem n bnd codes μ μ' i z) (hi : i < codes.length) (hz : z ≤ 10) :
    SegMem n bnd codes μ
      (Function.update μ' (bnd + 11 + i) ((codes.getD i 0 % 10 ^ n : ℕ) : ℤ)) (i + 1) z := by
  refine ⟨fun t ht => ?_, fun i' hi' => ?_, m.rest.update ⟨by omega, by omega⟩ _⟩
  · rw [Function.update_of_ne (by omega)]
    exact m.bounds t ht
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt | rfl
    · rw [Function.update_of_ne (by omega)]
      exact m.copied i' hlt
    · exact Function.update_self _ _ _

/-- The start of the next slice is noted. -/
theorem SegMem.advance (m : SegMem n bnd codes μ μ' i z) (hz : z < 10)
    (hstart : segStart n codes (z + 1) = i) :
    SegMem n bnd codes μ (Function.update μ' (bnd + (z + 1)) (i : ℤ)) i (z + 1) := by
  refine ⟨fun t ht => ?_, fun i' hi' => ?_, m.rest.update ⟨by omega, by omega⟩ _⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le ht) with hlt | rfl
    · rw [Function.update_of_ne (by omega)]
      exact m.bounds t (by omega)
    · rw [Function.update_self, hstart]
  · rw [Function.update_of_ne (by omega)]
    exact m.copied i' hi'

/-- When all codes are copied, the slice at z stands at the start of that slice. -/
theorem SegMem.slices (m : SegMem n bnd codes μ μ' codes.length 10)
    (hsort : codes.Pairwise (· < ·)) (z : ℕ) :
    SegN μ' (bnd + 11 + segStart n codes z) (Spec.sliceList n z codes) := by
  intro t ht
  have ht' : t < (Spec.sliceList n z codes).length := by simpa using ht
  obtain ⟨hpos, hcode, hlt⟩ := getD_segStart_add hsort z t ht'
  have hcell := m.copied _ hpos
  rw [hcode, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hlt, ← Nat.add_assoc] at hcell
  rw [hcell, List.getElem_map, List.getD_eq_getElem _ _ ht']

/-! ## The pass -/

variable {lim : Limits} {P : Program} {d : ℕ}

/-- What segBounds assumes. -/
structure SegPre (lim : Limits) (n l bnd : ℕ) (codes : List ℕ) (μ : ℕ → ℤ) : Prop where
  list : SegN μ l codes
  sorted : codes.Pairwise (· < ·)
  lt : ∀ x ∈ codes, x < 10 ^ (n + 1)
  below : l + codes.length ≤ bnd
  room : bnd + (11 + codes.length) ≤ lim.space
  word : ((100 * 10 ^ n : ℕ) : ℤ) ≤ lim.word

/-- The state of the loop. -/
abbrev segState (n l bnd : ℕ) (codes : List ℕ) (i z lo : ℕ) (μ' : ℕ → ℤ) : State :=
  ⟨frame [l, codes.length, (10 ^ n : ℕ), bnd, i, z, lo, (lo + 10 ^ n : ℕ)], μ'⟩

/-- The invariant of the loop. -/
def SegLoop (n l bnd : ℕ) (codes : List ℕ) (μ : ℕ → ℤ) (σ : State) : Prop :=
  ∃ (i z lo : ℕ) (μ' : ℕ → ℤ), σ = segState n l bnd codes i z lo μ' ∧
    SegInv (10 ^ n) codes i z lo ∧ SegMem n bnd codes μ μ' i z

/-- The codes and the first digits that are left. -/
def segRest (codes : List ℕ) (σ : State) : ℕ :=
  (codes.length - (σ.loc CI).toNat) + (10 - (σ.loc CZ).toNat)

/-- What a round that starts in σ achieves: the invariant holds again, and less is left. -/
def SegNext (n l bnd : ℕ) (codes : List ℕ) (μ : ℕ → ℤ) (σ σ' : State) : Prop :=
  SegLoop n l bnd codes μ σ' ∧ segRest codes σ' < segRest codes σ

/-- The list lies below what is written, so it can be read at any time. -/
theorem SegPre.read (pre : SegPre lim n l bnd codes μ) (m : SegMem n bnd codes μ μ' i z)
    (hi : i < codes.length) : μ' (l + i) = (codes.getD i 0 : ℕ) := by
  have := pre.below
  exact (m.rest _ (Or.inl (by omega))).trans (pre.list.read hi)

/-- The list increases. -/
theorem SegPre.mono (pre : SegPre lim n l bnd codes μ) {i i' : ℕ} (h₁ : i ≤ i')
    (h₂ : i' < codes.length) : codes.getD i 0 ≤ codes.getD i' 0 := by
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ h₂]
  rcases Nat.eq_or_lt_of_le h₁ with rfl | hlt
  · exact le_rfl
  · exact (List.pairwise_iff_getElem.1 pre.sorted i i' (by omega) h₂ hlt).le

/-- No code has first digit 10, so at z = 10 all codes are copied. -/
theorem SegPre.all_copied (pre : SegPre lim n l bnd codes μ)
    (inv : SegInv (10 ^ n) codes i 10 lo) : i = codes.length := by
  by_contra hne
  have hi : i < codes.length := lt_of_le_of_ne inv.i_le hne
  have hge := inv.above i le_rfl hi
  have hlt := pre.lt _ (List.getElem_mem hi)
  rw [List.getD_eq_getElem _ _ hi, inv.lo_eq] at hge
  rw [pow_succ'] at hlt
  omega

/-- lo = z 10^n is at most 10 · 10^n. -/
theorem SegInv.lo_le (h : SegInv pw codes i z lo) : lo ≤ 10 * pw :=
  h.lo_eq ▸ Nat.mul_le_mul_right _ h.hz

/-- The round in which a code is copied. -/
theorem segCopy_ends (std : Std lim) (pre : SegPre lim n l bnd codes μ)
    (inv : SegInv (10 ^ n) codes i z lo) (m : SegMem n bnd codes μ μ' i z) (hi : i < codes.length)
    (hlt : codes.getD i 0 < lo + 10 ^ n) :
    Ends lim P d segCopy (segState n l bnd codes i z lo μ') 16
      (SegNext n l bnd codes μ (segState n l bnd codes i z lo μ')) := by
  light_facts std pre
  have hread := pre.read m hi
  have hmod := inv.mod_eq hi hlt
  have hlo := inv.lo_le
  have hmodlt : codes.getD i 0 % 10 ^ n < 10 ^ n := Nat.mod_lt _ (by positivity)
  simp only [List.getD_eq_getElem?_getD] at hread hmod hmodlt
  unfold segCopy
  -- mem[bnd + 11 + i] := mem[l + i] - lo
  refine Ends.storeToThen (bnd + 11 + i) ((codes.getD i 0 % 10 ^ n : ℕ) : ℤ) ?_
    (by generalize 10 ^ n = pw at *; simp [Limits.Addr, abs_le, hread]; omega)
  -- i := i + 1
  light_set (i + 1 : ℕ)
  exact ⟨⟨i + 1, z, lo, _, rfl, inv.copy hi hlt, m.copy hi inv.hz⟩, by simp [segRest]; omega⟩

/-- The round in which the pass goes on to the next first digit. -/
theorem segAdvance_ends (std : Std lim) (pre : SegPre lim n l bnd codes μ)
    (inv : SegInv (10 ^ n) codes i z lo) (m : SegMem n bnd codes μ μ' i z) (hz : z < 10)
    (hge : ∀ i', i ≤ i' → i' < codes.length → lo + 10 ^ n ≤ codes.getD i' 0) :
    Ends lim P d segAdvance (segState n l bnd codes i z lo μ') 15
      (SegNext n l bnd codes μ (segState n l bnd codes i z lo μ')) := by
  light_facts std pre
  have hile := inv.i_le
  have hlo := inv.lo_le
  unfold segAdvance
  -- z := z + 1
  light_set (z + 1 : ℕ)
  -- mem[bnd + z] := i
  light_store (bnd + (z + 1)) i
  -- lo := hi
  light_set (lo + 10 ^ n : ℕ)
  -- hi := hi + pw
  refine Ends.setTo (lo + 10 ^ n + 10 ^ n : ℕ) ?_
    (by generalize 10 ^ n = pw at *; simp [abs_le]; omega)
  exact ⟨⟨i, z + 1, lo + 10 ^ n, _, rfl, inv.advance hz hge,
    m.advance hz (inv.segStart_succ pre.sorted hge)⟩, by simp [segRest]; omega⟩

/-- **segBounds**: a call takes at most cSegBounds (codes.length + 11) steps.  Afterwards the cells
bnd to bnd + 10 hold the starts of the ten slices and the end of the last one, the slice at z stands
at bnd + 11 + segStart n codes z, and no other cell has changed. -/
theorem segBounds_entry (std : Std lim) (hP : P[pSegBounds]? = some segBoundsBody) {c : ℕ}
    (hc : cSegBounds ≤ c) : SegBoundsSpec lim P c := by
  intro n l bnd codes μ hseg hsort hlt hlb hsp hword d _
  have pre : SegPre lim n l bnd codes μ :=
    ⟨hseg, hsort, hlt, hlb, hsp, by rwa [pow_add, mul_comm] at hword⟩
  light_facts std pre
  refine .mono_const (.of_body hP ?_) hc
  unfold segBoundsBody cSegBounds
  -- i := 0; z := 0; lo := 0; hi := pw
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set (0 + 10 ^ n : ℕ)
  -- mem[bnd] := 0
  light_store bnd 0
  -- while z < 10
  refine Ends.whileVariant (SegLoop n l bnd codes μ) (segRest codes) 27 ?start
    (fun _ _ => ⟨trivial, by simp; omega⟩) ?round ?done (by simp [segRest]; omega)
  case start =>
    refine ⟨0, 0, 0, _, rfl, ⟨Nat.zero_le _, Nat.zero_le _, by simp, fun _ h => absurd h (by omega),
      fun _ _ _ => Nat.zero_le _⟩, fun t ht => ?_, fun _ h => absurd h (by omega),
      SameOutside.refl.update ⟨by omega, by omega⟩ _⟩
    obtain rfl : t = 0 := by omega
    simp [segStart]
  case round =>
    rintro _ ⟨i, z, lo, μ', rfl, inv, m⟩ hz
    replace hz : z < 10 := by simpa using hz
    -- if i < len
    refine Ends.iteLast (fun hmore => ?_) (fun hmore => ?_)
    · replace hmore : i < codes.length := by simpa using hmore
      have hread := pre.read m hmore
      -- if mem[l + i] < hi
      refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
      · replace hc : ((codes.getD i 0 : ℕ) : ℤ) < (lo + 10 ^ n : ℕ) := by simpa [hread] using hc
        exact segCopy_ends std pre inv m hmore (by exact_mod_cast hc)
      · replace hc : ((lo + 10 ^ n : ℕ) : ℤ) ≤ (codes.getD i 0 : ℕ) := by simpa [hread] using hc
        replace hc : lo + 10 ^ n ≤ codes.getD i 0 := by exact_mod_cast hc
        exact (segAdvance_ends std pre inv m hz fun i' h₁ h₂ =>
          hc.trans (pre.mono h₁ h₂)).mono (by light_time) fun _ h => h
    · replace hmore : ¬ i < codes.length := by simpa using hmore
      exact (segAdvance_ends std pre inv m hz fun i' h₁ h₂ => absurd h₂ (by omega)).mono
        (by light_time) fun _ h => h
  case done =>
    rintro _ ⟨i, z, lo, μ', rfl, inv, m⟩ hz
    obtain rfl : z = 10 := le_antisymm inv.hz (by simpa using hz)
    obtain rfl : i = codes.length := pre.all_copied inv
    exact ⟨m.bounds, fun z _ => m.slices hsort z, m.rest⟩

end Light.Sec2
