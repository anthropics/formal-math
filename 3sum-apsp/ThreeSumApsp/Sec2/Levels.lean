/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements

/-!
# Strings cut along a set of levels

Section 2.3.3 cuts a string of `L` variables along a set `Q` of `m` levels: its variables
at the levels of `Q`, in the order of the levels, form a string of length `m`, and its variables at
the other levels form a string of length `L - m`. The first three parts of this file hold for every
alphabet; the last part specializes them to left, right and output strings.

* Every level is the `k`-th lowest level of `Q` or the `k`-th lowest level outside `Q` for some `k`.
  So a statement about all levels is checked on these two kinds of levels (`forall_level_iff`), and
  so is the statement that a set of levels is `Q` (`filter_eq_iff_forall_level`).
* `glue Q hQ f g` is the string with the letters of `f` at the levels of `Q` and the letters of `g`
  at the other levels. It is the only such string (`eq_glue_iff`), and `f` and `g` can be read off
  it (`glue_inj`).
* If the letters are of two kinds, inner and outer, and each is given by its kind and an index, then
  a string can be rebuilt from its inner set and the indices of its letters (`glue_index`).
* "A string is determined by its inner set, its outer part, and its inner part": the strings
  `leftStrOf Q hQ r π`, `rightStrOf Q hQ π c` and `outStrOf Q hQ r c` have the parts that their
  names say, and no other string has them (`existsUnique_leftStr`, `existsUnique_rightStr`,
  `existsUnique_outStr`). No later proof uses these three statements; the later proofs use the
  lemmas from which they follow.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)

/-! ### The levels of a set and of its complement, in order -/

/-- The `k`-th lowest level of `Q` is a level of `Q`. -/
theorem innerLevel_mem (k : Fin m) : innerLevel Q hQ k ∈ Q :=
  Q.orderEmbOfFin_mem hQ k

/-- The `k`-th lowest level outside `Q` is not a level of `Q`. -/
theorem outerLevel_notMem (k : Fin (L - m)) : outerLevel Q hQ k ∉ Q :=
  mem_compl.mp (Qᶜ.orderEmbOfFin_mem (card_compl_of_card_eq Q hQ) k)

/-- Every level of `Q` is the `k`-th lowest level of `Q` for some `k`. -/
theorem exists_innerLevel {ℓ : Fin L} (hℓ : ℓ ∈ Q) : ∃ k, innerLevel Q hQ k = ℓ :=
  (Q.range_orderEmbOfFin hQ).ge hℓ

/-- Every level outside `Q` is the `k`-th lowest level outside `Q` for some `k`. -/
theorem exists_outerLevel {ℓ : Fin L} (hℓ : ℓ ∉ Q) : ∃ k, outerLevel Q hQ k = ℓ :=
  (Qᶜ.range_orderEmbOfFin (card_compl_of_card_eq Q hQ)).ge (mem_coe.mpr (mem_compl.mpr hℓ))

/-- The levels of `Q` in order depend only on the set `Q`. -/
theorem innerLevel_congr {Q' : Finset (Fin L)} (h : Q' = Q) (hQ' : Q'.card = m) :
    innerLevel Q' hQ' = innerLevel Q hQ := by
  subst h
  rfl

/-- The levels outside `Q` in order depend only on the set `Q`. -/
theorem outerLevel_congr {Q' : Finset (Fin L)} (h : Q' = Q) (hQ' : Q'.card = m) :
    outerLevel Q' hQ' = outerLevel Q hQ := by
  subst h
  rfl

/-- A property holds at every level if and only if it holds at the levels of `Q` and at the levels
outside `Q`. -/
theorem forall_level_iff {P : Fin L → Prop} :
    (∀ ℓ, P ℓ) ↔ (∀ k, P (innerLevel Q hQ k)) ∧ ∀ k, P (outerLevel Q hQ k) := by
  refine ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩, fun ⟨hin, hout⟩ ℓ => ?_⟩
  by_cases hℓ : ℓ ∈ Q
  · obtain ⟨k, rfl⟩ := exists_innerLevel Q hQ hℓ
    exact hin k
  · obtain ⟨k, rfl⟩ := exists_outerLevel Q hQ hℓ
    exact hout k

/-- A property cuts out the set `Q` if and only if it holds at the levels of `Q` and fails at the
other levels. -/
theorem filter_eq_iff_forall_level {P : Fin L → Prop} [DecidablePred P] :
    univ.filter P = Q ↔ (∀ k, P (innerLevel Q hQ k)) ∧ ∀ k, ¬ P (outerLevel Q hQ k) := by
  simp only [Finset.ext_iff, forall_level_iff Q hQ, mem_filter, mem_univ, true_and,
    innerLevel_mem, outerLevel_notMem, iff_true, iff_false]

/-- A property that holds at the `m` levels of `Q`, and at `m` levels in all, cuts out `Q`. -/
theorem filter_eq_of_forall_innerLevel {P : Fin L → Prop} [DecidablePred P]
    (hin : ∀ k, P (innerLevel Q hQ k)) (hcard : (univ.filter P).card = m) : univ.filter P = Q := by
  refine (eq_of_subset_of_card_le (fun ℓ hℓ => ?_) (hcard.trans hQ.symm).le).symm
  obtain ⟨k, rfl⟩ := exists_innerLevel Q hQ hℓ
  exact mem_filter.mpr ⟨mem_univ _, hin k⟩

/-! ### Gluing two strings along a set of levels -/

variable {α : Type*}

/-- The string that has the letters of `f` at the levels of `Q` and the letters of `g` at the other
levels, both in the order of the levels. -/
def glue (f : Fin m → α) (g : Fin (L - m) → α) : Fin L → α :=
  fun ℓ =>
    if hℓ : ℓ ∈ Q then f ((Q.orderIsoOfFin hQ).symm ⟨ℓ, hℓ⟩)
    else g ((Qᶜ.orderIsoOfFin (card_compl_of_card_eq Q hQ)).symm ⟨ℓ, mem_compl.mpr hℓ⟩)

/-- At the `k`-th lowest level of `Q`, the glued string has the `k`-th letter of `f`. -/
@[simp]
theorem glue_innerLevel (f : Fin m → α) (g : Fin (L - m) → α) (k : Fin m) :
    glue Q hQ f g (innerLevel Q hQ k) = f k := by
  rw [glue, dif_pos (innerLevel_mem Q hQ k)]
  exact congrArg f ((OrderIso.symm_apply_eq _).mpr (Subtype.ext rfl))

/-- At the `k`-th lowest level outside `Q`, the glued string has the `k`-th letter of `g`. -/
@[simp]
theorem glue_outerLevel (f : Fin m → α) (g : Fin (L - m) → α) (k : Fin (L - m)) :
    glue Q hQ f g (outerLevel Q hQ k) = g k := by
  rw [glue, dif_neg (outerLevel_notMem Q hQ k)]
  exact congrArg g ((OrderIso.symm_apply_eq _).mpr (Subtype.ext rfl))

/-- At the `k`-th lowest level of a set `Q'` that is equal to `Q`, the string glued along `Q` has
the `k`-th letter of `f`. -/
private theorem glue_innerLevel_of_eq (f : Fin m → α) (g : Fin (L - m) → α) {Q' : Finset (Fin L)}
    (h : Q' = Q) (hQ' : Q'.card = m) (k : Fin m) : glue Q hQ f g (innerLevel Q' hQ' k) = f k := by
  rw [innerLevel_congr Q hQ h, glue_innerLevel]

/-- At the `k`-th lowest level outside a set `Q'` that is equal to `Q`, the string glued along `Q`
has the `k`-th letter of `g`. -/
private theorem glue_outerLevel_of_eq (f : Fin m → α) (g : Fin (L - m) → α) {Q' : Finset (Fin L)}
    (h : Q' = Q) (hQ' : Q'.card = m) (k : Fin (L - m)) :
    glue Q hQ f g (outerLevel Q' hQ' k) = g k := by
  rw [outerLevel_congr Q hQ h, glue_outerLevel]

variable {f f' : Fin m → α} {g g' : Fin (L - m) → α}

/-- The glued string is the only string with the letters of `f` at the levels of `Q` and the letters
of `g` at the other levels. -/
theorem eq_glue_iff {u : Fin L → α} :
    u = glue Q hQ f g
      ↔ (∀ k, u (innerLevel Q hQ k) = f k) ∧ ∀ k, u (outerLevel Q hQ k) = g k := by
  simp only [funext_iff, forall_level_iff Q hQ, glue_innerLevel, glue_outerLevel]

/-- The two strings can be read off the glued string. -/
theorem glue_inj : glue Q hQ f g = glue Q hQ f' g' ↔ f = f' ∧ g = g' := by
  rw [eq_glue_iff]
  simp only [glue_innerLevel, glue_outerLevel, funext_iff]

/-- A map applied to a glued string, letter by letter. -/
theorem map_glue {β : Type*} (φ : α → β) :
    (fun ℓ => φ (glue Q hQ f g ℓ)) = glue Q hQ (fun k => φ (f k)) (fun k => φ (g k)) := by
  simp only [eq_glue_iff, glue_innerLevel, glue_outerLevel, implies_true, and_self]

/-! ### Alphabets with inner and outer letters -/

variable (IsInner : α → Prop) [DecidablePred IsInner]

/-- If the letters of `f` are inner and those of `g` are outer, then the glued string has its inner
letters exactly at the levels of `Q`. -/
theorem filter_glue (hf : ∀ k, IsInner (f k)) (hg : ∀ k, ¬ IsInner (g k)) :
    (univ.filter fun ℓ => IsInner (glue Q hQ f g ℓ)) = Q := by
  simpa only [filter_eq_iff_forall_level Q hQ, glue_innerLevel, glue_outerLevel] using
    And.intro hf hg

/-- Let every inner letter `s` be `inner i` for its index `i = innerIndex s`, and every outer letter
be `outer o` for its index `o = outerIndex s`. Then a string whose inner letters are at the levels
of `Q` is rebuilt by gluing the letters `inner i` and `outer o` for the indices of its letters. -/
theorem glue_index {I O : Type*} {inner : I → α} {outer : O → α} {innerIndex : α → I}
    {outerIndex : α → O} (hI : ∀ s, IsInner s → inner (innerIndex s) = s)
    (hO : ∀ s, ¬ IsInner s → outer (outerIndex s) = s) {u : Fin L → α}
    (hu : (univ.filter fun ℓ => IsInner (u ℓ)) = Q) :
    u = glue Q hQ (fun k => inner (innerIndex (u (innerLevel Q hQ k))))
      (fun k => outer (outerIndex (u (outerLevel Q hQ k)))) := by
  obtain ⟨hin, hout⟩ := (filter_eq_iff_forall_level Q hQ).mp hu
  exact (eq_glue_iff Q hQ).mpr ⟨fun k => (hI _ (hin k)).symm, fun k => (hO _ (hout k)).symm⟩

/-! ### Left, right and output strings with a given inner set, outer part and inner part -/

/-- The left string with inner set `Q`, outer part `r` and inner part `π`. -/
def leftStrOf (r : OuterStr L m) (π : InnerStr m) : LeftStr L :=
  glue Q hQ (fun k => .p (π k).1 (π k).2) (fun k => .x (r k))

/-- The right string with inner set `Q`, inner part `π` and outer part `c`. -/
def rightStrOf (π : InnerStr m) (c : OuterStr L m) : RightStr L :=
  glue Q hQ (fun k => .q (π k).1 (π k).2) (fun k => .y (c k))

/-- The output string with inner set `Q`, row `r` and column `c` (Section 2.3.3: "the output strings
with inner set Q index the entries of the product X_Q Y_Q"): it has `z₀` at the levels of `Q`, and
at the `k`-th lowest level outside `Q` it has `z_{r_k c_k}`. -/
def outStrOf (r c : OuterStr L m) : OutStr L :=
  glue Q hQ (fun _ => .z0) (fun k => .z (r k) (c k))

/-- The inner set of `leftStrOf Q hQ r π` is `Q`. -/
@[simp]
theorem innerSetL_leftStrOf (r : OuterStr L m) (π : InnerStr m) :
    innerSetL (leftStrOf Q hQ r π) = Q :=
  filter_glue Q hQ LeftVar.IsInner (fun _ => trivial) fun _ => id

/-- The inner set of `rightStrOf Q hQ π c` is `Q`. -/
@[simp]
theorem innerSetR_rightStrOf (π : InnerStr m) (c : OuterStr L m) :
    innerSetR (rightStrOf Q hQ π c) = Q :=
  filter_glue Q hQ RightVar.IsInner (fun _ => trivial) fun _ => id

/-- The inner set of `outStrOf Q hQ r c` is `Q`. -/
@[simp]
theorem innerSetO_outStrOf (r c : OuterStr L m) : innerSetO (outStrOf Q hQ r c) = Q :=
  filter_glue Q hQ OutVar.IsInner (fun _ => trivial) fun _ => id

/-- The outer part of `leftStrOf Q hQ r π` is `r`. -/
@[simp]
theorem outerPartL_leftStrOf (r : OuterStr L m) (π : InnerStr m)
    (h : (innerSetL (leftStrOf Q hQ r π)).card = m) : outerPartL (leftStrOf Q hQ r π) h = r :=
  funext fun k => congrArg LeftVar.outerIndex
    (glue_outerLevel_of_eq Q hQ _ _ (innerSetL_leftStrOf Q hQ r π) h k)

/-- The inner part of `leftStrOf Q hQ r π` is `π`. -/
@[simp]
theorem innerPartL_leftStrOf (r : OuterStr L m) (π : InnerStr m)
    (h : (innerSetL (leftStrOf Q hQ r π)).card = m) : innerPartL (leftStrOf Q hQ r π) h = π :=
  funext fun k => congrArg LeftVar.innerIndex
    (glue_innerLevel_of_eq Q hQ _ _ (innerSetL_leftStrOf Q hQ r π) h k)

/-- The inner part of `rightStrOf Q hQ π c` is `π`. -/
@[simp]
theorem innerPartR_rightStrOf (π : InnerStr m) (c : OuterStr L m)
    (h : (innerSetR (rightStrOf Q hQ π c)).card = m) : innerPartR (rightStrOf Q hQ π c) h = π :=
  funext fun k => congrArg RightVar.innerIndex
    (glue_innerLevel_of_eq Q hQ _ _ (innerSetR_rightStrOf Q hQ π c) h k)

/-- The outer part of `rightStrOf Q hQ π c` is `c`. -/
@[simp]
theorem outerPartR_rightStrOf (π : InnerStr m) (c : OuterStr L m)
    (h : (innerSetR (rightStrOf Q hQ π c)).card = m) : outerPartR (rightStrOf Q hQ π c) h = c :=
  funext fun k => congrArg RightVar.outerIndex
    (glue_outerLevel_of_eq Q hQ _ _ (innerSetR_rightStrOf Q hQ π c) h k)

/-- The variable of `outStrOf Q hQ r c` at the `k`-th lowest level outside its inner set. -/
private theorem outStrOf_outerLevel (r c : OuterStr L m)
    (h : (innerSetO (outStrOf Q hQ r c)).card = m) (k : Fin (L - m)) :
    outStrOf Q hQ r c (outerLevel (innerSetO (outStrOf Q hQ r c)) h k) = .z (r k) (c k) := by
  rw [outerLevel_congr Q hQ (innerSetO_outStrOf Q hQ r c), outStrOf, glue_outerLevel]

/-- The row of `outStrOf Q hQ r c` is `r`. -/
@[simp]
theorem rowO_outStrOf (r c : OuterStr L m) (h : (innerSetO (outStrOf Q hQ r c)).card = m) :
    rowO (outStrOf Q hQ r c) h = r :=
  funext fun k => congrArg OutVar.rowIndex (outStrOf_outerLevel Q hQ r c h k)

/-- The column of `outStrOf Q hQ r c` is `c`. -/
@[simp]
theorem colO_outStrOf (r c : OuterStr L m) (h : (innerSetO (outStrOf Q hQ r c)).card = m) :
    colO (outStrOf Q hQ r c) h = c :=
  funext fun k => congrArg OutVar.colIndex (outStrOf_outerLevel Q hQ r c h k)

variable {Q}

/-- A left string with inner set `Q` is the string `leftStrOf` of its outer part and its inner
part. -/
theorem leftStr_eq_leftStrOf {u : LeftStr L} (hu : innerSetL u = Q) (h : (innerSetL u).card = m) :
    u = leftStrOf Q hQ (outerPartL u h) (innerPartL u h) := by
  subst hu
  refine glue_index _ h LeftVar.IsInner (inner := fun π : Fin 2 × Fin 2 => .p π.1 π.2) ?_ ?_ rfl
  · rintro (i | ⟨i, j⟩) hs
    exacts [hs.elim, rfl]
  · rintro (i | ⟨i, j⟩) hs
    exacts [rfl, (hs trivial).elim]

/-- A right string with inner set `Q` is the string `rightStrOf` of its inner part and its outer
part. -/
theorem rightStr_eq_rightStrOf {v : RightStr L} (hv : innerSetR v = Q)
    (h : (innerSetR v).card = m) : v = rightStrOf Q hQ (innerPartR v h) (outerPartR v h) := by
  subst hv
  refine glue_index _ h RightVar.IsInner (inner := fun π : Fin 2 × Fin 2 => .q π.1 π.2) ?_ ?_ rfl
  · rintro (j | ⟨i, j⟩) ht
    exacts [ht.elim, rfl]
  · rintro (j | ⟨i, j⟩) ht
    exacts [rfl, (ht trivial).elim]

/-- An output string with inner set `Q` is the string `outStrOf` of its row and its column. -/
theorem outStr_eq_outStrOf {w : OutStr L} (hw : innerSetO w = Q) (h : (innerSetO w).card = m) :
    w = outStrOf Q hQ (rowO w h) (colO w h) := by
  subst hw
  refine glue_index _ h OutVar.IsInner (inner := fun _ : Unit => .z0)
    (outer := fun rc : Fin 3 × Fin 3 => .z rc.1 rc.2) (innerIndex := fun _ => ())
    (outerIndex := fun z => (z.rowIndex, z.colIndex)) ?_ ?_ rfl
  · rintro (⟨i, j⟩ | _) hz
    exacts [hz.elim, rfl]
  · rintro (⟨i, j⟩ | _) hz
    exacts [rfl, (hz trivial).elim]

variable {hQ}

/-- Left strings with the same inner set and different outer or inner parts are different. -/
theorem leftStrOf_inj {r r' : OuterStr L m} {π π' : InnerStr m} :
    leftStrOf Q hQ r π = leftStrOf Q hQ r' π' ↔ r = r' ∧ π = π' := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  obtain ⟨hp, hx⟩ := (glue_inj Q hQ).mp h
  exact ⟨funext fun k => LeftVar.x.inj (congrFun hx k),
    funext fun k => Prod.ext (LeftVar.p.inj (congrFun hp k)).1 (LeftVar.p.inj (congrFun hp k)).2⟩

/-- Output strings with different inner sets, rows or columns are different. -/
theorem outStrOf_inj {Q' : Finset (Fin L)} {hQ' : Q'.card = m} {r c r' c' : OuterStr L m} :
    outStrOf Q hQ r c = outStrOf Q' hQ' r' c' ↔ Q = Q' ∧ r = r' ∧ c = c' := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl, rfl⟩; rfl⟩
  obtain rfl : Q = Q' := by rw [← innerSetO_outStrOf Q hQ r c, h, innerSetO_outStrOf]
  have hz := fun k => OutVar.z.inj (congrFun ((glue_inj Q hQ).mp h).2 k)
  exact ⟨rfl, funext fun k => (hz k).1, funext fun k => (hz k).2⟩

variable (Q) (hQ)
include hQ

/-- Section 2.3.3: "A string is determined by its inner set, its outer part, and its inner part",
and "the left strings with inner set Q index the entries of such a matrix": for each set `Q` of `m`
levels, each row `r` and each column `π` there is exactly one left string with inner set `Q`, outer
part `r` and inner part `π`. -/
theorem existsUnique_leftStr (r : OuterStr L m) (π : InnerStr m) :
    ∃! u : LeftStr L, innerSetL u = Q
      ∧ ∃ h : (innerSetL u).card = m, outerPartL u h = r ∧ innerPartL u h = π := by
  have hset := innerSetL_leftStrOf Q hQ r π
  refine ⟨leftStrOf Q hQ r π, ⟨hset, hset.symm ▸ hQ, outerPartL_leftStrOf Q hQ r π _,
    innerPartL_leftStrOf Q hQ r π _⟩, ?_⟩
  rintro u ⟨hu, h, rfl, rfl⟩
  exact leftStr_eq_leftStrOf hQ hu h

/-- Section 2.3.3: "Similarly, the right strings v with inner set Q index the entries of a D × N₀
matrix". -/
theorem existsUnique_rightStr (π : InnerStr m) (c : OuterStr L m) :
    ∃! v : RightStr L, innerSetR v = Q
      ∧ ∃ h : (innerSetR v).card = m, innerPartR v h = π ∧ outerPartR v h = c := by
  have hset := innerSetR_rightStrOf Q hQ π c
  refine ⟨rightStrOf Q hQ π c, ⟨hset, hset.symm ▸ hQ,
    innerPartR_rightStrOf Q hQ π c _, outerPartR_rightStrOf Q hQ π c _⟩, ?_⟩
  rintro v ⟨hv, h, rfl, rfl⟩
  exact rightStr_eq_rightStrOf hQ hv h

/-- Section 2.3.3: "Finally, the output strings with inner set Q index the entries of the product
X_Q Y_Q". -/
theorem existsUnique_outStr (r c : OuterStr L m) :
    ∃! w : OutStr L, innerSetO w = Q
      ∧ ∃ h : (innerSetO w).card = m, rowO w h = r ∧ colO w h = c := by
  have hset := innerSetO_outStrOf Q hQ r c
  refine ⟨outStrOf Q hQ r c, ⟨hset, hset.symm ▸ hQ, rowO_outStrOf Q hQ r c _,
    colO_outStrOf Q hQ r c _⟩, ?_⟩
  rintro w ⟨hw, h, rfl, rfl⟩
  exact outStr_eq_outStrOf hQ hw h

end ThreeSumApsp
