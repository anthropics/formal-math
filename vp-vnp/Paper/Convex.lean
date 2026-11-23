/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Curvature
import Paper.Alternative
import Nc.Price.BorderFew
import Nc.CaseI.Cube

/-!
# The paper, section "The main theorem": sums with few terms and the price of a set
-/

namespace Paper

open Finset Nc Nc.Price Nc.CaseI Ov

/-- **Paper: Lemma lem:few.** "Let P ⊆ V, let t be a tensor on P and T_1, …, T_J tensors on V, and suppose that
t = ∑_j ⟨f_j|T_j⟩, where each f_j consists of one functional at every party outside P. Then φ(t) ≤ J^g(P) max_j φ(T_j)
for every spectral point on V." (A tensor on P is one on V with legs of size at most one outside P.) -/
theorem lem_few {K : Type} [Field K] {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (φ : Spec K V) (P : Finset V)
    (t : Ten K V) (ht : ∀ q, q ∉ P → Subsingleton (t.ι q)) {J : ℕ} [NeZero J] (T : Fin J → Ten K V)
    (h : Ten.SumRestr t T) :
    φ.F t ≤ (J : ℝ) ^ hexp φ (Subtype.val : P → V) * univ.sup' univ_nonempty fun j => φ.F (T j) := by
  have := few φ (Subtype.val : P → V) t (fun q hq => ht q fun hmem => hq ⟨⟨q, hmem⟩, rfl⟩) (BSum.of_sumRestr h)
    (M := univ.sup' univ_nonempty fun j => φ.F (T j)) (fun j => Finset.le_sup' (fun j => φ.F (T j)) (mem_univ j))
  rwa [Fintype.card_fin] at this

section Steps

/-! The steps of the proof of Lemma lem:convex: the new parties are placed at random by Proposition prop:extend, and
Theorem thm:cn bounds how far they are from the midpoints. -/


variable {K : Type} [Field K] {P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

/-- Let σ l, with weights θ l ≥ 0 of sum 1, map new parties Q to the
parties P. A spectral point F over P has an extension F' to P ⊕ Q that is, at every tensor, at most the weighted geometric mean of
the values of F at the tensors with the legs moved by σ l. It has the same distances on P and the same value at a given
tensor C over P. -/
theorem exists_mix_spec_keep (F : Spec K P) (θ : Fin 2 → ℝ) (hθ : ∀ l, 0 ≤ θ l)
    (hθ1 : ∑ l, θ l = 1) (σ : Fin 2 → Q → P) (C : Ten K P) (hC : 0 < F.F C) :
    ∃ F' : Spec K (P ⊕ Q), (∀ t, F'.F t ≤ ∏ l, F.F (Ten.push (Sum.elim id (σ l)) t) ^ θ l) ∧
      (∀ p p', F'.e (Sum.inl p) (Sum.inl p') = F.e p p') ∧ F'.F (Ten.push Sum.inl C) = F.F C := by
  classical
  set W : Ten K P := Ten.prod fun e : P × P => Ten.wire K 2 e.1 e.2 with hW
  obtain ⟨F', hle, hWC⟩ := prop_extend (K := K) (Sum.inl : P → P ⊕ Q)
    (fun l => Sum.elim id (σ l)) (fun l i => rfl) θ hθ hθ1 F (W * C)
  -- on tensors over P the extension is not larger
  have hA : ∀ A : Ten K P, 0 < F.F A → F'.F (Ten.push Sum.inl A) ≤ F.F A := by
    intro A h0
    refine (hle _).trans (le_of_eq ?_)
    have h1 : ∀ l, F.F (Ten.push (Sum.elim id (σ l)) (Ten.push Sum.inl A)) = F.F A := by
      intro l
      have h := Ten.Equi.push_push (Sum.elim id (σ l)) (Sum.inl : P → P ⊕ Q) A
      rw [show Sum.elim id (σ l) ∘ (Sum.inl : P → P ⊕ Q) = id from rfl] at h
      exact F.congr (h.trans (Ten.Equi.push_id _))
    simp only [h1]
    rw [← Real.rpow_sum_of_pos h0, hθ1, Real.rpow_one]
  have hW0 : 0 < F.F W := by
    rw [hW, F.prod]
    exact Finset.prod_pos fun e _ => by rw [F.wire_two]; positivity
  rw [F'.congr (Ten.Equi.push_mul _ W C), F'.mul, F.mul] at hWC
  have h1 := hA W hW0
  have h2 := hA C hC
  have h3 : 0 ≤ F'.F (Ten.push Sum.inl W) := F'.nonneg _
  have h4 : 0 ≤ F'.F (Ten.push Sum.inl C) := F'.nonneg _
  have hC' : F'.F (Ten.push Sum.inl C) = F.F C := by
    refine le_antisymm h2 (not_lt.1 fun hlt => ?_)
    have : F'.F (Ten.push Sum.inl W) * F'.F (Ten.push Sum.inl C) < F.F W * F.F C :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right h1 h4) (mul_lt_mul_of_pos_left hlt hW0)
    exact this.ne hWC
  have hW' : F'.F (Ten.push Sum.inl W) = F.F W := by
    rw [hC'] at hWC
    exact mul_right_cancel₀ hC.ne' hWC
  refine ⟨F', hle, ?_, hC'⟩
  have hle' : ∀ p p', F'.e (Sum.inl p) (Sum.inl p') ≤ F.e p p' := by
    intro p p'
    have h := hA (Ten.wire K 2 p p') (by rw [F.wire_two]; positivity)
    rw [← F'.pull_F, (F'.pull _).wire_two, F'.pull_e, F.wire_two] at h
    exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h
  have hsum : ∑ e : P × P, F'.e (Sum.inl e.1) (Sum.inl e.2) = ∑ e : P × P, F.e e.1 e.2 := by
    rw [← F'.pull_F, hW, (F'.pull _).prod, F.prod] at hW'
    simp only [Spec.wire_two, Spec.pull_e] at hW'
    rw [← Real.rpow_sum_of_pos (by norm_num), ← Real.rpow_sum_of_pos (by norm_num)] at hW'
    have h2 := congrArg (Real.logb 2) hW'
    rwa [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_rpow (by norm_num) (by norm_num)]
      at h2
  intro p p'
  exact (Finset.sum_eq_sum_iff_of_le (fun (e : P × P) _ => hle' e.1 e.2)).1 hsum (p, p')
    (Finset.mem_univ _)

/-- Exponents: a power of two below the geometric mean of two powers of two. -/
theorem le_mean_of_two_rpow_le {r s t : ℝ}
    (h : (2 : ℝ) ^ r ≤ ∏ l : Fin 2, ((2 : ℝ) ^ (![s, t] l)) ^ (1 / 2 : ℝ)) : r ≤ (s + t) / 2 := by
  rw [Fin.prod_univ_two] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)] at h
  have := (Real.rpow_le_rpow_left_iff (by norm_num)).1 h
  linarith

variable {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]

/-- Let a, b, m map A to the parties V. A spectral point F over V has an extension
F' with a new party for every element of A, placed half at a and half at b: distances from new parties and the exponent of the
unit tensor on the new parties are at most the means of the two values for F. The distances on V and the exponent of the unit
tensor at m do not change. -/
theorem exists_mix_hexp [Nonempty V] (F : Spec K V) (a b m : A → V) :
    ∃ F' : Spec K (V ⊕ A), (∀ p p', F'.e (Sum.inl p) (Sum.inl p') = F.e p p') ∧
      hexp F' (Sum.inl ∘ m) = hexp F m ∧
      (∀ x y, F'.e x y ≤
        (F.e (Sum.elim id a x) (Sum.elim id a y) + F.e (Sum.elim id b x) (Sum.elim id b y)) / 2) ∧
      hexp F' Sum.inr ≤ (hexp F a + hexp F b) / 2 := by
  obtain ⟨F', hle, he, hC⟩ := exists_mix_spec_keep F (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun _ => by norm_num)
    (by norm_num) ![a, b] (Ten.push m (Ten.unit K A 2))
    (lt_of_lt_of_le one_pos (F.one_le_unit m (by norm_num)))
  refine ⟨F', he, ?_, fun x y => ?_, ?_⟩
  · rw [← hexp_pull, hexp, hexp, Spec.pull_F, hC]
  · have h := hle (Ten.wire K 2 x y)
    rw [F'.wire_two] at h
    refine le_mean_of_two_rpow_le (h.trans (le_of_eq ?_))
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← F.pull_F, (F.pull _).wire_two, F.pull_e]
    fin_cases l <;> rfl
  · have h := hle (Ten.push Sum.inr (Ten.unit K A 2))
    rw [unit_two_eq_rpow_hexp] at h
    refine le_mean_of_two_rpow_le (h.trans (le_of_eq ?_))
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← F.pull_F, unit_two_eq_rpow_hexp, hexp_pull]
    fin_cases l <;> rfl

/-- Let v be a midpoint of x and y for a price w, and let z have the distance at most
w(x, y)/2 + δ from x and from y. Then w(z, v)² ≤ w(x, y) δ + δ². -/
theorem sq_dist_midpoint_le {Y : Type} {w : Y → Y → ℝ} (hw : IsPrice K w) {x y v z : Y} {δ : ℝ}
    (hx : w x v ≤ w x y / 2) (hy : w y v ≤ w x y / 2) (hzx : w z x ≤ w x y / 2 + δ)
    (hzy : w z y ≤ w x y / 2 + δ) : w z v ^ 2 ≤ w x y * δ + δ ^ 2 := by
  have h := thm_cn hw x y v z hx hy (by ring)
  have h1 := hw.nonneg z x
  have h2 := hw.nonneg z y
  have h3 : w z x ^ 2 ≤ (w x y / 2 + δ) ^ 2 := pow_le_pow_left₀ h1 hzx 2
  have h4 : w z y ^ 2 ≤ (w x y / 2 + δ) ^ 2 := pow_le_pow_left₀ h2 hzy 2
  nlinarith

/-- Let F be a spectral point over V, c ≥ 0 a scale, and
a, b, m maps from A to V such that, in the metric c·d_F, every m v is a midpoint of a v and b v up to δ. Then the scaled exponent
of the unit tensor at m is at most the mean of those at a and at b, up to the sum of the numbers √(c d_F(a v, b v) δ + δ²). -/
theorem hexp_le_mean_add (F : Spec K V) {c : ℝ} (hc : 0 ≤ c) (a b m : A → V) {δ : ℝ}
    (ha : ∀ v, c * F.e (m v) (a v) ≤ c * F.e (a v) (b v) / 2 + δ)
    (hb : ∀ v, c * F.e (m v) (b v) ≤ c * F.e (a v) (b v) / 2 + δ) :
    c * hexp F m ≤ (c * hexp F a + c * hexp F b) / 2 + ∑ v, √(c * F.e (a v) (b v) * δ + δ ^ 2) := by
  rcases isEmpty_or_nonempty A with hA | ⟨⟨v₀⟩⟩
  · rw [Subsingleton.elim a m, Subsingleton.elim b m]
    simp
  have : Nonempty V := ⟨m v₀⟩
  obtain ⟨F', he, hm, hd, hg⟩ := exists_mix_hexp F a b m
  have hw : IsPrice K fun x y => c * F'.e x y := (isPrice_spec F').smul hc
  -- the new party v is close to m v
  have hclose : ∀ v, c * F'.e (Sum.inl (m v)) (Sum.inr v) ≤ √(c * F.e (a v) (b v) * δ + δ ^ 2) := by
    intro v
    refine Real.le_sqrt_of_sq_le ?_
    have h := sq_dist_midpoint_le hw (x := Sum.inl (a v)) (y := Sum.inl (b v)) (v := Sum.inr v)
      (z := Sum.inl (m v)) (δ := δ) ?_ ?_ ?_ ?_
    · simpa only [he] using h
    · have h1 := hd (Sum.inl (a v)) (Sum.inr v)
      simp only [Sum.elim_inl, Sum.elim_inr, id, F.e_self] at h1
      have := mul_le_mul_of_nonneg_left h1 hc
      simp only [he]
      linarith
    · have h1 := hd (Sum.inl (b v)) (Sum.inr v)
      simp only [Sum.elim_inl, Sum.elim_inr, id, F.e_self, F.e_comm (b v) (a v)] at h1
      have := mul_le_mul_of_nonneg_left h1 hc
      simp only [he]
      linarith
    · simpa only [he] using ha v
    · simpa only [he] using hb v
  have h1 := hexp_le_move F' (Sum.inl ∘ m) Sum.inr
  rw [hm] at h1
  calc c * hexp F m ≤ c * (hexp F' Sum.inr + ∑ v, F'.e ((Sum.inl ∘ m) v) (Sum.inr v)) :=
        mul_le_mul_of_nonneg_left h1 hc
    _ = c * hexp F' Sum.inr + ∑ v, c * F'.e (Sum.inl (m v)) (Sum.inr v) := by
        rw [mul_add, Finset.mul_sum]
        rfl
    _ ≤ c * ((hexp F a + hexp F b) / 2) + ∑ v, √(c * F.e (a v) (b v) * δ + δ ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hg hc) (Finset.sum_le_sum fun v _ => hclose v)
    _ = _ := by ring

/-- Let w be a function on the pairs of a finite set V (the distances of a
placement of V in a metric space), and A a finite set. For every ε > 0 there is a δ > 0 as follows. Let F be a spectral point over
V and c ≥ 0 a scale such that c·d_F differs from w by less than δ. Let a, b, m map A to V, every m v being a midpoint of a v and
b v for w. Then the scaled exponent of the unit tensor at m is at most the mean of those at a and at b, plus ε. -/
theorem hexp_convex (K : Type) [Field K] {V : Type} [Fintype V] [DecidableEq V] (A : Type) [Fintype A] [DecidableEq A]
    (w : V → V → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (F : Spec K V) (c : ℝ), 0 ≤ c → (∀ u v, |w u v - c * F.e u v| < δ) →
      ∀ a b m : A → V, (∀ v, w (m v) (a v) ≤ w (a v) (b v) / 2) → (∀ v, w (m v) (b v) ≤ w (a v) (b v) / 2) →
        c * hexp F m ≤ (c * hexp F a + c * hexp F b) / 2 + ε := by
  set R : ℝ := ∑ u, ∑ v, |w u v| with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => abs_nonneg _
  have hwR : ∀ u v, w u v ≤ R := fun u v =>
    (le_abs_self _).trans ((Finset.single_le_sum (f := fun v => |w u v|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ v)).trans (Finset.single_le_sum (f := fun u => ∑ v, |w u v|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ u)))
  set n : ℝ := (Fintype.card A : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hden : 0 < (n ^ 2 + 1) * (2 * R + 4) := by positivity
  refine ⟨min 1 (ε ^ 2 / ((n ^ 2 + 1) * (2 * R + 4))), lt_min one_pos (by positivity), ?_⟩
  intro F c hc hF a b m ha hb
  set δ : ℝ := min 1 (ε ^ 2 / ((n ^ 2 + 1) * (2 * R + 4))) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ * ((n ^ 2 + 1) * (2 * R + 4)) ≤ ε ^ 2 := by
    rw [← le_div_iff₀ hden]
    exact min_le_right _ _
  have key := hexp_le_mean_add F hc a b m (δ := 3 / 2 * δ)
    (fun v => by
      have h1 := abs_lt.1 (hF (m v) (a v))
      have h2 := abs_lt.1 (hF (a v) (b v))
      have := ha v
      linarith [h1.1, h2.2])
    (fun v => by
      have h1 := abs_lt.1 (hF (m v) (b v))
      have h2 := abs_lt.1 (hF (a v) (b v))
      have := hb v
      linarith [h1.1, h2.2])
  refine key.trans (add_le_add le_rfl ?_)
  have hterm : ∀ v, √(c * F.e (a v) (b v) * (3 / 2 * δ) + (3 / 2 * δ) ^ 2) ≤ √(δ * (2 * R + 4)) := by
    intro v
    refine Real.sqrt_le_sqrt ?_
    have h2 := abs_lt.1 (hF (a v) (b v))
    have h3 : c * F.e (a v) (b v) ≤ R + 1 := by linarith [h2.1, hwR (a v) (b v)]
    nlinarith
  refine (Finset.sum_le_sum fun v _ => hterm v).trans ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn]
  refine Real.le_sqrt_of_sq_le ?_ |>.trans (Real.sqrt_sq hε.le).le
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  nlinarith [mul_nonneg hδ0.le (by positivity : 0 ≤ 2 * R + 4)]

end Steps

/-- **Paper: Lemma lem:convex.** "Let V ⊆ ℝⁿ be finite, and let a, b, m : I → V be such that every
m(i) is the midpoint of a(i) and b(i). For every ε > 0 there is δ > 0 such that for every spectral point φ on V and
c ≥ 0 with |c·d(x,y) − ‖x−y‖| < δ on V, c·g(m) ≤ ½c·g(a) + ½c·g(b) + ε." -/
theorem lem_convex (K : Type) [Field K] {n : ℕ} (V : Finset (EuclideanSpace ℝ (Fin n))) {I : Type} [Fintype I]
    [DecidableEq I] {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (φ : Spec K V) (c : ℝ), 0 ≤ c → (∀ x y : V, |c * φ.e x y - dist x y| < δ) →
      ∀ a b m : I → V, (∀ i, (m i : EuclideanSpace ℝ (Fin n)) = midpoint ℝ (a i).1 (b i).1) →
        c * hexp φ m ≤ 1 / 2 * (c * hexp φ a) + 1 / 2 * (c * hexp φ b) + ε := by
  classical
  obtain ⟨δ, hδ, h⟩ := hexp_convex K I (fun x y : V => dist x y) hε
  refine ⟨δ, hδ, fun φ c hc hd a b m hm => ?_⟩
  have := h φ c hc (fun x y => by rw [abs_sub_comm]; exact hd x y) a b m (fun i => le_of_eq ?_) (fun i => le_of_eq ?_)
  · linarith
  · rw [Subtype.dist_eq, Subtype.dist_eq, hm, dist_midpoint_left, Real.norm_ofNat]
    ring
  · rw [Subtype.dist_eq, Subtype.dist_eq, hm, dist_midpoint_right, Real.norm_ofNat]
    ring

/-- The maps α_χ of the proof of Proposition prop:cube: at level j the centre ±½e_i (i = d, the sign s) goes to itself
if i is among the first j coordinates, and to ±½χ_i(0, …, 0, χ), with j zeros, if not. (Here u stands for the point
½u.) -/
def cubeAlpha {k : ℕ} (j : ℕ) (χ : Fin k → Bool) (d : Fin k) (s : Bool) : Fin k → SignType :=
  fun x => if d.1 < j then (if x = d then bsign s else 0) else (if x.1 < j then 0 else bsign s * bsign (χ d) * bsign (χ x))

/-- "At level 0 the image is contained in a main diagonal." -/
theorem cubeAlpha_zero {k : ℕ} (χ : Fin k → Bool) (d : Fin k) (s : Bool) :
    cubeAlpha 0 χ d s = (fun x => bsign (χ x)) ∨ cubeAlpha 0 χ d s = fun x => -bsign (χ x) := by
  unfold cubeAlpha
  cases s <;> cases χ d
  · left; funext x; cases χ x <;> simp [bsign]
  · right; funext x; cases χ x <;> simp [bsign]
  · right; funext x; cases χ x <;> simp [bsign]
  · left; funext x; cases χ x <;> simp [bsign]

/-- "At level k it is P." -/
theorem cubeAlpha_top {k : ℕ} (χ : Fin k → Bool) (d : Fin k) (s : Bool) :
    half (cubeAlpha k χ d s) = (if s then (1 / 2 : ℝ) else -(1 / 2)) • EuclideanSpace.single d (1 : ℝ) := by
  ext x
  rw [half_apply]
  by_cases hx : x = d <;> cases s <;> simp [cubeAlpha, bsign, hx, neg_div]

/-- "For j ≥ 1 the map α_χ is the pointwise midpoint of the two maps α_(±1,χ) of level j − 1; compare the three cases
i < j, i = j, i > j." -/
theorem cubeAlpha_midpoint {k j : ℕ} (hj : j < k) (χ : Fin k → Bool) (d : Fin k) (s : Bool) :
    half (cubeAlpha (j + 1) χ d s) = midpoint ℝ (half (cubeAlpha j (Function.update χ ⟨j, hj⟩ true) d s))
      (half (cubeAlpha j (Function.update χ ⟨j, hj⟩ false) d s)) := by
  have key : ∀ x : Fin k, ((cubeAlpha (j + 1) χ d s x : SignType) : ℝ) =
      (((cubeAlpha j (Function.update χ ⟨j, hj⟩ true) d s x : SignType) : ℝ) +
        ((cubeAlpha j (Function.update χ ⟨j, hj⟩ false) d s x : SignType) : ℝ)) / 2 := by
    intro x
    unfold cubeAlpha
    by_cases h1 : d.1 < j
    · simp [h1, h1.trans (Nat.lt_succ_self j)]
    · by_cases h2 : d = ⟨j, hj⟩
      · subst h2
        by_cases h3 : x.1 < j
        · have : x ≠ ⟨j, hj⟩ := fun h => h3.ne (congrArg Fin.val h)
          simp [h3, this]
        · by_cases h4 : x = ⟨j, hj⟩
          · subst h4
            cases s <;> simp [bsign]
          · cases s <;> simp [h3, h4, bsign] <;> cases χ x <;> simp
      · have h2' : ¬ d.1 < j + 1 := fun h => h2 (Fin.ext (show d.1 = j by omega))
        by_cases h3 : x.1 < j
        · simp [h1, h2', h3, h3.trans (Nat.lt_succ_self j)]
        · by_cases h4 : x = ⟨j, hj⟩
          · subst h4
            cases s <;> cases χ d <;> simp [h1, h2, h2', bsign]
          · have h4' : ¬ x.1 < j + 1 := fun h => h4 (Fin.ext (show x.1 = j by omega))
            simp [h1, h2, h2', h3, h4, h4']
  ext x
  rw [midpoint_eq_smul_add]
  simp only [PiLp.smul_apply, PiLp.add_apply, half_apply, smul_eq_mul, key]
  simp
  ring

/-- **Paper: Proposition prop:cube.** "In the flat case let V ⊆ ℝᵏ be finite, P ⊆ V ∩ {±½e₁, …, ±½e_k} nonempty and
ε > 0. There are a spectral point φ on V and c ≥ 0 with |c·d(x,y) − ‖x−y‖| < ε on V and c·g(P) ≤ √k + ε." -/
theorem prop_cube {K : Type} [Field K] (hK : Flat K) {k : ℕ} (V : Finset (EuclideanSpace ℝ (Fin k)))
    (P : Finset (EuclideanSpace ℝ (Fin k))) (hPV : P ⊆ V) (hP : P.Nonempty)
    (hc : ∀ x ∈ P, ∃ (j : Fin k) (b : Bool), x = (if b then (1 / 2 : ℝ) else -(1 / 2)) • EuclideanSpace.single j 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (φ : Spec K V) (c : ℝ), 0 ≤ c ∧ (∀ x y : V, |c * φ.e x y - dist x y| < ε) ∧
      c * hexp φ (fun x : P => (⟨x.1, hPV x.2⟩ : V)) ≤ √k + ε := by
  classical
  have : Nonempty P := hP.coe_sort
  have hk : 0 < k := by
    obtain ⟨x₀, hx₀⟩ := hP
    obtain ⟨j₀, -, -⟩ := hc x₀ hx₀
    exact j₀.pos
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  choose j b hjb using fun x : P => hc x.1 x.2
  -- add the points ½u
  let V' : Finset (EuclideanSpace ℝ (Fin k)) := V ∪ univ.image half
  let incl : V → V' := fun x => ⟨x.1, mem_union_left _ x.2⟩
  let pt : (Fin k → SignType) → V' := fun u => ⟨half u, mem_union_right _ (mem_image_of_mem _ (mem_univ u))⟩
  have : Nonempty V' := ⟨pt fun _ => 0⟩
  obtain ⟨δ, hδ, hconv⟩ := lem_convex K V' (I := P) (show 0 < ε / (2 * k) by positivity)
  obtain ⟨φ, c, hc0, hφ⟩ := (hK k V' fun x => x.1).exists_spec id (show 0 < min δ (ε / 2) by positivity)
  have hφ' : ∀ x y : V', |c * φ.e x y - dist x y| < min δ (ε / 2) := fun x y => by
    rw [abs_sub_comm, Subtype.dist_eq]
    exact hφ x y
  let α : ℕ → (Fin k → Bool) → P → V' := fun i χ x => pt (cubeAlpha i χ (j x) (b x))
  have hlevel : ∀ i ≤ k, ∀ χ, c * hexp φ (α i χ) ≤ √k + ε / 2 + i * (ε / (2 * k)) := by
    intro i
    induction i with
    | zero =>
      intro _ χ
      have h1 := hexp_le_of_two φ (α 0 χ) (pt fun x => bsign (χ x)) (pt fun x => -bsign (χ x)) fun x => by
        rcases cubeAlpha_zero χ (j x) (b x) with h | h
        · exact Or.inl (congrArg pt h)
        · exact Or.inr (congrArg pt h)
      have h2 := (abs_lt.1 (hφ' (pt fun x => bsign (χ x)) (pt fun x => -bsign (χ x)))).2
      rw [Subtype.dist_eq, dist_half_neg] at h2
      have h3 := mul_le_mul_of_nonneg_left h1 hc0
      simp only [Nat.cast_zero, zero_mul, add_zero]
      linarith [min_le_right δ (ε / 2)]
    | succ i ih =>
      intro hi χ
      have h1 := hconv φ c hc0 (fun x y => (hφ' x y).trans_le (min_le_left _ _))
        (α i (Function.update χ ⟨i, hi⟩ true)) (α i (Function.update χ ⟨i, hi⟩ false)) (α (i + 1) χ)
        fun x => cubeAlpha_midpoint hi χ (j x) (b x)
      have h2 := ih (Nat.le_of_succ_le hi) (Function.update χ ⟨i, hi⟩ true)
      have h3 := ih (Nat.le_of_succ_le hi) (Function.update χ ⟨i, hi⟩ false)
      push_cast
      linarith
  refine ⟨φ.pull incl, c, hc0, fun x y => ?_, ?_⟩
  · rw [φ.pull_e, Subtype.dist_eq]
    exact (hφ' (incl x) (incl y)).trans_le ((min_le_right _ _).trans (by linarith))
  · have e : incl ∘ (fun x : P => (⟨x.1, hPV x.2⟩ : V)) = α k fun _ => true :=
      funext fun x => Subtype.ext ((hjb x).trans (cubeAlpha_top _ _ _).symm)
    rw [hexp_pull, e]
    refine (hlevel k le_rfl _).trans (le_of_eq ?_)
    field_simp
    ring

end Paper
