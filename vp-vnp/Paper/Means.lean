/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Crossing
import Nc.Cat.Length

/-!
# The paper, section "Prices are nonpositively curved": means

The subsection "Means". For n = 1, 2, … a function W n is a price on two sheets of ℤ² (the type Bool × ℤ × ℤ) with
W n (P, P+g) ≤ Λ|g| on each sheet. The mean E is Cat.mean, the limit along a fixed free ultrafilter of the means over the
windows; it is linear, positive and invariant under translations (Nc/Cat/Mean.lean).
-/

namespace Paper

open Finset Filter Topology Nc.Price

variable {K : Type} [Field K]

/-- The paper's ν(g) = (E W(P,P+g)²)^(1/2). -/
noncomputable def meanLength (W : ℕ → (Bool × ℤ × ℤ) → (Bool × ℤ × ℤ) → ℝ) (g : ℤ × ℤ) : ℝ :=
  Cat.len (fun n b P P' => W n (b, P) (b, P')) g

/-- ν(g) is the square root of the limit along a fixed ultrafilter of the means of W(P, P+g)² over both sheets of the
n-th window. -/
theorem meanLength_eq (W : ℕ → (Bool × ℤ × ℤ) → (Bool × ℤ × ℤ) → ℝ) (g : ℤ × ℤ) :
    meanLength W g = √(limUnder (hyperfilter ℕ : Filter ℕ) fun n => (∑ b : Bool, ∑ i ∈ range (n ^ 2),
      ∑ j ∈ range n, W n (b, ((i : ℤ), (j : ℤ))) (b, ((i : ℤ), (j : ℤ)) + g) ^ 2) / (2 * n ^ 3)) := by
  simp only [meanLength, Cat.len, Cat.nm, Cat.mean, Cat.avg, Cat.df, Pi.mul_apply, add_zero, pow_two]

/-- The paper's N(g) = inf ν(Sg)/S over integers S ≥ 1. -/
noncomputable def meanNorm (W : ℕ → (Bool × ℤ × ℤ) → (Bool × ℤ × ℤ) → ℝ) (g : ℤ × ℤ) : ℝ :=
  sInf {r : ℝ | ∃ S : ℕ, 0 < S ∧ r = meanLength W (S • g) / S}

section Norm

variable (W : ℕ → (Bool × ℤ × ℤ) → (Bool × ℤ × ℤ) → ℝ) (g : ℤ × ℤ)

theorem meanLength_nonneg : 0 ≤ meanLength W g := Cat.nm_nonneg _

theorem meanNorm_isGLB : IsGLB {r : ℝ | ∃ S : ℕ, 0 < S ∧ r = meanLength W (S • g) / S} (meanNorm W g) :=
  isGLB_csInf ⟨_, 1, one_pos, rfl⟩
    ⟨0, by rintro _ ⟨S, -, rfl⟩; exact div_nonneg (meanLength_nonneg _ _) (Nat.cast_nonneg _)⟩

/-- "For upper bounds [on N it is enough to prove them] for one S." -/
theorem meanNorm_le {S : ℕ} (hS : 0 < S) : meanNorm W g ≤ meanLength W (S • g) / S :=
  (meanNorm_isGLB W g).1 ⟨S, hS, rfl⟩

theorem meanNorm_le_meanLength : meanNorm W g ≤ meanLength W g := by
  simpa using meanNorm_le W g one_pos

/-- "For lower bounds [on N] it is enough to prove them for ν(Sg)/S for every S." -/
theorem le_meanNorm {c : ℝ} (h : ∀ S : ℕ, 0 < S → c * S ≤ meanLength W (S • g)) : c ≤ meanNorm W g := by
  refine (meanNorm_isGLB W g).2 ?_
  rintro _ ⟨S, hS, rfl⟩
  rw [le_div_iff₀ (by exact_mod_cast hS)]
  exact h S hS

theorem meanNorm_nonneg : 0 ≤ meanNorm W g :=
  le_meanNorm W g fun S _ => by rw [zero_mul]; exact meanLength_nonneg _ _

end Norm

variable {W : ℕ → (Bool × ℤ × ℤ) → (Bool × ℤ × ℤ) → ℝ} {Λ : ℝ}

/-- What is used of the prices W n: they are pseudometrics, Lipschitz on each sheet, and satisfy (Q), which is Proposition
prop:crossing. -/
theorem lem_means_lip (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) :
    Cat.Lip (fun n b P P' => W n (b, P) (b, P')) Λ where
  nonneg n _ _ _ := (hW n).nonneg _ _
  self n _ _ := (hW n).self _
  symm n _ _ _ := (hW n).symm _ _
  tri n _ _ _ _ := (hW n).triangle _ _ _
  lip := hΛ
  q n b x v y u o o' w w' _ _ τ hp hq hτ :=
    eq_Q (hW n) (b, x) (b, v) (b, y) (b, u) (b, o) (b, o') (b, w) (b, w') hp hq τ hτ

/-- The text before Lemma lem:means: "By translation invariance and Minkowski's inequality ν is even …" -/
theorem lem_means_even (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) (g : ℤ × ℤ) :
    meanLength W (-g) = meanLength W g :=
  (lem_means_lip hW hΛ).len_neg g

/-- The text before Lemma lem:means: "… and subadditive". -/
theorem lem_means_subadditive (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) (g h : ℤ × ℤ) :
    meanLength W (g + h) ≤ meanLength W g + meanLength W h :=
  (lem_means_lip hW hΛ).len_add g h

/-- The first step of the proof of Lemma lem:means: "By the Cauchy–Schwarz inequality ν satisfies (Q) with the norms of
differences for the distances, p and q the norms of x − v and y − u." -/
theorem lem_means_Q (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|))
    (x v y u o o' w w' : ℤ × ℤ) {τ : ℝ} (hτ : 0 < τ) :
    2 * (meanLength W (x - v) ^ 2 + meanLength W (y - u) ^ 2) ≤
      meanLength W (x - v) *
        (meanLength W (x - o) + meanLength W (v - o') + meanLength W (x - w) + meanLength W (v - w'))
      + meanLength W (y - u) *
        (meanLength W (y - o) + meanLength W (u - o') + meanLength W (u - w) + meanLength W (y - w'))
      + τ * (meanLength W (x - v) ^ 2 + meanLength W (y - u) ^ 2)
      + (meanLength W (o - o') ^ 2 + meanLength W (w - w') ^ 2) / (2 * τ) :=
  (lem_means_lip hW hΛ).len_q x v y u o o' w w' τ hτ

/-- ν is an even subadditive function with (Q). -/
theorem meanLength_len (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) :
    Cat.Len (meanLength W) where
  nonneg := meanLength_nonneg W
  zero := (lem_means_lip hW hΛ).len_zero
  neg := lem_means_even hW hΛ
  add := lem_means_subadditive hW hΛ
  q x v y u o o' w w' _ hτ := lem_means_Q hW hΛ x v y u o o' w w' hτ

/-- N is an even subadditive function with (Q), and homogeneous. -/
theorem meanNorm_len (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) :
    Cat.Len (meanNorm W) ∧ Cat.Homog (meanNorm W) := by
  obtain ⟨N, hN, hom, hle, hgl⟩ := (meanLength_len hW hΛ).exists_homog
  have e : N = meanNorm W := by
    funext g
    refine le_antisymm (le_meanNorm W g fun S _ => ?_) (hgl g _ fun S hS => ?_)
    · rw [mul_comm, ← hom S g]
      exact hle _
    · have := meanNorm_le W g hS
      rwa [le_div_iff₀ (by exact_mod_cast hS)] at this
  exact e ▸ ⟨hN, hom⟩

/-- The definition of N: "N(g) = lim ν(Sg)/S = inf ν(Sg)/S." The limit exists and is the infimum, as ν is subadditive. -/
theorem lem_means_limit (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) (g : ℤ × ℤ) :
    Tendsto (fun S : ℕ => meanLength W (S • g) / S) atTop (𝓝 (meanNorm W g)) := by
  have hν := meanLength_len hW hΛ
  have hb : BddBelow (Set.range fun S : ℕ => meanLength W (S • g) / S) :=
    ⟨0, by rintro _ ⟨S, rfl⟩; exact div_nonneg (hν.nonneg _) (Nat.cast_nonneg _)⟩
  have ht := (hν.subadditive g).tendsto_lim hb
  have e : (hν.subadditive g).lim = meanNorm W g := by
    refine le_antisymm (le_meanNorm W g fun S hS => ?_) ?_
    · have := (hν.subadditive g).lim_le_div hb (n := S) hS.ne'
      rwa [le_div_iff₀ (by exact_mod_cast hS)] at this
    · exact ge_of_tendsto ht (eventually_atTop.2 ⟨1, fun S hS => meanNorm_le W g hS⟩)
  rwa [e] at ht

/-- The text before Lemma lem:means: "so N is also homogeneous". -/
theorem lem_means_homogeneous (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) (S : ℕ) (g : ℤ × ℤ) :
    meanNorm W (S • g) = S * meanNorm W g :=
  (meanNorm_len hW hΛ).2 S g

/-- The text before Lemma lem:means: N is even and subadditive, as ν is. With lem_means_homogeneous and meanNorm_nonneg this
makes N a seminorm on ℤ². -/
theorem lem_means_seminorm (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) :
    (∀ g, meanNorm W (-g) = meanNorm W g) ∧ ∀ g h, meanNorm W (g + h) ≤ meanNorm W g + meanNorm W h :=
  ⟨(meanNorm_len hW hΛ).1.neg, (meanNorm_len hW hΛ).1.add⟩

/-- The second step of the proof of Lemma lem:means: "Apply this to eight vectors multiplied by S, divide by S² and let
S → ∞: so does N, with the same τ." -/
theorem lem_means_Q_norm (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|))
    (x v y u o o' w w' : ℤ × ℤ) {τ : ℝ} (hτ : 0 < τ) :
    2 * (meanNorm W (x - v) ^ 2 + meanNorm W (y - u) ^ 2) ≤
      meanNorm W (x - v) * (meanNorm W (x - o) + meanNorm W (v - o') + meanNorm W (x - w) + meanNorm W (v - w'))
      + meanNorm W (y - u) * (meanNorm W (y - o) + meanNorm W (u - o') + meanNorm W (u - w) + meanNorm W (y - w'))
      + τ * (meanNorm W (x - v) ^ 2 + meanNorm W (y - u) ^ 2)
      + (meanNorm W (o - o') ^ 2 + meanNorm W (w - w') ^ 2) / (2 * τ) :=
  (meanNorm_len hW hΛ).1.q x v y u o o' w w' τ hτ

/-! ### The proof of Lemma lem:means

The steps after "so does N" use of N only that it is even, subadditive and homogeneous and satisfies (Q). This is
Cat.Len N and Cat.Homog N, and it holds for N = meanNorm W by lem_means_seminorm, lem_means_homogeneous and
lem_means_Q_norm. As in the paper c = a + b, e = a − b, f = N(c), f′ = N(e). -/

section Parallelogram

/-- "∂p = 2N(p) − N(p−a) − N(p−b)". The paper's ∂′q = 2N(q) − N(q−a) − N(q+b) is the same with −b for b. -/
def meansDiff (N : ℤ × ℤ → ℝ) (a b p : ℤ × ℤ) : ℝ := 2 * N p - N (p - a) - N (p - b)

/-- "A_i = Mc + ie". With −b for b this is Me + ic. -/
def meansPt (a b : ℤ × ℤ) (M i : ℕ) : ℤ × ℤ := M • (a + b) + i • (a - b)

/-- "δ_i = N(A_i − a) − N(A_i − 2a)". -/
def meansDelta (N : ℤ × ℤ → ℝ) (a b : ℤ × ℤ) (M i : ℕ) : ℝ :=
  N (meansPt a b M i - a) - N (meansPt a b M i - a - a)

variable {N : ℤ × ℤ → ℝ}

/-- "Take (x,v,y,u) = (p,−p,q,−q) and (o,o′,w,w′) = (a,−a,b,−b) and divide by 4:
N(p)∂p + N(q)∂′q ≤ τ(N(p)² + N(q)²) + (N(a)² + N(b)²)/(2τ)." -/
theorem lem_means_display (hN : Cat.Len N) (hh : Cat.Homog N) (a b p q : ℤ × ℤ) {τ : ℝ} (hτ : 0 < τ) :
    N p * meansDiff N a b p + N q * meansDiff N a (-b) q ≤
      τ * (N p ^ 2 + N q ^ 2) + (N a ^ 2 + N b ^ 2) / (2 * τ) := by
  unfold meansDiff
  have h := hN.q p (-p) q (-q) a (-a) b (-b) τ hτ
  have e1 : ∀ Z : ℤ × ℤ, N (Z - -Z) = 2 * N Z := by
    intro Z
    rw [show Z - -Z = 2 • Z by module, hh]
    norm_num
  have e2 : N (-p - -a) = N (p - a) := by rw [← hN.neg]; congr 1; module
  have e3 : N (-p - -b) = N (p - b) := by rw [← hN.neg]; congr 1; module
  have e4 : N (-q - -a) = N (q - a) := by rw [← hN.neg]; congr 1; module
  have e5 : N (-q - b) = N (q - -b) := by rw [← hN.neg]; congr 1; module
  rw [e1 p, e1 q, e1 a, e1 b, e2, e3, e4, e5] at h
  have e6 : ((2 * N a) ^ 2 + (2 * N b) ^ 2) / (2 * τ) = 4 * ((N a ^ 2 + N b ^ 2) / (2 * τ)) := by
    ring
  rw [e6] at h
  linarith

/-- "∂A_i + ∂(A_i − a) = 2(N(A_i) − N(A_i − c)) + δ_i − δ_{i+1}." This holds for every function N. -/
theorem lem_means_identity (a b : ℤ × ℤ) (M i : ℕ) :
    meansDiff N a b (meansPt a b M i) + meansDiff N a b (meansPt a b M i - a) =
      2 * (N (meansPt a b M i) - N (meansPt a b M i - (a + b)))
        + (meansDelta N a b M i - meansDelta N a b M (i + 1)) := by
  simp only [meansDiff, meansDelta, meansPt]
  have e1 : M • (a + b) + (i + 1) • (a - b) - a = M • (a + b) + i • (a - b) - b := by module
  have e2 : M • (a + b) + i • (a - b) - b - a = M • (a + b) + i • (a - b) - (a + b) := by module
  have e3 : M • (a + b) + i • (a - b) - a - b = M • (a + b) + i • (a - b) - (a + b) := by module
  rw [e1, e2, e3]
  ring

/-- "As t ↦ N(tc + ie) is convex, the first difference on the right is at least f − 2N(ie)/M." Here s stands for ie, and
convexity is used at the integers t ≥ 0: the differences N((t+1)c + s) − N(tc + s) do not decrease. -/
theorem lem_means_convex (hN : Cat.Len N) (hh : Cat.Homog N) (s c : ℤ × ℤ) (M : ℕ) (hM : 0 < M) :
    N c - 2 * N s / M ≤ N (M • c + s) - N (M • c + s - c) := by
  have hmono : Monotone fun t : ℕ => N ((t + 1) • c + s) - N (t • c + s) := by
    refine monotone_nat_of_le_succ fun t => ?_
    have h1 := hN.add ((t + 1 + 1) • c + s) (t • c + s)
    have h2 : (t + 1 + 1) • c + s + (t • c + s) = 2 • ((t + 1) • c + s) := by module
    rw [h2, hh] at h1
    push_cast at h1
    linarith
  obtain ⟨M, rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  have h1 := Finset.sum_range_sub (fun t : ℕ => N (t • c + s)) (M + 1)
  have h2 : ∑ t ∈ range (M + 1), (N ((t + 1) • c + s) - N (t • c + s)) ≤
      ∑ t ∈ range (M + 1), (N ((M + 1) • c + s) - N (M • c + s)) :=
    Finset.sum_le_sum fun t ht => hmono (by simpa [Nat.lt_succ_iff] using ht)
  rw [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul (α := ℝ), zero_smul, zero_add] at h2
  have h3 := hN.sub_le ((M + 1) • c + s) s
  rw [add_sub_cancel_right, hh] at h3
  have h4 : (M + 1) • c + s - c = M • c + s := by module
  rw [h4]
  have hM' : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  have h5 : N c - 2 * N s / ((M + 1 : ℕ) : ℝ) =
      (((M + 1 : ℕ) : ℝ) * N c - 2 * N s) / ((M + 1 : ℕ) : ℝ) := by field_simp
  rw [h5, div_le_iff₀ hM']
  linarith

/-- "The δ_i are bounded and telescope": the sum of ∂A_i + ∂(A_i − a) over 0 ≤ i < R is at least
2R(f − 2R·f′/M) − 2N(a). -/
theorem lem_means_telescope (hN : Cat.Len N) (hh : Cat.Homog N) (a b : ℤ × ℤ) {M : ℕ} (hM : 0 < M) (R : ℕ) :
    2 * R * (N (a + b) - 2 * R * N (a - b) / M) - 2 * N a ≤
      ∑ i ∈ range R, (meansDiff N a b (meansPt a b M i) + meansDiff N a b (meansPt a b M i - a)) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have h2 : ∀ i ∈ range R, 2 * (N (a + b) - 2 * R * N (a - b) / M)
      + (meansDelta N a b M i - meansDelta N a b M (i + 1)) ≤
        meansDiff N a b (meansPt a b M i) + meansDiff N a b (meansPt a b M i - a) := by
    intro i hi
    rw [lem_means_identity]
    have h3 := lem_means_convex hN hh (i • (a - b)) (a + b) M hM
    rw [hh] at h3
    have h4 : 2 * ((i : ℝ) * N (a - b)) / M ≤ 2 * R * N (a - b) / M := by
      apply div_le_div_of_nonneg_right _ hM'.le
      have : (i : ℝ) ≤ R := by exact_mod_cast (Finset.mem_range.1 hi).le
      nlinarith [hN.nonneg (a - b)]
    simp only [meansPt]
    linarith
  have h5 := Finset.sum_le_sum h2
  rw [Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_const, Finset.card_range,
    nsmul_eq_mul (α := ℝ)] at h5
  have h6 : meansDelta N a b M R ≤ N a := by
    unfold meansDelta
    linarith [hN.le_add_sub (meansPt a b M R - a) a]
  have h7 : -N a ≤ meansDelta N a b M 0 := by
    unfold meansDelta
    linarith [hN.sub_le (meansPt a b M 0 - a) a]
  linarith

/-- N(p) = Mf + O(R) at the points p = Mc + ie and p = Mc + ie − a with i < R: the error is at most 2Rκ if N(a), N(e) ≤ κ. -/
theorem lem_means_near (hN : Cat.Len N) (hh : Cat.Homog N) {a c e : ℤ × ℤ} {κ : ℝ} (ha : N a ≤ κ) (he : N e ≤ κ)
    (M : ℕ) {R i : ℕ} (hi : i < R) :
    |N (M • c + i • e) - M * N c| ≤ 2 * R * κ ∧ |N (M • c + i • e - a) - M * N c| ≤ 2 * R * κ := by
  have hi' : (i : ℝ) + 1 ≤ R := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  rw [← hh]
  constructor
  · have h1 := hN.abs_sub_le (M • c + i • e) (M • c)
    rw [add_sub_cancel_left, hh i e] at h1
    nlinarith [hN.nonneg e]
  · have h1 := hN.abs_sub_le (M • c + i • e - a) (M • c)
    have h2 : M • c + i • e - a - M • c = i • e - a := by module
    rw [h2] at h1
    have h3 := hN.sub_le (i • e) a
    rw [hh i e] at h3
    nlinarith [hN.nonneg e]

/-- "∂ is bounded by N(a) + N(b), so N(p)∂p = Mf∂p + O(R)", and the same for ∂′ at q, with f′. "With τ = 1/(2M)" the
display becomes Mf∂p + Mf′∂′q ≤ M(½(f² + f′²) + N(a)² + N(b)²) + O(R). Here f = N(c), f′ = N(e), the points p, q have
N(p) = Mf + O(R), N(q) = Mf′ + O(R) with errors at most 2Rκ, and the last O(R) is 12Rκ². -/
theorem lem_means_estimate (hN : Cat.Len N) (hh : Cat.Homog N) (a b p q c e : ℤ × ℤ) {M R : ℕ} {κ : ℝ} (hM : 0 < M)
    (hR : R ≤ M) (hκ : N a + N b ≤ κ) (hc : N c ≤ κ) (he : N e ≤ κ)
    (hp : |N p - M * N c| ≤ 2 * R * κ) (hq : |N q - M * N e| ≤ 2 * R * κ) :
    M * N c * meansDiff N a b p + M * N e * meansDiff N a (-b) q ≤
      M * ((N c ^ 2 + N e ^ 2) / 2 + (N a ^ 2 + N b ^ 2)) + 12 * R * κ ^ 2 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hR' : (R : ℝ) ≤ M := by exact_mod_cast hR
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hκ0 : 0 ≤ κ := (hN.nonneg c).trans hc
  have h1 := lem_means_display hN hh a b p q (τ := 1 / (2 * M)) (by positivity)
  have e1 : (N a ^ 2 + N b ^ 2) / (2 * (1 / (2 * (M : ℝ)))) = M * (N a ^ 2 + N b ^ 2) := by
    field_simp
  rw [e1] at h1
  have hxp : |meansDiff N a b p| ≤ κ := by
    unfold meansDiff
    have h2 := hN.abs_sub_le p (p - a)
    have h3 := hN.abs_sub_le p (p - b)
    rw [sub_sub_cancel] at h2 h3
    rw [abs_le] at h2 h3 ⊢
    constructor <;> linarith
  have hxq : |meansDiff N a (-b) q| ≤ κ := by
    unfold meansDiff
    have h2 := hN.abs_sub_le q (q - a)
    have h3 := hN.abs_sub_le q (q - -b)
    rw [sub_sub_cancel] at h2 h3
    rw [hN.neg] at h3
    rw [abs_le] at h2 h3 ⊢
    constructor <;> linarith
  have low : ∀ (A B x : ℝ), |A - B| ≤ 2 * R * κ → |x| ≤ κ → B * x - 2 * R * κ ^ 2 ≤ A * x := by
    intro A B x hA hx
    have h2 : |(A - B) * x| ≤ 2 * R * κ * κ := by
      rw [abs_mul]
      exact mul_le_mul hA hx (abs_nonneg _) (by positivity)
    have h3 := (abs_le.1 h2).1
    nlinarith
  have sq : ∀ (Z c : ℤ × ℤ), N c ≤ κ → |N Z - M * N c| ≤ 2 * R * κ →
      1 / (2 * M) * N Z ^ 2 ≤ M * N c ^ 2 / 2 + 4 * R * κ ^ 2 := by
    intro Z c hc hZ
    have h2 : N Z ≤ M * N c + 2 * R * κ := by linarith [(abs_le.1 hZ).2]
    have h3 : N Z ^ 2 ≤ (M * N c + 2 * R * κ) ^ 2 := pow_le_pow_left₀ (hN.nonneg Z) h2 2
    have h4 : (M * N c + 2 * R * κ) ^ 2 ≤ M ^ 2 * N c ^ 2 + 8 * M * R * κ ^ 2 := by
      have h5 : (M : ℝ) * R * (N c * κ) ≤ M * R * κ ^ 2 := by
        rw [sq κ]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hκ0) (by positivity)
      have h6 : (R : ℝ) * R * κ ^ 2 ≤ M * R * κ ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hR' hR0) (sq_nonneg _)
      nlinarith
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  have l1 := low _ _ _ hp hxp
  have l2 := low _ _ _ hq hxq
  have s1 := sq _ _ hc hp
  have s2 := sq _ _ he hq
  linarith

/-- The arithmetic of "averaging over i and dividing by 2M", with M = m², f, f′, n = N(a) at most κ, Q = N(a)² + N(b)². -/
private theorem means_arith {m f f' n Q κ : ℝ} (hm : 0 < m) (hf0 : 0 ≤ f) (hf : f ≤ κ) (hf0' : 0 ≤ f') (hf' : f' ≤ κ)
    (hn0 : 0 ≤ n) (hn : n ≤ κ)
    (h : m ^ 2 * f * (2 * m * (f - 2 * m * f' / m ^ 2) - 2 * n)
        + m ^ 2 * f' * (2 * m * (f' - 2 * m * f / m ^ 2) - 2 * n) ≤
      m * (m ^ 2 * ((f ^ 2 + f' ^ 2) / 2 + Q) + 12 * m * κ ^ 2
        + (m ^ 2 * ((f ^ 2 + f' ^ 2) / 2 + Q) + 12 * m * κ ^ 2))) :
    f ^ 2 + f' ^ 2 ≤ 2 * Q + 36 * κ ^ 2 * (1 / m) := by
  have hκ0 : 0 ≤ κ := hf0.trans hf
  have q1 : f * f' ≤ κ ^ 2 := by rw [sq]; exact mul_le_mul hf hf' hf0' hκ0
  have q2 : f * n ≤ κ ^ 2 := by rw [sq]; exact mul_le_mul hf hn hn0 hκ0
  have q3 : f' * n ≤ κ ^ 2 := by rw [sq]; exact mul_le_mul hf' hn hn0 hκ0
  have e3 : m ^ 2 * f * (2 * m * (f - 2 * m * f' / m ^ 2) - 2 * n) =
      2 * m ^ 3 * f ^ 2 - 4 * (f * f') * m ^ 2 - 2 * (f * n) * m ^ 2 := by
    field_simp
    ring
  have e4 : m ^ 2 * f' * (2 * m * (f' - 2 * m * f / m ^ 2) - 2 * n) =
      2 * m ^ 3 * f' ^ 2 - 4 * (f * f') * m ^ 2 - 2 * (f' * n) * m ^ 2 := by
    field_simp
    ring
  rw [e3, e4] at h
  have h5 : m ^ 3 * (f ^ 2 + f' ^ 2) ≤ m ^ 3 * (2 * Q + 36 * κ ^ 2 * (1 / m)) := by
    have e5 : m ^ 3 * (2 * Q + 36 * κ ^ 2 * (1 / m)) = 2 * m ^ 3 * Q + 36 * κ ^ 2 * m ^ 2 := by
      field_simp
    rw [e5]
    have w1 := mul_le_mul_of_nonneg_right q1 (sq_nonneg m)
    have w2 := mul_le_mul_of_nonneg_right q2 (sq_nonneg m)
    have w3 := mul_le_mul_of_nonneg_right q3 (sq_nonneg m)
    linarith
  exact le_of_mul_le_mul_left h5 (by positivity)

/-- "With τ = 1/(2M), adding the two inequalities, averaging over i and dividing by 2M gives
f² + f′² ≤ ½(f² + f′²) + N(a)² + N(b)² + O(1/R)", where M = R². Here the inequality is doubled and ½(f² + f′²) is
subtracted, and the O(1/R) becomes 36(N(a) + N(b))²/R. -/
theorem lem_means_average (hN : Cat.Len N) (hh : Cat.Homog N) (a b : ℤ × ℤ) {R : ℕ} (hR : 0 < R) :
    N (a + b) ^ 2 + N (a - b) ^ 2 ≤ 2 * (N a ^ 2 + N b ^ 2) + 36 * (N a + N b) ^ 2 * (1 / (R : ℝ)) := by
  set κ := N a + N b with hκ
  have hc : N (a + b) ≤ κ := hN.add a b
  have he : N (a - b) ≤ κ := hN.sub_le a b
  have ha : N a ≤ κ := by linarith [hN.nonneg b]
  have hM : 0 < R ^ 2 := by positivity
  have hRM : R ≤ R ^ 2 := by nlinarith
  have s1 := lem_means_telescope hN hh a b hM R
  have s2 := lem_means_telescope hN hh a (-b) hM R
  simp only [meansPt] at s1 s2
  rw [sub_neg_eq_add, ← sub_eq_add_neg] at s2
  have p : ∀ i ∈ range R, _ := fun i hi => add_le_add
    (lem_means_estimate hN hh a b _ _ (a + b) (a - b) hM hRM le_rfl hc he
      (lem_means_near hN hh ha he _ (Finset.mem_range.1 hi)).1 (lem_means_near hN hh ha hc _ (Finset.mem_range.1 hi)).1)
    (lem_means_estimate hN hh a b _ _ (a + b) (a - b) hM hRM le_rfl hc he
      (lem_means_near hN hh ha he _ (Finset.mem_range.1 hi)).2 (lem_means_near hN hh ha hc _ (Finset.mem_range.1 hi)).2)
  have hp := Finset.sum_le_sum p
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul (α := ℝ)] at hp
  have hp2 : ((R ^ 2 : ℕ) : ℝ) * N (a + b) *
        (2 * R * (N (a + b) - 2 * R * N (a - b) / (R ^ 2 : ℕ)) - 2 * N a)
      + ((R ^ 2 : ℕ) : ℝ) * N (a - b) *
        (2 * R * (N (a - b) - 2 * R * N (a + b) / (R ^ 2 : ℕ)) - 2 * N a) ≤
      R * (((R ^ 2 : ℕ) : ℝ) * ((N (a + b) ^ 2 + N (a - b) ^ 2) / 2 + (N a ^ 2 + N b ^ 2))
        + 12 * R * κ ^ 2 + (((R ^ 2 : ℕ) : ℝ) * ((N (a + b) ^ 2 + N (a - b) ^ 2) / 2
        + (N a ^ 2 + N b ^ 2)) + 12 * R * κ ^ 2)) := by
    refine le_trans ?_ hp
    refine le_trans (add_le_add
      (mul_le_mul_of_nonneg_left s1 (mul_nonneg (Nat.cast_nonneg _) (hN.nonneg _)))
      (mul_le_mul_of_nonneg_left s2 (mul_nonneg (Nat.cast_nonneg _) (hN.nonneg _)))) ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => le_of_eq (by ring)
  push_cast at hp2
  exact means_arith (by exact_mod_cast hR) (hN.nonneg _) hc (hN.nonneg _) he (hN.nonneg _) ha hp2

/-- "Thus N(a+b)² + N(a−b)² ≤ 2N(a)² + 2N(b)²." -/
theorem lem_means_parallelogram_le (hN : Cat.Len N) (hh : Cat.Homog N) (a b : ℤ × ℤ) :
    N (a + b) ^ 2 + N (a - b) ^ 2 ≤ 2 * (N a ^ 2 + N b ^ 2) := by
  have h1 : Tendsto (fun R : ℕ => 2 * (N a ^ 2 + N b ^ 2) + 36 * (N a + N b) ^ 2 * (1 / (R : ℝ))) atTop
      (𝓝 (2 * (N a ^ 2 + N b ^ 2) + 36 * (N a + N b) ^ 2 * 0)) :=
    (tendsto_one_div_atTop_nhds_zero_nat.const_mul _).const_add _
  rw [mul_zero, add_zero] at h1
  refine ge_of_tendsto h1 ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact lem_means_average hN hh a b hR

end Parallelogram

/-- **Paper: Lemma lem:means.** For prices W_n on two sheets of ℤ² with W_n(P,P+g) ≤ Λ|g| for points of one sheet, and
N(g) = lim ν(Sg)/S = inf ν(Sg)/S: "N(a+b)² + N(a−b)² = 2N(a)² + 2N(b)² for all a, b ∈ ℤ²." -/
theorem lem_means (W : ℕ → (Bool × ℤ × ℤ) → (Bool × ℤ × ℤ) → ℝ) (hW : ∀ n, IsPrice K (W n)) (Λ : ℝ)
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) :
    ∃ N : ℤ × ℤ → ℝ,
      (∀ g, Tendsto (fun S : ℕ => meanLength W (S • g) / S) atTop (𝓝 (N g)) ∧
        IsGLB {r : ℝ | ∃ S : ℕ, 0 < S ∧ r = meanLength W (S • g) / S} (N g)) ∧
      ∀ a b, N (a + b) ^ 2 + N (a - b) ^ 2 = 2 * N a ^ 2 + 2 * N b ^ 2 := by
  refine ⟨meanNorm W, fun g => ⟨lem_means_limit hW hΛ g, meanNorm_isGLB W g⟩, fun a b => ?_⟩
  have hom : Cat.Homog (meanNorm W) := lem_means_homogeneous hW hΛ
  have hN : Cat.Len (meanNorm W) :=
    { nonneg := meanNorm_nonneg W
      zero := by simpa using hom 0 0
      neg := (lem_means_seminorm hW hΛ).1
      add := (lem_means_seminorm hW hΛ).2
      q := fun x v y u o o' w w' _ hτ => lem_means_Q_norm hW hΛ x v y u o o' w w' hτ }
  refine le_antisymm (by linarith [lem_means_parallelogram_le hN hom a b]) ?_
  -- "applied to a+b, a−b it gives equality"
  have h := lem_means_parallelogram_le hN hom (a + b) (a - b)
  rw [show a + b + (a - b) = (2 : ℕ) • a by rw [two_nsmul]; abel,
    show a + b - (a - b) = (2 : ℕ) • b by rw [two_nsmul]; abel, hom, hom] at h
  push_cast at h
  linarith

/-- Lemma lem:means for the function N = meanNorm W. -/
theorem lem_means_norm (hW : ∀ n, IsPrice K (W n))
    (hΛ : ∀ n b (P g : ℤ × ℤ), W n (b, P) (b, P + g) ≤ Λ * (|(g.1 : ℝ)| + |(g.2 : ℝ)|)) (a b : ℤ × ℤ) :
    meanNorm W (a + b) ^ 2 + meanNorm W (a - b) ^ 2 = 2 * meanNorm W a ^ 2 + 2 * meanNorm W b ^ 2 := by
  obtain ⟨N, hN, h⟩ := lem_means W hW Λ hΛ
  have e : N = meanNorm W := funext fun g => (hN g).2.unique (meanNorm_isGLB W g)
  rw [← e]
  exact h a b

end Paper
