/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.End.Run
import NS1.Main
import Nc.Acc.Main

/-!
# The substitution that names letters by bits
-/

set_option linter.unusedSectionVars false

namespace NS1

open Finset MvPolynomial

variable {A : Type} [CommRing A]

/-- The substitution that names the letters by bits. -/
noncomputable def letS (K : Type*) [Field K] {Γ : Type*} [DecidableEq Γ] (bt : Bool → Γ) (N : ℕ) :
    Fin N × Option Γ → MvPolynomial (Fin N × Option Bool) K := fun q =>
  match q.2 with
  | none => X (q.1, none)
  | some γ => if γ = bt true then X (q.1, some true) else if γ = bt false then X (q.1, some false) else 0

theorem eval_letS {K : Type} [Field K] {Γ : Type} [DecidableEq Γ] {bt : Bool → Γ} (hb : Function.Injective bt)
    (N : ℕ) (w : List Bool) (q : Fin N × Option Γ) :
    eval (codeB K N w) (letS K bt N q) =
      if Nc.code N (fun _ : Fin 1 => w.map bt) q then (1 : K) else 0 := by
  obtain ⟨p, o⟩ := q
  have hw : Nc.wordOf (List.ofFn fun _ : Fin 1 => w.map bt) = w.map (some ∘ bt) ++ [none] := by
    simp [Nc.wordOf]
  have hcode : Nc.code N (fun _ : Fin 1 => w.map bt) (p, o) =
      decide ((w.map (some ∘ bt) ++ [none])[(p : ℕ)]? = some o) := by
    unfold Nc.code
    rw [hw]
  have hmap : w.map (some ∘ bt) ++ [none] = (w.map some ++ [none]).map (Option.map bt) := by
    simp
  have hget : ∀ o' : Option Γ, ((w.map (some ∘ bt) ++ [none])[(p : ℕ)]? = some o') ↔
      ∃ x, (w.map some ++ [none])[(p : ℕ)]? = some x ∧ Option.map bt x = o' := by
    intro o'
    rw [hmap, List.getElem?_map, Option.map_eq_some_iff]
  rw [hcode]
  simp only [decide_eq_true_eq, hget]
  rcases o with _ | γ
  · simp only [letS, eval_X, codeB]
    refine if_congr ⟨fun h => ⟨_, h, rfl⟩, ?_⟩ rfl rfl
    rintro ⟨x, h1, h2⟩
    rw [Option.map_eq_none_iff] at h2
    rw [h1, h2]
  · have hx : ∀ b : Bool, γ = bt b → ((∃ x, (w.map some ++ [none])[(p : ℕ)]? = some x ∧
        Option.map bt x = some γ) ↔ (w.map some ++ [none])[(p : ℕ)]? = some (some b)) := by
      intro b hγ
      constructor
      · rintro ⟨x, h1, h2⟩
        rw [Option.map_eq_some_iff] at h2
        obtain ⟨y, rfl, h3⟩ := h2
        rw [h1, hb (h3.trans hγ)]
      · intro h
        exact ⟨_, h, by rw [hγ]; rfl⟩
    by_cases h1 : γ = bt true
    · simp only [letS, if_pos h1, eval_X, codeB]
      exact if_congr (hx true h1).symm rfl rfl
    · by_cases h2 : γ = bt false
      · simp only [letS, if_neg h1, if_pos h2, eval_X, codeB]
        exact if_congr (hx false h2).symm rfl rfl
      · simp only [letS, if_neg h1, if_neg h2, map_zero]
        rw [if_neg]
        rintro ⟨x, -, h3⟩
        rw [Option.map_eq_some_iff] at h3
        obtain ⟨y, -, h4⟩ := h3
        cases y
        · exact h2 h4.symm
        · exact h1 h4.symm

theorem isAffine_letS {K : Type} [Field K] {Γ : Type} [DecidableEq Γ] (bt : Bool → Γ) (N : ℕ)
    (q : Fin N × Option Γ) : Nc.IsAffine (letS K bt N q) := by
  have hX : ∀ j : Fin N × Option Bool, Nc.IsAffine (X j : MvPolynomial (Fin N × Option Bool) K) := fun j =>
    Or.inr ⟨j, 1, 0, by simp⟩
  obtain ⟨p, o⟩ := q
  rcases o with _ | γ
  · exact hX _
  · simp only [letS]
    split_ifs
    · exact hX _
    · exact hX _
    · exact Or.inl ⟨0, by simp⟩

theorem totalDegree_letS {K : Type} [Field K] {Γ : Type} [DecidableEq Γ] (bt : Bool → Γ) (N : ℕ)
    (q : Fin N × Option Γ) : (letS K bt N q).totalDegree ≤ 1 := by
  obtain ⟨p, o⟩ := q
  rcases o with _ | γ
  · simp only [letS]
    exact (totalDegree_X _).le
  · simp only [letS]
    split_ifs
    · exact (totalDegree_X _).le
    · exact (totalDegree_X _).le
    · simp

theorem totalDegree_aeval_le {K : Type*} [Field K] {σ τ : Type*} (p : MvPolynomial σ K)
    (f : σ → MvPolynomial τ K) (hf : ∀ i, (f i).totalDegree ≤ 1) :
    (aeval f p).totalDegree ≤ p.totalDegree := by
  rw [aeval_def, eval₂_eq]
  refine totalDegree_finsetSum_le fun d hd => ?_
  refine (totalDegree_mul _ _).trans ?_
  have h0 : (algebraMap K (MvPolynomial τ K) (coeff d p)).totalDegree = 0 := totalDegree_C _
  rw [h0, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  have h1 : ∀ i ∈ d.support, (f i ^ d i).totalDegree ≤ d i := fun i _ => by
    refine (totalDegree_pow _ _).trans ?_
    calc d i * (f i).totalDegree ≤ d i * 1 := Nat.mul_le_mul_left _ (hf i)
      _ = d i := mul_one _
  refine (sum_le_sum h1).trans ?_
  exact le_totalDegree hd

theorem eval_aeval' {K : Type*} [Field K] {σ τ : Type*} (x : τ → K) (f : σ → MvPolynomial τ K)
    (p : MvPolynomial σ K) : eval x (aeval f p) = eval (fun i => eval x (f i)) p := by
  have h : ((eval x).comp (aeval f : MvPolynomial σ K →ₐ[K] MvPolynomial τ K).toRingHom) =
      eval fun i => eval x (f i) := by
    apply ringHom_ext
    · intro r; simp
    · intro i; simp
  exact DFunLike.congr_fun h p

theorem eval_sub {K : Type} [Field K] {Γ : Type} [DecidableEq Γ] {bt : Bool → Γ}
    (hb : Function.Injective bt) (N : ℕ) (w : List Bool) (p : MvPolynomial (Fin N × Option Γ) K) :
    eval (codeB K N w) (aeval (letS K bt N) p) =
      eval (fun q => if Nc.code N (fun _ : Fin 1 => w.map bt) q then (1 : K) else 0) p := by
  have e1 : (fun q => eval (codeB K N w) (letS K bt N q)) =
      fun q => if Nc.code N (fun _ : Fin 1 => w.map bt) q then (1 : K) else 0 := by
    funext q
    exact eval_letS hb N w q
  exact (eval_aeval' (codeB K N w) (letS K bt N) p).trans (congrArg (fun g => eval g p) e1)

end NS1
