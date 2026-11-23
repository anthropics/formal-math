/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Flat
import Nc.RunMn

/-!
# The paper, proof of Lemma lem:circuit: the clause sum Φ
-/

set_option linter.unusedSectionVars false

namespace Paper

open Finset MvPolynomial Nc

section Assignments

variable {F : Type*} [Field F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]
variable {n t M N : ℕ}

/-- **Paper: proof of Lemma lem:circuit, one assignment.** "So there is exactly one assignment for each matched sequence
and each sequence of states": an assignment g that violates no clause gives a matched sequence with the first and last
state, and each of these comes from exactly one. -/
theorem lem_circuit_assignment (i e : Q) (u : Fin n → List Γ) (hM : N + t < M)
    (hN : (wordOf (List.ofFn u)).length ≤ N) (o : Fin t → Letter S (Fin n) Γ) (q : Fin (t + 1) → Q) :
    ((Matched (List.ofFn o) u ∧ q 0 = i ∧ q (Fin.last t) = e) →
      ∃! g : ∀ d, RE Γ S Q n t M d, (gEm g = o ∧ gSt g = q) ∧ Good i e (code N u) (gEm g) (gSt g) (gPl g) (gCt g)) ∧
    ∀ g : ∀ d, RE Γ S Q n t M d, gEm g = o → gSt g = q → Good i e (code N u) (gEm g) (gSt g) (gPl g) (gCt g) →
      Matched (List.ofFn o) u ∧ q 0 = i ∧ q (Fin.last t) = e := by
  refine ⟨fun ⟨h, hi, he⟩ => ?_, fun g h1 h2 hg => h1 ▸ h2 ▸ ⟨hg.matched (by omega), hg.first, hg.last⟩⟩
  obtain ⟨P, c, hg⟩ := exists_good hM hN h hi he
  refine existsUnique_of_exists_of_unique ⟨fun d => match d with
    | .inl τ => o τ
    | .inr (.inl τ) => q τ
    | .inr (.inr (.inl (z, τ))) => P z τ
    | .inr (.inr (.inr (s, p))) => c s p, ⟨rfl, rfl⟩, hg⟩ ?_
  rintro g g' ⟨⟨a1, a2⟩, hg⟩ ⟨⟨a1', a2'⟩, hg'⟩
  have h1 := a1.trans a1'.symm
  have h2 := a2.trans a2'.symm
  funext d
  rcases d with τ | τ | ⟨z, τ⟩ | ⟨s, p⟩
  · exact congrFun h1 τ
  · exact congrFun h2 τ
  · refine Fin.ext ?_
    have e1 := hg.place z τ
    have e2 := hg'.place z τ
    rw [hg.place_zero] at e1
    rw [hg'.place_zero, ← h1] at e2
    exact e1.trans e2.symm
  · have e1 := hg.contents s false p
    have e2 := hg'.contents s false p
    rw [← h1] at e2
    exact e1.trans e2.symm

/-- **Paper: proof of Lemma lem:circuit, the value at a code.** The sum over the assignments at the code of an input is
the value of the automaton on it. -/
theorem lem_circuit_value (mu : Letter S (Fin n) Γ → Matrix Q Q F) (i e : Q) (u : Fin n → List Γ) (hM : N + t < M)
    (hN : (wordOf (List.ofFn u)).length ≤ N) :
    fdSum (rLits (Γ := Γ) (S := S) (n := n) (t := t) (M := M) (N := N) i e) (rWt mu) (code N u) = runVal mu i e t u := by
  classical
  have hl : fdSum (rLits (Γ := Γ) (S := S) (n := n) (t := t) (M := M) (N := N) i e) (rWt mu) (code N u) = ∑ g : ∀ d, RE Γ S Q n t M d,
      if Good i e (code N u) (gEm g) (gSt g) (gPl g) (gCt g) then
        ∏ τ, mu (gEm g τ) (gSt g (Fin.castSucc τ)) (gSt g (Fin.succ τ)) else 0 := by
    unfold fdSum
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Fintype.prod_sum_type]
    have h1 := prod_soft mu (code N u) g
    have h2 := prod_hard (F := F) i e (code N u) g
    refine Eq.trans (b := (∏ τ, mu (gEm g τ) (gSt g (Fin.castSucc τ)) (gSt g (Fin.succ τ))) *
      if Good i e (code N u) (gEm g) (gSt g) (gPl g) (gCt g) then 1 else 0) ?_ (by simp)
    refine congrArg₂ (· * ·) ?_ ?_
    · exact h1
    · refine Eq.trans ?_ h2
      refine Finset.prod_congr rfl fun r _ => ?_
      by_cases hr : ∀ l ∈ hLits i e r, Sum.elim (code N u) (hot g) l.1 = l.2
      · rw [if_pos hr]
        exact if_pos hr
      · rw [if_neg hr]
        exact if_neg hr
  have hr : runVal mu i e t u = ∑ y : (Fin t → Letter S (Fin n) Γ) × (Fin (t + 1) → Q),
      if Matched (List.ofFn y.1) u ∧ y.2 0 = i ∧ y.2 (Fin.last t) = e then
        ∏ τ, mu (y.1 τ) (y.2 (Fin.castSucc τ)) (y.2 (Fin.succ τ)) else 0 := by
    unfold runVal
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun o _ => ?_
    by_cases ho : Matched (List.ofFn o) u
    · rw [if_pos ho, prod_ofFn_apply]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp [ho]
    · simp [ho]
  rw [hl, hr, ← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij (fun g _ => (gEm g, gSt g)) ?_ ?_ ?_ ?_
  · intro g hg
    rw [mem_filter] at hg ⊢
    exact ⟨mem_univ _, (lem_circuit_assignment i e u hM hN _ _).2 g rfl rfl hg.2⟩
  · intro g hg g' hg' heq
    rw [mem_filter] at hg hg'
    obtain ⟨h1, h2⟩ := Prod.mk.inj heq
    exact ((lem_circuit_assignment i e u hM hN _ _).1 ((lem_circuit_assignment i e u hM hN _ _).2 g' rfl rfl hg'.2)).unique
      ⟨⟨h1, h2⟩, hg.2⟩ ⟨⟨rfl, rfl⟩, hg'.2⟩
  · rintro ⟨o, q⟩ hy
    rw [mem_filter] at hy
    obtain ⟨g, ⟨⟨h1, h2⟩, hg⟩, -⟩ := (lem_circuit_assignment i e u hM hN o q).1 hy.2
    exact ⟨g, by rw [mem_filter]; exact ⟨mem_univ _, hg⟩, by rw [h1, h2]⟩
  · intros
    rfl

end Assignments

section Inputs

variable {R : Type} [CommRing R] {ι α κ : Type}

/-- One more clause for every variable of the code: if its bit is 1 its weight is the variable. -/
def withInputs (lits : κ → List ((ι ⊕ α) × Bool)) : κ ⊕ ι → List ((ι ⊕ α) × Bool) :=
  Sum.elim lits fun b => [(Sum.inl b, true)]

/-- The weights: constants, and the variables of the code. -/
noncomputable def inputWeights (w : κ → R) : κ ⊕ ι → MvPolynomial ι R := Sum.elim (fun k => C (w k)) X

theorem clauseSum_inputs {F : Type} [Field F] [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] [Fintype κ]
    (lits : κ → List ((ι ⊕ α) × Bool)) (w : κ → F) :
    clauseSum (withInputs lits) (inputWeights w) = mlExtC 0 (wideSum lits w) := by
  classical
  unfold clauseSum mlExtC wideSum
  rw [← (Equiv.sumArrowEquivProdArrow ι α Bool).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.prod_sum_type, map_prod]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) (Finset.prod_congr rfl fun b _ => ?_)
  · have e : (Equiv.sumArrowEquivProdArrow ι α Bool).symm (x, a) = Sum.elim x a := rfl
    simp only [withInputs, inputWeights, Sum.elim_inl, e]
    rw [apply_ite (C : F → MvPolynomial ι F), map_one]
    split_ifs <;> rfl
  · cases hx : x b <;> simp [withInputs, inputWeights, hx]

end Inputs

theorem card_clauses {a b c d p i : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d] [Fintype p] [Fintype i] :
    Fintype.card ((((a ⊕ b) ⊕ c) ⊕ d ⊕ p × p) ⊕ i) = Fintype.card a + Fintype.card b + Fintype.card c +
      (Fintype.card d + Fintype.card p * Fintype.card p) + Fintype.card i := by
  simp only [Fintype.card_sum, Fintype.card_prod]

theorem literal_bound {B N I E R₁ R₂ R₃ D IE : ℕ} (hB : 1 ≤ B) (hN : N ≤ B) (hE : E ≤ 9 * B ^ 3) (h1 : R₁ ≤ 4 * B ^ 5)
    (h2 : R₂ ≤ 25 * B ^ 5) (hD : D ≤ 6 * B ^ 2) (h3 : R₃ ≤ 2 * B ^ 3) (hI : I ≤ B * B) (hIE : IE = I + E + 3) :
    (R₁ + R₂ + R₃ + (D + E * E) + I) * IE ≤ 1600 * B ^ 9 := by
  have p := fun k (hk : k ≤ 6) => Nat.pow_le_pow_right (show 0 < B from hB) hk
  have h5 := p 5 (by norm_num)
  have h33 := p 3 (by norm_num)
  have h22 := p 2 (by norm_num)
  have hBB : B * B = B ^ 2 := (pow_two B).symm
  have hE2 : E * E ≤ 81 * B ^ 6 := by
    calc E * E ≤ (9 * B ^ 3) * (9 * B ^ 3) := Nat.mul_le_mul hE hE
      _ = 81 * B ^ 6 := by ring
  have h23 : B ^ 2 ≤ B ^ 3 := Nat.pow_le_pow_right hB (by norm_num)
  have h03 : 1 ≤ B ^ 3 := Nat.one_le_pow _ _ hB
  calc (R₁ + R₂ + R₃ + (D + E * E) + I) * IE ≤ 120 * B ^ 6 * (13 * B ^ 3) := Nat.mul_le_mul (by omega) (by omega)
    _ ≤ 1600 * B ^ 9 := by ring_nf; omega

variable {F : Type} [Field F] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S]
  [Fintype Q] [DecidableEq Q]

set_option synthInstance.maxSize 4000 in
set_option maxHeartbeats 1000000 in
/-- **Paper: proof of Lemma lem:circuit, Φ.** A clause sum with at most 1600 B⁹ literals, weights that are constants or
variables, degree at most N, and the automaton's value at the code of every word of fewer than N symbols: what the proof
uses of Φ. ("It has degree at most n, and at the code of a word it takes that word's value ... This has v^O(1) literals.")
B is the sum of the numbers of steps, places, states, symbols and tapes. That Φ is the printed sum over words is not
stated. -/
theorem lem_circuit_phi (mu : Letter S Unit Γ → Matrix Q Q F) (i e : Q) (t N : ℕ) :
    ∃ (V K : Type) (_ : Fintype V) (_ : DecidableEq V) (_ : Fintype K) (_ : DecidableEq K)
      (lits : K → List (V × Bool)) (wt : K → MvPolynomial (Fin N × Option Γ) F),
      (∀ κ, lits κ ≠ []) ∧ (∀ b, ∃ κ, ∃ l ∈ lits κ, l.1 = b) ∧ (∀ κ, (∃ i, wt κ = X i) ∨ ∃ a, wt κ = C a) ∧
      ∑ κ, (lits κ).length ≤ 1600 * (t + N + Fintype.card Q + Fintype.card S + Fintype.card Γ + 2) ^ 9 ∧
      (clauseSum lits wt).totalDegree ≤ N ∧
      ∀ u : List Γ, u.length + 1 ≤ N →
        eval (fun b => if code1 N u b then (1 : F) else 0) (clauseSum lits wt) = runVal mu i e t fun _ => u := by
  classical
  obtain ⟨B, hBdef⟩ : ∃ B, B = t + N + Fintype.card Q + Fintype.card S + Fintype.card Γ + 2 := ⟨_, rfl⟩
  rw [← hBdef]
  have hB : 1 ≤ B := by omega
  obtain ⟨M, hMdef⟩ : ∃ M, M = N + t + 1 := ⟨_, rfl⟩
  let φ : Fin 1 ≃ Unit := Equiv.ofUnique (Fin 1) Unit
  let mu' : Letter S (Fin 1) Γ → Matrix Q Q F := fun a => mu (letterEquiv S Γ φ a)
  have cE := card_RE_le (Γ := Γ) (S := S) (Q := Q) (n := 1) (t := t) (M := M) (B := B) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hB
  have cD := card_RD_le (S := S) (n := 1) (t := t) (M := M) (B := B) (by omega) (by omega)
    (by omega) (by omega) hB
  have cS := card_RS_le (Γ := Γ) (S := S) (Q := Q) (n := 1) (t := t) (B := B) (by omega) (by omega)
    (by omega) (by omega) (by omega) hB
  have cH := card_RH_le (Γ := Γ) (S := S) (n := 1) (t := t) (M := M) (B := B) (by omega) (by omega)
    (by omega) (by omega) (by omega) hB
  have cI : Fintype.card (Fin N × Option Γ) ≤ B * B := by
    rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    exact Nat.mul_le_mul (by omega) (by omega)
  have cV : Fintype.card (RC Γ N) ≤ 2 * B ^ 3 := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
    have h1 : N ≤ B := by omega
    have h2 : Fintype.card Γ + 1 ≤ B := by omega
    have h3 : B ≤ B ^ 3 := Nat.le_self_pow (by omega) B
    calc _ ≤ B * (B * B) + B := by gcongr
      _ = B ^ 3 + B := by ring
      _ ≤ 2 * B ^ 3 := by omega
  let L := Sum.elim (rLits (Γ := Γ) (S := S) (n := 1) (t := t) (M := M) (N := N) i e) cLits
  let W : (RS Γ S Q 1 t ⊕ RH Γ S 1 t M) ⊕ RC Γ N → F := Sum.elim (rWt mu') cRWt
  have hM0 : 0 < M := by omega
  have hE0 : ∀ d : RD S 1 t M, Nonempty (RE Γ S Q 1 t M d)
    | .inl _ => ⟨(none : Letter S (Fin 1) Γ)⟩
    | .inr (.inl _) => ⟨i⟩
    | .inr (.inr (.inl _)) => ⟨⟨0, hM0⟩⟩
    | .inr (.inr (.inr _)) => ⟨(none : Option Γ)⟩
  have hle : ∀ d, Fintype.card (RE Γ S Q 1 t M d) ≤ Fintype.card (Σ d, RE Γ S Q 1 t M d) := fun d =>
    Fintype.card_le_of_injective (Sigma.mk d) sigma_mk_injective
  obtain ⟨f, hf⟩ : ∃ f, f = fdSum L W := ⟨_, rfl⟩
  have hphi : clauseSum (withInputs (fdLits L)) (inputWeights (fdWt W)) = mlExtC 0 f := by
    rw [clauseSum_inputs, hf, show fdSum L W = wideSum (fdLits L) (fdWt W) from funext fun x => fdSum_eq L W x]
  refine ⟨_, _, inferInstance, inferInstance, inferInstance, inferInstance, withInputs (fdLits L), inputWeights (fdWt W),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ((((r | r) | r) | d | ⟨p, q⟩) | b)
    · simp [withInputs, fdLits, L, rLits, sLits]
    · rcases r with ((_ | _) | z | ⟨z, τ, m, a⟩ | ⟨j, j', m⟩ | ⟨s, b, τ, γ, m⟩ | ⟨s, b, m, p⟩ | ⟨j, τ, γ, m⟩ | ⟨j, m⟩) <;>
        simp [withInputs, fdLits, L, rLits, hLits, hM0]
    · rcases r with ⟨p, y, y'⟩ | p <;> simp [withInputs, fdLits, L, cLits, Finset.univ_eq_empty_iff]
    · have := hE0 d
      simp [withInputs, fdLits, Finset.univ_eq_empty_iff, not_isEmpty_iff, this]
    · simp [withInputs, fdLits]
    · simp [withInputs]
  · rintro (b | ⟨d, x⟩)
    · exact ⟨.inr b, (Sum.inl b, true), by simp [withInputs], rfl⟩
    · exact ⟨.inl (.inr (.inl d)), (Sum.inr ⟨d, x⟩, false), by simp [withInputs, fdLits], rfl⟩
  · rintro (k | b)
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl ⟨b, rfl⟩
  · obtain ⟨IE, hIE⟩ : ∃ x, x = Fintype.card (Fin N × Option Γ) + Fintype.card (Σ d, RE Γ S Q 1 t M d) + 3 := ⟨_, rfl⟩
    have hlen : ∀ κ, (withInputs (fdLits L) κ).length ≤ IE := by
      rintro ((((r | r) | r) | d | ⟨p, q⟩) | b)
      · simp [withInputs, fdLits, L, rLits, sLits]
        omega
      · rcases r with ((_ | _) | z | ⟨z, τ, m, a⟩ | ⟨j, j', m⟩ | ⟨s, b, τ, γ, m⟩ | ⟨s, b, m, p⟩ | ⟨j, τ, γ, m⟩ | ⟨j, m⟩) <;>
          simp [withInputs, fdLits, L, rLits, hLits] <;> (try split_ifs) <;> (try simp) <;> omega
      · rcases r with ⟨p, y, y'⟩ | p
        · simp [withInputs, fdLits, L, cLits]
          omega
        · have h1 : ((univ : Finset (Fin N)).filter (· < p)).card ≤ N := (Finset.card_filter_le _ _).trans (by simp)
          have h2 : N + (Fintype.card Γ + 1) ≤ Fintype.card (Fin N × Option Γ) + 1 := by
            rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_option]
            have hN1 : 1 ≤ N := Nat.lt_of_le_of_lt (Nat.zero_le _) p.2
            obtain ⟨N', hN'⟩ := Nat.exists_eq_add_of_le hN1
            subst hN'
            have h9 := Nat.le_mul_of_pos_right N' (Nat.succ_pos (Fintype.card Γ))
            rw [Nat.succ_eq_add_one] at h9
            rw [add_mul, one_mul]
            omega
          simp [withInputs, fdLits, L, cLits]
          omega
      · have := hle d
        simp [withInputs, fdLits]
        omega
      · simp [withInputs, fdLits]
        omega
      · simp [withInputs]
        omega
    refine (Finset.sum_le_card_nsmul _ _ IE fun κ _ => hlen κ).trans ?_
    rw [smul_eq_mul, Finset.card_univ]
    rw [card_clauses]
    exact literal_bound hB (by omega) cE cS cH cD cV cI hIE
  · rw [hphi]
    refine totalDegree_mnExt f fun b hb => ?_
    rw [hf, fdSum_valid] at hb
    by_cases hx : VOk b
    · exact card_ones_le hx
    · rw [if_neg hx] at hb
      exact absurd rfl hb
  · intro u hu
    have hv : ∀ b, f b = if VOk b then fdSum (rLits (Γ := Γ) (S := S) (n := 1) (t := t) (M := M) (N := N) i e)
        (rWt mu') b else 0 := by
      intro b
      rw [hf, fdSum_valid]
    rw [hphi]
    have hcode : code N (fun _ : Fin 1 => u) = code1 N u := by
      funext b
      simp [code, code1, wordOf]
    have hval : f (code1 N u) = runVal mu i e t fun _ => u := by
      rw [hv, if_pos (vOk_code1 u hu), ← hcode, lem_circuit_value mu' i e (fun _ => u) (by omega)
        (by rw [length_wordOf_ofFn]; simpa using hu)]
      exact runVal_rename φ mu i e t fun _ => u
    have hline : line (fun b => if code1 N u b then (1 : F) else 0) (mlExtC 0 f) =
        Polynomial.C (runVal mu i e t fun _ => u) * Polynomial.X ^ (u.length + 1) := by
      rw [line_mnExt, Finset.sum_eq_single (code1 N u)]
      · rw [if_pos fun _ h => h, hval, card_ones_code1 u hu]
      · intro b _ hne
        split_ifs with h
        · have h0 : f b = 0 := by
            rw [hv]
            exact if_neg fun hx => hne (eq_code1 hx h)
          rw [h0, map_zero, zero_mul]
        · rfl
      · intro h
        exact absurd (mem_univ _) h
    rw [← eval_one_line, hline]
    simp

end Paper
