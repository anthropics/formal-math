/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.Col.Colouring
public import StepMachines.Prog.NetVal
public import PaddedDescent.F.Interfaces

/-! # The search for a colouring succeeds on few nodes

`PaddedDescent.F.goodG` compares the label bits between two classes with a bound β given as an
argument; it is a variant of the test `goodB`, whose bound is computed from the network and contains
the error term of a colouring lemma.
`goodG_iff` says what the test means, and `exists_goodG` that some colouring among the
K^g passes it, if no two nodes share more than M label bits, 4·D²·m·K ≤ g, (g+2)·K < 2^m and U +
3g²M/D ≤ K²·β. -/

public section

namespace PaddedDescent.Col

open Groundwork Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F Finset

variable {C : Type}

variable {K g : ℕ} (Np : PNet C) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}

/-- What the test says: every class has fewer than 2g/K nodes, and two classes share at most β label
bits. -/
theorem goodG_iff (hK : 0 < K) (hN : Np.Presents c N t S) (β x : ℕ) :
    goodG K g Np β (c, x) = true ↔ (∀ G : Fin K, K * #{a : Fin g | chi hK x a = G} < 2 * g) ∧
      ∀ G G' : Fin K, G ≠ G' → (N.merge (chi hK x) [] []).c G G' ≤ β := by
  simp only [goodG, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, Bool.or_eq_true,
    beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun G => ?_, fun G G' hne => ?_⟩
    · rw [← length_members]; exact h1 G.val G.2
    · rw [← lbLen_eq Np hK hN x hne]
      exact (h2 G.val G.2 G'.val G'.2).resolve_left fun e => hne (Fin.ext e)
  · rintro ⟨h1, h2⟩
    refine ⟨fun G hG => ?_, fun G hG G' hG' => ?_⟩
    · rw [length_members hK x ⟨G, hG⟩]; exact h1 _
    · by_cases e : G = G'
      · exact .inl e
      · right
        have hne : (⟨G, hG⟩ : Fin K) ≠ ⟨G', hG'⟩ := fun e' => e (congrArg Fin.val e')
        rw [lbLen_eq Np hK hN x hne]
        exact h2 _ _ hne

/-- Some colouring among the K^g passes the test. -/
theorem exists_goodG {M D m β : ℕ} (hK : 1 ≤ K) (hN : Np.Presents c N t S) (hM0 : 0 < M) (hD : 1 ≤ D)
    (hM : ∀ a b, a ≠ b → N.c a b ≤ M) (h1 : 4 * D ^ 2 * m * K ≤ g) (h2 : (g + 2) * K < 2 ^ m)
    (hβ : D * N.U + 3 * g ^ 2 * M ≤ D * K ^ 2 * β) : ∃ x < K ^ g, goodG K g Np β (c, x) = true := by
  have hK0 : 0 < K := hK
  obtain ⟨χ, a1, a2⟩ := exists_colouring_cap_nat hK (fun a b => if a = b then 0 else N.c a b) M D m hM0 hD
    (fun a b => by
      by_cases e : a = b
      · simp [e]
      · simpa [e] using hM a b e) h1 h2
  have hχ : chi hK0 (finFunctionFinEquiv χ).val = χ := by
    funext a
    have := congrFun (finFunctionFinEquiv.symm_apply_apply χ) a
    rw [← this]
    rfl
  refine ⟨(finFunctionFinEquiv χ).val, (finFunctionFinEquiv χ).2, (goodG_iff Np hK0 hN β _).2 ?_⟩
  rw [hχ]
  refine ⟨a1, fun G G' hne => ?_⟩
  rw [Network.merge_c]
  have e1 : ∑ a with χ a = G, ∑ b with χ b = G', (if a = b then 0 else N.c a b)
      = ∑ a with χ a = G, ∑ b with χ b = G', N.c a b := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    have hab : a ≠ b := fun e => hne (by rw [← (Finset.mem_filter.1 ha).2, ← (Finset.mem_filter.1 hb).2, e])
    rw [if_neg hab]
  have e2 : ∑ a, ∑ b, (if a = b then 0 else N.c a b) = N.U := by
    rw [Network.U]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_erase (univ : Finset (Fin g)) (a := a) (by simp)]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [if_neg (Finset.ne_of_mem_erase hb).symm]
  have a3 := a2 G G'
  rw [e1, e2] at a3
  have hpos : 0 < D * K ^ 2 := by positivity
  exact Nat.le_of_mul_le_mul_left (a3.trans hβ) hpos

end PaddedDescent.Col
