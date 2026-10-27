/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Half.Consts
public import GeneralPieces.Half.Size
public import GeneralPieces.Trim.Prog
public import ClauseBound.Inst.HalfAll

/-! # The pieces with ρ = 1/√2 as programs: their specification, from the statements about the ring

This file specifies the programs `halfF c₀ c`. That the pieces add up to h!·[x = v][y = u] and that
they are the sums of displays (54) and (55) is taken
from `AppHalfPieces.PieceFacts`, the steps of the proof of the theorem on pieces with ρ = 1/√2 as
statements about the ring ℚ[t₁, t₂, …] (a hypothesis of every theorem here). The bounds on the
pieces and on the values that the programs return are those of the
paragraph «Sizes and operations» of that proof (`Half/Size.lean`), and the two constants are chosen
from its paragraph «Numbers of bits», from log Δ = O(λ) and from the theorem on pieces with ρ = 1/√2
without the bound on operations of Definition 7(c)
(`thmHalfPiecesPure`). That the programs return the entries of the matrices, the list of the labels
and the encoding of the strings is taken from the lemmas about the programs (`stVal_all`, `stLabs`,
`stEnc`). -/

public section

namespace GeneralPieces

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half Finset

/-- The piece number i for strings of λ bits, as an integer function: A_s with s = i − 2h, h the
least number ≥ 2 with p(h) ≥ 2^λ, and μ(x) the partition with number x (lowest bit first) in the
programs' table of
the partitions of h, which is the lexicographic list of Appendix B (proved in `Half/Order.lean`). -/
@[expose] noncomputable def halfA (lam i : ℕ) : Pieces.Four lam :=
  ClauseBound.Boson.ApcL (ell (ClauseBound.Part.hOf lam)) (ClauseBound.Part.hOf lam) ((i : ℤ) - 2 * ClauseBound.Part.hOf lam)

/-- The two factorizations of the pieces by the two programs. The row half is display (54) on the
ring (`ApcL_row_eq`); the column half is display (55) in a form for the matrices
(`ClauseBound.Boson.ApcL_col_eq`);
display (55) on the ring is used where the function is identified with the A_s of Appendix B
(`ApcL_eq_piece`). -/
theorem stFact (hPF : AppHalfPieces.PieceFacts) : StFact := by
  intro c₀ c lam pad hl hC hp h' i hi x y u v
  have hh : 1 ≤ ClauseBound.Part.hOf lam := le_trans (by norm_num) (ClauseBound.Part.two_le_hOf lam)
  have hℓ : ∀ x : Pieces.Bits lam, ClauseBound.Boson.Pos (ell (ClauseBound.Part.hOf lam) x) ∧ (ell (ClauseBound.Part.hOf lam) x).sum = ClauseBound.Part.hOf lam :=
    fun x => ⟨((stEnc lam _ hh (ClauseBound.Part.two_pow_le_p_hOf lam)).1 x).1, ((stEnc lam _ hh (ClauseBound.Part.two_pow_le_p_hOf lam)).1 x).2.1⟩
  constructor
  · rw [Fact.sum_words_eq stWords stLabs stVal_all hl hC hp false h' hi, ApcL_row_eq hPF hℓ hh]
    rfl
  · rw [Fact.sum_words_eq stWords stLabs stVal_all hl hC hp true h' hi, ClauseBound.Boson.ApcL_col_eq hℓ]
    rfl

/-- The programs realize the functions `halfA`, at every length at which the constants are large
enough. -/
theorem half_realizes (hPF : AppHalfPieces.PieceFacts) {c₀ c lam : ℕ} (h' : ℕ) (hl : 1 ≤ lam) (hC : Cst c₀ c lam) : Realizes (halfF c₀ c) h' lam (halfA lam) := by
  have hhF : hF c₀ lam = ClauseBound.Part.hOf lam := hF_eq hC.h_le
  have hh2 := ClauseBound.Part.two_le_hOf lam
  have hh1 : 1 ≤ ClauseBound.Part.hOf lam := by omega
  obtain ⟨hℓ, hinj⟩ := stEnc lam (ClauseBound.Part.hOf lam) hh1 (ClauseBound.Part.two_pow_le_p_hOf lam)
  have hℓ' : ∀ x : Pieces.Bits lam, ClauseBound.Boson.Pos (ell (ClauseBound.Part.hOf lam) x) ∧ (ell (ClauseBound.Part.hOf lam) x).sum = ClauseBound.Part.hOf lam :=
    fun x => ⟨(hℓ x).1, (hℓ x).2.1⟩
  have hbig : (2 : ℤ) ^ ClauseBound.Boson.big (ClauseBound.Part.hOf lam) ≤ 2 ^ (2 * lam) ^ c := pow_le_pow_right₀ (by norm_num) hC.bits
  have hcnt : (halfF c₀ c).cnt h' lam = 4 * ClauseBound.Part.hOf lam + 1 := by
    change 4 * hF c₀ lam + 1 = _
    rw [hhF]
  refine ⟨fun x y u v => ?_, fun i hi x y u v => ?_, fun pad hpad i hi => ?_⟩
  · rw [hcnt]
    unfold halfA
    rw [Spec.sum_range_shift (ClauseBound.Part.hOf lam) fun s => ClauseBound.Boson.ApcL (ell (ClauseBound.Part.hOf lam)) (ClauseBound.Part.hOf lam) s x y u v,
      sum_ApcL hPF hℓ' hinj hh1]
    change _ = ((factN (hF c₀ lam) : ℕ) : ℤ) * _
    rw [factN_eq, hhF]
  · rw [hcnt] at hi
    refine (GeneralPieces.Half.abs_ApcL_lt hPF (ClauseBound.Part.two_pow_le_p_hOf lam) hℓ' hh1 ?_ x y u v).le.trans hbig
    rw [abs_le]
    omega
  · rw [hcnt] at hi
    have hpad' : 2 ^ (c * lam) ≤ pad.length := hpad
    refine ⟨fun x y u v => (stFact hPF c₀ c lam pad hl hC hpad' h' i hi x y u v).1,
      fun x y u v => (stFact hPF c₀ c lam pad hl hC hpad' h' i hi x y u v).2, fun tr x y θ => ?_⟩
    have key : ∀ top : Bool, |partH c₀ top ((pad, tr), (h', i), (bitsOf x, bitsOf y, θ))| ≤ 2 ^ (2 * lam) ^ c := by
      intro top
      rw [stVal_all c₀ lam pad hl hC.h_le ((Spec.padLen_le hC).trans hpad') tr top h' i x y θ]
      cases hp : (labs (allTab (4 * ClauseBound.Part.hOf lam)) tr (ClauseBound.Part.hOf lam) (sOf (ClauseBound.Part.hOf lam) i))[ofWord θ]? with
      | none =>
        simp only [Option.elim_none, abs_zero]
        positivity
      | some p =>
        have hmem := (stLabs tr (ClauseBound.Part.hOf lam) (sOf (ClauseBound.Part.hOf lam) i) (Spec.abs_sOf_le _ _)).2.2 p (List.mem_of_getElem? hp)
        simp only [Option.elim_some]
        exact (GeneralPieces.Half.abs_valK_lt hh1 tr top _ (hℓ' x) (hℓ' y) (mem_flatten_allTab.1 hmem.1).2.1 (mem_flatten_allTab.1 hmem.1).1).le.trans hbig
    exact ⟨key true, key false⟩

/-- The specification of the pieces at every length at which the constants are large enough. -/
theorem stSpec (hPF : AppHalfPieces.PieceFacts) : StSpec := by
  intro c₀ c lam h' hl hC
  have hhF : hF c₀ lam = ClauseBound.Part.hOf lam := hF_eq hC.h_le
  refine ⟨Nat.succ_pos _, ?_, ?_, fun tr i _ => min_le_left _ _, halfA lam, half_realizes hPF h' hl hC⟩
  · change 1 ≤ factN (hF c₀ lam)
    rw [factN_eq]
    exact Nat.factorial_pos _
  · change 1 ≤ c
    by_contra h0
    have h1 : c = 0 := by omega
    have h2 := hC.cnt
    have h3 := ClauseBound.Part.two_le_hOf lam
    rw [h1, pow_zero] at h2
    omega

/-- For suitable constants the pieces with ρ = 1/√2, as programs, have the parameters (1/√2, c), and
the constants are large enough at every length. -/
theorem exists_par_half2 (hPF : AppHalfPieces.PieceFacts) :
    ∃ c₀ c : ℕ, ClauseBound.Gen.Par (halfF c₀ c) (1 / Real.sqrt 2) c ∧ ∀ lam : ℕ, 1 ≤ lam → Cst c₀ c lam := by
  obtain ⟨c₀, c, hC⟩ := exists_cst2 (thmHalfPiecesPure hPF)
  exact ⟨c₀, c, ClauseBound.Inst.Half.Par.par_of_cst (stSpec hPF) hC, hC⟩

end GeneralPieces
