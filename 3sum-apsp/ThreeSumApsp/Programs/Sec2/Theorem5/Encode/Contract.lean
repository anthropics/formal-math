/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts
public import ThreeSumApsp.Programs.Sec2.Theorem5.Encode.Meaning

/-!
# What the callers of encode assume

The callers of encode (Section 2.4.1) assume a specification of the procedure that does not name its
body: `EncodeLSpec` for the array a and the forms φ_λ, `EncodeRSpec` for b and ψ_λ.  Both hold for
every program that has encStep and encode at their numbers.  The places that the callers provide are
a layout for encode (`EncodePlaces.layout`), so the specification of encode on lists applies
(`encode_entry`, for any alphabet of seven variables); the two specifications are its cases for the
left variables with the forms φ_λ and for the right variables with the forms ψ_λ.
-/

public section

namespace Light.Sec2

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {n Lmax src dst scr tab p7 p10 : ℕ} {μ : ℕ → ℤ}

/-- The scratch area of encode has fewer than 7^L cells. -/
private theorem scrSize_le (L : ℕ) : scrSize L + 1 ≤ 7 ^ L := by
  induction L with
  | zero => simp [scrSize]
  | succ L ih =>
    rw [scrSize, pow_succ]
    omega

/-- The places that the callers provide are a layout for encode. -/
theorem EncodePlaces.layout (std : Std lim)
    (h : EncodePlaces lim n Lmax src dst scr tab p7 p10 μ) :
    EncodeLayout lim src dst scr tab p7 p10 n := by
  light_facts h
  have hscr := scrSize_le n
  exact ⟨std, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- A cell of a table of powers. -/
private theorem pow_of_seg {p b : ℕ} (h : Seg μ p (powList b (Lmax + 1))) (hn : n ≤ Lmax) :
    ∀ i < n, μ (p + i) = ((b ^ i : ℕ) : ℤ) := fun i hi => by
  rw [h.get (i := i) (by simp; omega), getElem_powList]

/-- **The specification that the callers of encode assume**, for any alphabet of seven variables.
The callers allow `7^n` cells of scratch area, more than the `scrSize n` that `encode` uses. -/
theorem encode_entry {α : Type} [Fintype α] (e : α ≃ Fin 7) (coef : Term → α → ℤ)
    {T : List ℤ} (hT : T.length = 70) (hc : ∀ x ∈ T, -1 ≤ x ∧ x ≤ 1)
    (hcoef : ∀ lam s, T.getD (7 * (termIdx lam : ℕ) + (e s : ℕ)) 0 = coef lam s) (std : Std lim)
    (hS : P[pEncStep]? = some encStepBody) (hE : P[pEncode]? = some (encodeBody pEncStep pEncode))
    {d : ℕ} (hd : d + (n + 1) ≤ lim.depth) (hpl : EncodePlaces lim n Lmax src dst scr tab p7 p10 μ)
    (htab : Seg μ tab T) (A : (Fin n → α) → ℤ) (hsrc : Seg μ src (arrStr e A)) {V : ℤ}
    (hV : ∀ u, |A u| ≤ V) (hVB : 7 ^ (n + 1) * V ≤ lim.word) :
    Meets lim P pEncode d [n, src, dst, scr, tab, p7, p10] μ (cEncode * 10 ^ n) fun _ μ' =>
      Seg μ' dst (arrT (computeEncoding coef n A)) ∧
        SameOutside2 μ μ' dst (10 ^ n) scr (7 ^ n) := by
  have hV0 : 0 ≤ V := (abs_nonneg _).trans (hV fun _ => e.symm 0)
  have hVB' : ((7 ^ n : ℕ) : ℤ) * V ≤ lim.word := by
    refine le_trans ?_ hVB
    push_cast
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)) hV0
  have hscr := scrSize_le n
  refine .of_body hE ((encode_str e coef hT hc hcoef hS hE (hpl.layout std) A hsrc hV htab
    (pow_of_seg hpl.hp7 hpl.n_le) (pow_of_seg hpl.hp10 hpl.n_le) hVB' (by omega)).mono le_rfl
    fun σ' h => ⟨h.1, h.2.mono fun x hx => by omega⟩)

/-- **The specification that the callers of encode assume, for the array a.** -/
theorem encodeL_entry (std : Std lim) (hS : P[pEncStep]? = some encStepBody)
    (hE : P[pEncode]? = some (encodeBody pEncStep pEncode)) : EncodeLSpec lim P cEncode := by
  intro n Lmax src dst scr tab p7 p10 μ a V hpl htab hsrc hV hVB d hd
  exact computeEncoding_phi a ▸ encode_entry leftEquiv phi (by decide) (by decide) phiFlat_spec std
    hS hE hd hpl htab a hsrc hV hVB

/-- **The specification that the callers of encode assume, for the array b.** -/
theorem encodeR_entry (std : Std lim) (hS : P[pEncStep]? = some encStepBody)
    (hE : P[pEncode]? = some (encodeBody pEncStep pEncode)) : EncodeRSpec lim P cEncode := by
  intro n Lmax src dst scr tab p7 p10 μ b V hpl htab hsrc hV hVB d hd
  exact computeEncoding_psi b ▸ encode_entry rightEquiv psi (by decide) (by decide) psiFlat_spec std
    hS hE hd hpl htab b hsrc hV hVB

end Light.Sec2
