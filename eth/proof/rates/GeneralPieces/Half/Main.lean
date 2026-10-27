/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Half.Spec
public import GeneralPieces.Half.Order
public import GeneralPieces.DefGenPieces.Conv
public import ClauseBound.Inst.CertHalf
public import ClauseBound.Inst.HalfEnd

/-! # The theorem on pieces with ρ = 1/√2, with the running time

`AppRunningTime.ThmHalfPieces`: the programs `halfF c₀ c` are pieces with parameters (1/√2, c') in
the sense of the definition in Appendix A, for the constant c' = `max (c + 1) (2 * (halfF c₀ c).m)`
of the proof below, and they are the pieces of the proof in Appendix B: h is the least number ≥ 2
with p(h) ≥ 2^λ, μ(x) is the partition of h with number x in the lexicographic list, 𝓘 = {−2h, …,
2h} is numbered from 0 to 4h, d = h!, A_s is the coefficient of t^{μ(u)} in
Q_s(a^{μ(x)}, b^{μ(v)})·t^{μ(y)}, and the numbers of bits are ⌈log R^row_s⌉ and ⌈log R^col_s⌉. The
statements about the ring, `AppHalfPieces.PieceFacts`, are a hypothesis. The cut-offs in the
programs
(the search for h up to c₀·λ², the number of a piece at 4h, the numbers of bits at 2cλ) are not
active for the constants that are chosen. The running times of the proof's last paragraph are those
of the programs `halfF`: they are functions of an input and of a padding input,
run in polynomial time, and give the right values once the padding input has 2^{cλ} units, which
stands for the bound of 2^{cλ} operations in part (c) of that definition; they are not restated
sentence by sentence. -/

public section

namespace GeneralPieces

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half GeneralPieces.Half

/-- The theorem on pieces with ρ = 1/√2, with the running time, for the functions of its proof,
given the statements about the ring (`AppHalfPieces.PieceFacts`, proved in
`proof/rates/GeneralPieces/Main.lean`). -/
theorem thmHalfPieces (hPF : AppHalfPieces.PieceFacts) : AppRunningTime.ThmHalfPieces := by
  obtain ⟨c₀, c, hP, hC⟩ := exists_par_half2 hPF
  refine ⟨max (c + 1) (2 * (halfF c₀ c).m), halfF c₀ c, halfA, valOf (halfF c₀ c),
    of_par_realizes hP (Cert.halfF_keeps c₀ c) half_le lt_one fun lam hl => half_realizes hPF 0 hl (hC lam hl), fun lam hl => ?_⟩
  have hhF : hF c₀ lam = ClauseBound.Part.hOf lam := hF_eq (hC lam hl).h_le
  have hh1 : 1 ≤ ClauseBound.Part.hOf lam := le_trans (by norm_num) (ClauseBound.Part.two_le_hOf lam)
  have hℓ : ∀ x : Pieces.Bits lam, ClauseBound.Boson.Pos (ell (ClauseBound.Part.hOf lam) x) ∧ (ell (ClauseBound.Part.hOf lam) x).sum = ClauseBound.Part.hOf lam :=
    fun x => ⟨((stEnc lam _ hh1 (ClauseBound.Part.two_pow_le_p_hOf lam)).1 x).1, ((stEnc lam _ hh1 (ClauseBound.Part.two_pow_le_p_hOf lam)).1 x).2.1⟩
  have hcnt : (halfF c₀ c).cnt 0 lam = 4 * ClauseBound.Part.hOf lam + 1 := by
    change 4 * hF c₀ lam + 1 = _
    rw [hhF]
  rw [hOf_eq lam]
  refine ⟨fun x => ptn (ell (ClauseBound.Part.hOf lam) x), isMu (ClauseBound.Part.two_pow_le_p_hOf lam), hcnt, ?_, fun i hi => ⟨fun x y u v => ?_, ?_, ?_⟩⟩
  · change factN (hF c₀ lam) = _
    rw [factN_eq, hhF]
  · exact ApcL_eq_piece hPF hℓ hh1 _ x y u v
  · exact Fact.cap_eq (hC lam hl) false 0 (hcnt ▸ hi)
  · exact Fact.cap_eq (hC lam hl) true 0 (hcnt ▸ hi)

end GeneralPieces
