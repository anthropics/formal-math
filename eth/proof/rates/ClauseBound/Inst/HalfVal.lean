/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.HalfIfc

/-! # The pieces with ρ = 1/√2 as programs: the values of the two functions of a factorization

`partH c₀ top` is the program for one of the two functions of a factorization. This file says what
it returns when the pad is long enough (`partH_eq`): the label θ, read as a number,
picks the pair (j, τ) with that number in the list `labs`, and the value is an entry of one of the
matrices `ClauseBound.Boson.topK`, `ClauseBound.Boson.botK` (`valK` of
proof/rates/ClauseBound/Inst/HalfIfc.lean), or 0 if the list has no such pair.
Two statements on the tables are taken as hypotheses: `StTopF` and `StBotF` say that `topF` and
`botF`, applied to the list of all partitions of 0, …, 4h, return the entries of `topK` and `botK`.
The strings enter through their partitions only, which have to be listed and of weight h; the
interface statement `StEnc` says that they are. The end of the file is `stVal`, which proves
the interface statement `StVal` from these three. -/

@[expose] public section

namespace ClauseBound.Inst.Half

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec Finset

/-- With a pad of length at least `padLen h`, `topF` on the list of all partitions of 0, …, 4h
returns the entries of `topK μ h i r`, for a listed μ of weight h and i ≤ 2h. -/
def StTopF : Prop := ∀ (pad : U) (h : ℕ), 1 ≤ h → padLen h ≤ pad.length → ∀ μ ∈ (allTab (4 * h)).flatten, μ.sum = h → ∀ i ≤ 2 * h, ∀ r : ℤ,
  ∀ π ∈ (allTab (4 * h)).flatten, ∀ σ ∈ (allTab (4 * h)).flatten,
    topF pad (4 * h) (allTab (4 * h)).flatten h μ i r π σ = ClauseBound.Boson.topK μ h i r (π : Multiset ℕ) (σ : Multiset ℕ)

/-- With a pad of length at least `padLen h`, `botF` on the list of all partitions of 0, …, 4h
returns the entries of `botK μ h r`, for a listed μ of weight h. -/
def StBotF : Prop := ∀ (pad : U) (h : ℕ), 1 ≤ h → padLen h ≤ pad.length → ∀ μ ∈ (allTab (4 * h)).flatten, μ.sum = h → ∀ r : ℤ,
  ∀ π ∈ (allTab (4 * h)).flatten, ∀ σ ∈ (allTab (4 * h)).flatten,
    botF pad (4 * h) (allTab (4 * h)).flatten h μ r π σ = ClauseBound.Boson.botK μ h r (π : Multiset ℕ) (σ : Multiset ℕ)

namespace Val

/-- A member of an entry of a table is a member of the flattened table. -/
theorem mem_flatten_of_mem_getD {γ : Type} {T : List (List γ)} {n : ℕ} {L : γ} (h : L ∈ T.getD n []) : L ∈ T.flatten := by
  by_cases hn : n < T.length
  · rw [List.getD_eq_getElem _ _ hn] at h
    exact List.mem_flatten.2 ⟨_, List.getElem_mem hn, h⟩
  · rw [List.getD_eq_default _ _ (not_lt.1 hn)] at h
    simp at h

/-- A pair (j, τ) of the list of labels has j ≤ 2h and a listed τ. -/
theorem mem_labs {T : PT} {tr : Bool} {h : ℕ} {s : ℤ} {p : ℕ × List ℕ} (hp : p ∈ labs T tr h s) : p.1 ≤ 2 * h ∧ p.2 ∈ T.flatten := by
  obtain ⟨j, hj, hp⟩ := List.mem_flatMap.1 hp
  split_ifs at hp
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.1 hp
    exact ⟨Nat.lt_succ_iff.1 (List.mem_range.1 hj), mem_flatten_of_mem_getD hτ⟩
  · simp at hp

/-- The number of all partitions of 0, …, 4h, as a sum. -/
theorem deltaF_eq (h : ℕ) : deltaF h = ∑ E ∈ range (4 * h + 1), Partitions.p E := by
  rw [deltaF, pTab_eq, sum_map_range]

/-- A pad of length `padLen h` suffices for the table of all partitions of 0, …, 4h. -/
theorem pad_allTab {h : ℕ} {pad : U} (hp : padLen h ≤ pad.length) :
    (7 * (4 * h) + 10) * ∑ E ∈ range (4 * h + 1), Partitions.p E ≤ pad.length := by
  refine le_trans ?_ hp
  rw [← deltaF_eq, padLen]
  have h1 : h + 2 ≤ (h + 2) ^ 4 := Nat.le_self_pow (by norm_num) _
  have h2 : deltaF h + 1 ≤ (deltaF h + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  exact Nat.mul_le_mul (by omega) (by omega)

end Val

open Val

/-- What `partT` returns on the table of all partitions of 0, …, 4h, if the pad is long enough and
the partitions of the two strings are listed and have weight h. -/
theorem partT_eq (hT : StTopF) (hB : StBotF) {h : ℕ} (hh : 1 ≤ h) {pad : U} (hp : padLen h ≤ pad.length) (tr top : Bool) (s : ℤ) (a b θ : List Bool)
    (ha : encF (allTab (4 * h)) h a ∈ (allTab (4 * h)).flatten ∧ (encF (allTab (4 * h)) h a).sum = h)
    (hb : encF (allTab (4 * h)) h b ∈ (allTab (4 * h)).flatten ∧ (encF (allTab (4 * h)) h b).sum = h) :
    partT pad tr top h s (allTab (4 * h)) a b θ =
      ((labs (allTab (4 * h)) tr h s)[ofWord θ]?).elim 0 (valK tr top h s (encF (allTab (4 * h)) h a) (encF (allTab (4 * h)) h b)) := by
  unfold partT
  cases hq : (labs (allTab (4 * h)) tr h s)[ofWord θ]? with
  | none => rfl
  | some p =>
    obtain ⟨h1, h2⟩ := mem_labs (List.mem_of_getElem? hq)
    simp only [Option.elim]
    cases top <;> cases tr <;> simp only [valK, cond_true, cond_false]
    · exact hB pad h hh hp _ hb.1 hb.2 _ _ ha.1 _ h2
    · exact hB pad h hh hp _ hb.1 hb.2 _ _ h2 _ ha.1
    · exact hT pad h hh hp _ ha.1 ha.2 _ h1 _ _ h2 _ hb.1
    · exact hT pad h hh hp _ ha.1 ha.2 _ h1 _ _ hb.1 _ h2

/-- What `partH c₀ top` returns on two strings of λ bits and a label θ, with h = `hF c₀ λ`, s =
`sOf h i` and T the table of all partitions of 0, …, 4h: the value `valK` at the pair number θ
of the list of labels, or 0 if there is no such pair. The pad has length at least `padLen h`, and
the partitions of the two strings are listed and have weight h. -/
theorem partH_eq (hT : StTopF) (hB : StBotF) {c₀ lam : ℕ} {pad : U} (hp : padLen (hF c₀ lam) ≤ pad.length) (tr top : Bool) (h' i : ℕ)
    (a b : Pieces.Bits lam) (θ : List Bool)
    (ha : encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf a) ∈ (allTab (4 * hF c₀ lam)).flatten ∧
      (encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf a)).sum = hF c₀ lam)
    (hb : encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf b) ∈ (allTab (4 * hF c₀ lam)).flatten ∧
      (encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf b)).sum = hF c₀ lam) :
    partH c₀ top ((pad, tr), (h', i), (bitsOf a, bitsOf b, θ)) =
      ((labs (allTab (4 * hF c₀ lam)) tr (hF c₀ lam) (sOf (hF c₀ lam) i))[ofWord θ]?).elim 0
        (valK tr top (hF c₀ lam) (sOf (hF c₀ lam) i) (encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf a))
          (encF (allTab (4 * hF c₀ lam)) (hF c₀ lam) (bitsOf b))) := by
  have hl : (bitsOf a).length = lam := List.length_ofFn
  simp only [partH, hl]
  rw [allTabF_eq (pad_allTab hp)]
  exact partT_eq hT hB ((by norm_num : 1 ≤ 2).trans (two_le_hF c₀ lam)) hp tr top _ _ _ θ ha hb

/-- The values of the two programs, as the interface states them: h is the least number ≥ 2 with
p(h) ≥ 2^λ, which the program finds if it is at most c₀·λ². -/
theorem stVal (hT : StTopF) (hB : StBotF) (hE : StEnc) : StVal := by
  intro c₀ lam pad _ hc hp tr top h' i a b θ
  have hh : hF c₀ lam = ClauseBound.Part.hOf lam := hF_eq hc
  obtain ⟨e1, -⟩ := hE lam (ClauseBound.Part.hOf lam) ((by norm_num : 1 ≤ 2).trans (ClauseBound.Part.two_le_hOf lam)) (ClauseBound.Part.two_pow_le_p_hOf lam)
  have h := partH_eq hT hB (c₀ := c₀) (lam := lam) (pad := pad) (by rw [hh]; exact hp) tr top h' i a b θ
    (by rw [hh]; exact ⟨(e1 a).2.2, (e1 a).2.1⟩) (by rw [hh]; exact ⟨(e1 b).2.2, (e1 b).2.1⟩)
  rw [hh] at h
  exact h

end ClauseBound.Inst.Half
