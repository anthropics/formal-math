/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.HalfTabSpec
public import ClauseBound.Boson.Half

/-! # The second factor of a term of a piece, from the table of ν[·]

`zzF` computes z_ν, and `botF` computes the entries of (h!/z_ν)·ν[r], if the list of monomials is in
order, all parts of ν are at most W and the pad is long enough. -/

public section

namespace ClauseBound.Inst.Half

open Finset Groundwork PaddedDescent.F ClauseBound.Inst.Rec ClauseBound.Boson

namespace HalfTabBot

/-- A product over the distinct members of a list. -/
theorem prod_toFinset_coe (ν : List ℕ) (g : ℕ → ℤ) : ∏ k ∈ (ν : Multiset ℕ).toFinset, g k = (ν.dedup.map g).prod := by
  have h : (ν : Multiset ℕ).toFinset.val = (ν.dedup : Multiset ℕ) := by rw [Multiset.toFinset_val, Multiset.coe_dedup]
  rw [Finset.prod_eq_multiset_prod, h, Multiset.map_coe, Multiset.prod_coe]

end HalfTabBot

/-- `zzF` computes z_ν. -/
theorem zzF_eq (ν : List ℕ) : zzF ν = ClauseBound.Boson.zz (ν : Multiset ℕ) := by
  rw [zzF, ← HalfTabBot.prod_toFinset_coe ν fun k => ((k ^ ν.count k * factN (ν.count k) : ℕ) : ℤ), ← Nat.cast_prod, Int.natAbs_natCast, zz]
  exact Finset.prod_congr rfl fun k _ => by rw [factN_eq, Multiset.coe_count]

/-- `botF` computes the entries of (h!/z_μ)·μ[r]. -/
theorem botF_eq {pad : U} {W : ℕ} {flat : List (List ℕ)} {μ : List ℕ} (hW : 1 ≤ W) (hf : FlatOK W flat) (hμ : ∀ n ∈ μ, n ≤ W)
    (hp : padOp W flat.length μ.length ≤ pad.length) (h : ℕ) (r : ℤ) {π σ : List ℕ} (hπ : π ∈ flat) (hσ : σ ∈ flat) :
    botF pad W flat h μ r π σ = ClauseBound.Boson.botK μ h r ↑π ↑σ := by
  unfold botF botK
  by_cases hr : r = (π.sum : ℤ) - σ.sum
  · rw [if_pos hr, factN_eq, zzF_eq, tabOp_rep hW hf hμ hp π hπ σ hσ, hr]
  · rw [if_neg hr]
    have h0 : op μ r (π : Multiset ℕ) (σ : Multiset ℕ) = 0 := by
      by_contra hne
      have hg := op_grade hne
      rw [Multiset.sum_coe, Multiset.sum_coe] at hg
      exact hr (by omega)
    rw [h0, mul_zero]

end ClauseBound.Inst.Half
