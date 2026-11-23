/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Groups
import Nc.Tower.Tower
import Nc.Tow.Cst

/-!
# The paper, section "Networks are sums of thin trees": the tower
-/

namespace Paper

open Finset Nc.Tow
open Nc.Tower (U x NN ee tower SL2 gen th evG sh XX)

/-- **Paper: Proposition prop:tower.** "There are G_n-sets X^(0) = G_n, …, X^(J) with equivariant projections that are b
to one, such that (a) for every i the X_k, k ≠ i, generate a copy of U_h (in order), which acts freely; (b) c and X_i c
always lie in different i-cosets, and π maps every i-coset
bijectively onto one, exactly b of them onto each; (c) |X^(J)| ≤ const, and |G_n| has
bounded quotients; (d) every element of G_n is a word of at most O(n+1)^7 letters X_k." An i-coset of stage j is an orbit of th i; VV are
the chambers with coordinate 1, one in each coset (Paper.prop_tower_representatives), so their fibres count the cosets over a coset. -/
theorem prop_tower (h : ℕ) [NeZero h] (h3 : 3 ≤ h) :
    ∃ C : ℕ, ∀ n : ℕ,
      Fintype.card (XX h n 0) = Nat.card (Nc.Tower.G h n) ∧
      (∀ j < Nc.Tower.JJ h n, (∀ d : XX h n (j + 1),
          (univ.filter fun c : XX h n j => Nc.Tower.pr c = d).card = 2 ^ ee h) ∧
        ∀ (g : Nc.Tower.G h n) (c : XX h n j), Nc.Tower.pr (g • c) = g • Nc.Tower.pr c) ∧
      (∀ i : Fin h, Function.Injective (th i : U h →* Nc.Tower.G h n) ∧
        (∀ l, (th i (x h l) : Nc.Tower.G h n) = gen (by omega) (sh i l)) ∧
        (∀ j (u : U h) (c : XX h n j), (th i u : Nc.Tower.G h n) • c = c → u = 1) ∧
        (∀ j (c : XX h n j) (u : U h), (th i u : Nc.Tower.G h n) • c ≠ (gen (by omega) i : Nc.Tower.G h n) • c) ∧
        ∀ j (c : XX h n j) (u : U h), Nc.Tower.pr ((th i u : Nc.Tower.G h n) • c) = (th i u : Nc.Tower.G h n) • Nc.Tower.pr c) ∧
      (∀ i : Fin h, (∀ k, k ≠ i → ∃ l, sh i l = k) ∧
        (∀ (H : Subgroup (Nc.Tower.G h n)), (∀ k, k ≠ i → gen (by omega) k ∈ H) → ∀ u : U h, (th i u : Nc.Tower.G h n) ∈ H) ∧
        ∀ j < Nc.Tower.JJ h n, ∀ v : Nc.Tower.VV h n (j + 1) i,
          (univ.filter fun w : Nc.Tower.VV h n j i => Nc.Tower.prV w = v).card = 2 ^ ee h) ∧
      Fintype.card (XX h n (Nc.Tower.JJ h n)) < Nat.card (SL2 h) * 2 ^ ee h ∧
      Nat.card (Nc.Tower.G h (n + 1)) = Nat.card (Nc.Tower.G h n) * 2 ^ (h ^ 2 - 1) ∧
      ∀ g : Nc.Tower.G h n, ∃ l : List (Fin h), l.length ≤ C * (n + 1) ^ 7 ∧ (l.map (gen (by omega))).prod = g := by
  obtain ⟨C, hC⟩ := Nc.Tower.exists_diam h (by omega) h3
  refine ⟨C, fun n => ⟨?_, fun j hj => ⟨prop_tower_fibre hj, prop_tower_equivariant⟩, fun i => ⟨Nc.Tower.th_injective i,
    Nc.Tower.th_x (by omega) i, fun j u c e => prop_tower_free i u c e,
    fun j c u => prop_tower_cosets (by omega) i c u, fun j c u => prop_tower_equivariant _ c⟩,
    fun i => ⟨fun k hk => Nc.Tower.exists_sh hk, fun H hH u => ?_, fun j hj v => prop_tower_cosets_over hj v⟩,
    Nc.Tower.card_XJ h n (by omega), Nc.Tower.card_G_succ, fun g => hC n g⟩⟩
  · simpa using Nc.Tower.card_XX (h := h) (n := n) (j := 0) (Nat.zero_le _)
  · refine Nc.Flag.mem_of_x (H.comap (th i : U h →* Nc.Tower.G h n)) (fun l => ?_) u
    show (th i (x h l) : Nc.Tower.G h n) ∈ H
    rw [Nc.Tower.th_x (by omega)]
    exact hH _ (Nc.Tower.sh_ne i l)

end Paper
