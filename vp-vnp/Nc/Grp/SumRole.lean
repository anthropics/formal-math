/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.RoleProg
import Nc.Grp.SumSim

/-!
# Sums over the runs of the transducer of a role
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

theorem chS_cons (L : G.Law A) (p : L.Ro) {B : ℕ} (z : Bk L p) (f : Fin B → Bk L p) (ν : L.CnAt p) :
    chS L p (Fin.cons z f : Fin (B + 1) → Bk L p) ν = (List.ofFn (L.lab z.1) ++ List.ofFn (z.2 ν)) ++ chS L p f ν := by
  unfold chS Nc.G.chString
  rw [List.ofFn_succ, List.flatten_cons]
  rfl

theorem headD_getD (w : List Bool) : w.headD false = w.getD 0 false := by cases w <;> rfl

theorem tail_getD (w : List Bool) (k : ℕ) : w.tail.getD k false = w.getD (k + 1) false := by cases w <;> simp

theorem sumL_role_gen (L : G.Law A) (p : L.Ro) (htab : ∀ i x g, ∃ e : WE, e.val θ = L.tab p i x g) (B : ℕ)
    (ins : Fin (slList L p).length → List Bool) (out : Fin (cnList L p).length → List Bool)
    (G : TSt 1 (slList L p).length (cnList L p).length Bool → A) :
    sumL (runL θ (roleTab θ L p) B (0, ins, out)) G = ∑ f : Fin B → Bk L p,
      (∏ k, L.tab p (f k).1 (fun e => (ins (slIdx L p e)).getD k false) (f k).2) *
        G (0, fun i => (ins i).drop B, fun j => (chS L p f ((cnList L p).get j)).reverse ++ out j) := by
  induction B generalizing ins out with
  | zero =>
    rw [runL, List.replicate_zero, foldL, sumL_single, Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, List.drop_zero, chS, Nc.G.chString, List.ofFn_zero,
      List.flatten_nil, List.reverse_nil, List.nil_append]
  | succ B ih =>
    rw [sumL_runL_succ]
    have h1 : sumL (stepL θ (roleTab θ L p) (0, ins, out)) (fun s' => sumL (runL θ (roleTab θ L p) B s') G) =
        ∑ z : Bk L p, L.tab p z.1 (fun e => (ins (slIdx L p e)).headD false) z.2 *
          sumL (runL θ (roleTab θ L p) B (0, fun i => (ins i).tail, fun j =>
            (List.ofFn (L.lab z.1) ++ List.ofFn (z.2 ((cnList L p).get j))).reverse ++ out j)) G := by
      rw [stepL, roleTab, List.map_map, sumL_toList]
      refine Finset.sum_congr rfl fun z _ => ?_
      simp only [Function.comp_apply, Opt.app, we_val (htab _ _ _)]
    rw [h1, ← (Fin.consEquiv fun _ : Fin (B + 1) => Bk L p).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    have e1 : (Fin.consEquiv fun _ : Fin (B + 1) => Bk L p) (z, f) = Fin.cons z f := rfl
    rw [e1, Fin.prod_univ_succ, ← mul_assoc]
    congr 1
    · congr 1
      · show L.tab p z.1 (fun e => (ins (slIdx L p e)).headD false) z.2 =
          L.tab p z.1 (fun e => (ins (slIdx L p e)).getD 0 false) z.2
        simp only [headD_getD]
      · refine Finset.prod_congr rfl fun k _ => ?_
        show L.tab p (f k).1 (fun e => (ins (slIdx L p e)).tail.getD k false) (f k).2 =
          L.tab p (f k).1 (fun e => (ins (slIdx L p e)).getD (k + 1) false) (f k).2
        simp only [tail_getD]
    · congr 1
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · funext i
        show (ins i).tail.drop B = (ins i).drop (B + 1)
        cases ins i <;> simp
      · funext j
        show (chS L p f ((cnList L p).get j)).reverse ++ ((List.ofFn (L.lab z.1) ++
          List.ofFn (z.2 ((cnList L p).get j))).reverse ++ out j) =
          (chS L p (Fin.cons z f : Fin (B + 1) → Bk L p) ((cnList L p).get j)).reverse ++ out j
        rw [chS_cons]
        simp only [List.reverse_append, List.append_assoc]

theorem sumL_role (L : G.Law A) (p : L.Ro) (htab : ∀ i x g, ∃ e : WE, e.val θ = L.tab p i x g) (B : ℕ)
    (ins : Fin (slList L p).length → List Bool) (G : TSt 1 (slList L p).length (cnList L p).length Bool → A) :
    sumL (runL θ (roleTab θ L p) B (0, ins, fun _ => [])) G = ∑ f : Fin B → Bk L p,
      (∏ k, L.tab p (f k).1 (fun e => (ins (slIdx L p e)).getD k false) (f k).2) *
        G (0, fun i => (ins i).drop B, fun j => (chS L p f ((cnList L p).get j)).reverse) := by
  rw [sumL_role_gen L p htab]
  simp only [List.append_nil]

end Nc.Grp
