/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Tower.Chain
import Tower.Kernel
import Tower.Runs

/-! # Runs of the tower

A run of the solver, with its calls and queries answered as the specification says, is a run of
`nest Sol Inn` with the list env beside every state (`sol_sim`); the same for the procedure
(`inn_sim`). So `nest Sol Inn` meets the hypothesis of
`SelfCallRuns` with the good inputs, values, depths and costs of `Chain.lean` (`nest_within`), and
`TowerRuns` is its conclusion on the input `Sum.inl ([], c)`. -/

public section

namespace QueryMachines.Tower

open Groundwork

variable {Ctx Q G A : Type} [HasSize Ctx] {P : Spec Ctx Q A} {gl : G → Option A} {wg : G → ℕ} {Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A} {Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A}
  {TS : ℕ → ℕ → ℕ → ℕ} {TI : ℕ → ℕ → ℕ} {SS SI SC : ℕ} {c0 : Ctx} {f0 : Q → Option A} {tq : ℕ}

/-- The states of `nest Sol Inn`. -/
abbrev NSt (Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A) (Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A) : Type := (List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ)

/-- A run of the solver on the instance at the end of a chain is a run of `nest Sol Inn` with the
list env beside every state, at the prices of `Chain.lean`. -/
theorem sol_sim (hM : P.Meets gl wg Sol Inn TS TI SS SI SC) (hG : P.Good c0 f0) (env : List Ctx) (hC : Chain P c0 f0 env) {b : A} {s : Sol.σ} {own : ℕ} {L : List (Ctx ⊕ (Q ⊕ G))}
    (hr : Sol.Reaches (P.oracle gl (parent c0 env) (tabs P f0 env)) SS b s own L) :
    (nest Sol Inn).WithinFrom (callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P) (Sum.inl (env, parent c0 env))) (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2) (Sum.inl (env, s) : NSt Sol Inn)
      (own + (L.map (Sum.elim (fun _ => callCost TS TI (P.lev (parent c0 env)) (price P TI tq env)) (Sum.elim (fun _ => price P TI tq env) wg))).sum) (P.lev c0 * (SC + 1) + SS + SI + 2) b := by
  obtain ⟨hGd, hlev, hsize⟩ := chain_facts hM hG env hC
  have hsz : ∀ s : Sol.σ, size s ≤ SS → size (Sum.inl (env, s) : NSt Sol Inn) ≤ (P.lev c0 * (SC + 1) + SS + SI + 2) := fun s hs => by
    have : env.length * (SC + 1) ≤ P.lev c0 * (SC + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [size_inl, size_prod]; dsimp only; omega
  induction hr with
  | halt h1 h2 => exact wfHalt (M := nest Sol Inn) h1 (hsz _ h2)
  | @step s own L h1 h2 h3 _ ih =>
    have ha : (nest Sol Inn).ask (Sum.inl (env, s) : NSt Sol Inn) = none := by simp [nest, h2]
    exact wfMono (wfStep (M := nest Sol Inn) (s := (Sum.inl (env, s) : NSt Sol Inn)) h1 ha (hsz _ h3) ih) (by omega) le_rfl
  | @query s own L z v h1 h2 h3 h4 _ ih =>
    rcases z with c' | y
    · obtain ⟨hch, rfl⟩ : P.Child (parent c0 env) (tabs P f0 env) c' ∧ P.val c' (P.tab c' (tabs P f0 env)) = v := by simpa [Spec.oracle] using h3
      have hl := hM.child_lev _ _ c' hGd hch
      have ha : (nest Sol Inn).ask (Sum.inl (env, s) : NSt Sol Inn) = some (Sum.inr (Sum.inl (c' :: env, c'))) := by simp [nest, h2]
      have ho : callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P) (Sum.inl (env, parent c0 env)) (Sum.inr (Sum.inl (c' :: env, c'))) = some (Sum.inr (P.val c' (P.tab c' (tabs P f0 env)))) :=
        callOracle_call _ _ ⟨⟨⟨hC, hch⟩, rfl⟩, by show 2 * P.lev c' + (env.length + 1) + 1 < 2 * P.lev (parent c0 env) + env.length + 1; omega⟩
      have hw : (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2) (Sum.inr (Sum.inl (c' :: env, c'))) = callCost TS TI (P.lev (parent c0 env)) (price P TI tq env) := by rw [← hl]; rfl
      refine wfMono (wfQuery (M := nest Sol Inn) (s := (Sum.inl (env, s) : NSt Sol Inn)) (w := (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2)) h1 ha ho (hsz _ h4) ih) ?_ le_rfl
      rw [hw]; simp only [List.map_cons, List.sum_cons, Sum.elim_inl]; omega
    · obtain ⟨r, ho, rfl, hw⟩ := up_ok tq gl wg TS env hC y v (by cases y <;> exact h3) (Sum.inl (env, parent c0 env))
        (by show env.length ≤ 2 * P.lev (parent c0 env) + env.length + 1; omega)
      have ha : (nest Sol Inn).ask (Sum.inl (env, s) : NSt Sol Inn) = some (upQuery env y) := by simp [nest, h2]
      refine wfMono (wfQuery (M := nest Sol Inn) (s := (Sum.inl (env, s) : NSt Sol Inn)) (w := (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2)) h1 ha ho (hsz _ h4) ih) ?_ le_rfl
      rw [hw]; simp only [List.map_cons, List.sum_cons, Sum.elim_inr]; omega

/-- The same for a run of the procedure. -/
theorem inn_sim (hM : P.Meets gl wg Sol Inn TS TI SS SI SC) (hG : P.Good c0 f0) (env : List Ctx) (hC : Chain P c0 f0 env) (c : Ctx) (q : Q) {b : A} {i : Inn.σ} {own : ℕ} {L : List (Q ⊕ G)}
    (hr : Inn.Reaches (Sum.elim (tabs P f0 env) gl) SI b i own L) :
    (nest Sol Inn).WithinFrom (callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P) (Sum.inr (c, env, q))) (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2) (Sum.inr (env, i) : NSt Sol Inn) (own + (L.map (Sum.elim (fun _ => price P TI tq env) wg)).sum) (P.lev c0 * (SC + 1) + SS + SI + 2) b := by
  obtain ⟨hGd, hlev, hsize⟩ := chain_facts hM hG env hC
  have hsz : ∀ i : Inn.σ, size i ≤ SI → size (Sum.inr (env, i) : NSt Sol Inn) ≤ (P.lev c0 * (SC + 1) + SS + SI + 2) := fun i hi => by
    have : env.length * (SC + 1) ≤ P.lev c0 * (SC + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [size_inr, size_prod]; dsimp only; omega
  induction hr with
  | halt h1 h2 => exact wfHalt (M := nest Sol Inn) h1 (hsz _ h2)
  | @step i own L h1 h2 h3 _ ih =>
    have ha : (nest Sol Inn).ask (Sum.inr (env, i) : NSt Sol Inn) = none := by simp [nest, h2]
    exact wfMono (wfStep (M := nest Sol Inn) (s := (Sum.inr (env, i) : NSt Sol Inn)) h1 ha (hsz _ h3) ih) (by omega) le_rfl
  | @query i own L y v h1 h2 h3 h4 _ ih =>
    obtain ⟨r, ho, rfl, hw⟩ := up_ok tq gl wg TS env hC y v h3 (Sum.inr (c, env, q)) (le_refl env.length)
    have ha : (nest Sol Inn).ask (Sum.inr (env, i) : NSt Sol Inn) = some (upQuery env y) := by simp [nest, h2]
    refine wfMono (wfQuery (M := nest Sol Inn) (s := (Sum.inr (env, i) : NSt Sol Inn)) (w := (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2)) h1 ha ho (hsz _ h4) ih) ?_ le_rfl
    rw [hw]; simp only [List.map_cons, List.sum_cons]; omega

/-- `nest Sol Inn` meets the hypothesis of `SelfCallRuns`. -/
theorem nest_within (hM : P.Meets gl wg Sol Inn TS TI SS SI SC) (hG : P.Good c0 f0) (x : NIn Ctx Q) (hx : nGood P c0 f0 x) :
    (nest Sol Inn).Within (callOracle (Sum.elim f0 gl) (nGood P c0 f0) (nval P c0 f0) (ndep P) x) (Sum.elim (Sum.elim (fun _ : Q => tq) wg) fun a' => nT P TS TI tq a' + 2) x (nT P TS TI tq x) (P.lev c0 * (SC + 1) + SS + SI + 2) (nval P c0 f0 x) := by
  rcases x with ⟨env, c⟩ | ⟨c, env, q⟩
  · obtain ⟨hC, rfl⟩ := hx
    obtain ⟨own, L, hr, hc⟩ := hM.sol _ _ (chain_facts hM hG env hC).1 (callCost TS TI (P.lev (parent c0 env)) (price P TI tq env)) (price P TI tq env)
    obtain ⟨own', L', hr', hc'⟩ := sol_sim (tq := tq) hM hG env hC hr
    exact ⟨own', L', hr', hc'.trans (hc.trans (le_of_eq (cost_eq TS TI _ _).symm))⟩
  · obtain ⟨hC, hs⟩ := hx
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨own, L, hr, hc⟩ := hM.inn _ _ c (chain_facts hM hG env hC.1).1 hC.2 q a ha (price P TI tq env)
    obtain ⟨own', L', hr', hc'⟩ := inn_sim (tq := tq) hM hG env hC.1 c q hr
    have hv : nval P c0 f0 (Sum.inr (c, env, q)) = a := by show (P.tab c (tabs P f0 env) q).getD _ = a; rw [ha]; rfl
    rw [hv]
    exact ⟨own', L', hr', hc'.trans hc⟩

/-- The tower has the runs of `selfCall (nest Sol Inn)`. -/
theorem tower_reaches {O : Q ⊕ G → Option A} {S : ℕ} {b : A} {s : (selfCall (nest Sol Inn)).σ} {own : ℕ} {L : List (Q ⊕ G)} (h : (selfCall (nest Sol Inn)).Reaches O S b s own L) :
    (tower Sol Inn).Reaches O S b s own L := by
  induction h with
  | halt h1 h2 => exact .halt h1 h2
  | step h1 h2 h3 _ ih => exact .step h1 h2 h3 ih
  | query h1 h2 h3 h4 _ ih => exact .query h1 h2 h3 h4 ih

/-- The tower returns the value of every well-formed instance, at the cost of the recursion. -/
theorem towerRuns : TowerRuns := by
  intro Ctx Q G A _ P gl wg Sol Inn TS TI SS SI SC hM c f hG tq
  obtain ⟨own, L, hr, hc⟩ := selfCallRuns _ _ _ _ (nest Sol Inn) (Sum.elim f gl) (Sum.elim (fun _ => tq) wg) (nGood P c f) (nval P c f) (ndep P) (nT P TS TI tq)
    (P.lev c * (SC + 1) + SS + SI + 2) (fun x hx => nest_within hM hG x hx) (Sum.inl ([], c)) ⟨trivial, rfl⟩
  exact ⟨own, L, tower_reaches hr, hc⟩

end QueryMachines.Tower
