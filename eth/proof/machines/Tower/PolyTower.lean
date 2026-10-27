/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Tower.Poly

/-! # Certificates of polynomial-time steps for `nest Sol Inn` and for the tower

The states of `nest Sol Inn` are pairs of a list of contexts and a state of the solver or of the
procedure; the five functions of `nest` call those of `Sol` and `Inn` once and move the list. The
tower has the states, step, result, query
and resumption of `selfCall (nest Sol Inn)`, so its certificate is that of `Poly.lean` with another
start. -/

@[expose] public section

namespace QueryMachines.Tower

open Groundwork Groundwork.PolyT QueryMachines.QueryMachine

variable {Ctx Q G A : Type} [HasSize Ctx] [Enc Ctx] [Enc Q] [Enc G] [Enc A]

omit [HasSize Ctx] in
/-- Where a query goes is computed in polynomial time from the list and the query. -/
@[fun_prop] theorem upQuery_poly {γ : Type} [Enc γ] {e : γ → List Ctx} {x : γ → Q ⊕ G} (he : PolyT e) (hx : PolyT x) :
    PolyT fun z => upQuery (e z) (x z) := by
  refine (by fun_prop : PolyT fun z => (x z).elim
    (fun q => (e z).head?.elim (Sum.inl (Sum.inl q) : (Q ⊕ G) ⊕ NIn Ctx Q) fun c => Sum.inr (Sum.inr (c, (e z).tail, q)))
    fun g => Sum.inl (Sum.inr g)).congr fun z => ?_
  rcases x z with q | g
  · rcases e z with _ | ⟨c, env⟩ <;> rfl
  · rfl

variable (Sol : QueryMachine (Ctx ⊕ (Q ⊕ G)) A Ctx A) (Inn : QueryMachine (Q ⊕ G) A (Ctx × Q) A) [IsPolyQ Sol] [IsPolyQ Inn]

/-- The start of `nest Sol Inn`. -/
theorem nest_init_poly : PolyT (β := (List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ)) (fun x : NIn Ctx Q => (nest Sol Inn).init x) := by
  have h1 := IsPolyQ.init (M := Sol); have h2 := IsPolyQ.init (M := Inn)
  exact (by fun_prop : PolyT fun x : NIn Ctx Q => x.elim (fun p => (Sum.inl (p.1, Sol.init p.2) : (List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ)))
    fun p => Sum.inr (p.2.1, Inn.init (p.1, p.2.2))).congr fun x => by rcases x with ⟨env, c⟩ | ⟨c, env, q⟩ <;> rfl

/-- Its step. -/
theorem nest_step_poly : PolyT (β := (List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ)) (fun s : (List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ) => (nest Sol Inn).step s) := by
  have h1 := IsPolyQ.step (M := Sol); have h2 := IsPolyQ.step (M := Inn)
  exact (by fun_prop : PolyT fun s : (List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ) => s.elim (fun p => (Sum.inl (p.1, Sol.step p.2) : (List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ)))
    fun p => Sum.inr (p.1, Inn.step p.2)).congr fun s => by rcases s with ⟨env, s⟩ | ⟨env, i⟩ <;> rfl

/-- Its result. -/
theorem nest_out_poly : PolyT (fun s : (List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ) => (nest Sol Inn).out s) := by
  have h1 := IsPolyQ.out (M := Sol); have h2 := IsPolyQ.out (M := Inn)
  exact (by fun_prop : PolyT fun s : (List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ) => s.elim (fun p => Sol.out p.2) fun p => Inn.out p.2).congr
    fun s => by rcases s with ⟨env, s⟩ | ⟨env, i⟩ <;> rfl

/-- Its query. -/
theorem nest_ask_poly : PolyT (fun s : (List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ) => (nest Sol Inn).ask s) := by
  have h1 := IsPolyQ.ask (M := Sol); have h2 := IsPolyQ.ask (M := Inn)
  refine (by fun_prop : PolyT fun s : (List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ) => s.elim
    (fun p => (Sol.ask p.2).elim (none : Option ((Q ⊕ G) ⊕ NIn Ctx Q)) fun y => y.elim (fun c' => some (Sum.inr (Sum.inl (c' :: p.1, c')))) fun x => some (upQuery p.1 x))
    fun p => (Inn.ask p.2).map (upQuery p.1)).congr fun s => ?_
  rcases s with ⟨env, s⟩ | ⟨env, i⟩
  · simp only [nest, Sum.elim_inl]
    rcases Sol.ask s with _ | (c' | x) <;> rfl
  · rfl

/-- How it goes on with an answer. -/
theorem nest_resume_poly : PolyT (β := (List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ)) (fun p : ((List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ)) × (A ⊕ A) => (nest Sol Inn).resume p.1 p.2) := by
  have h1 := IsPolyQ.resume (M := Sol); have h2 := IsPolyQ.resume (M := Inn)
  exact (by fun_prop : PolyT fun p : ((List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ)) × (A ⊕ A) => p.1.elim
    (fun s => (Sum.inl (s.1, Sol.resume s.2 (p.2.elim id id)) : (List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ)))
    fun s => Sum.inr (s.1, Inn.resume s.2 (p.2.elim id id))).congr fun p => by rcases p with ⟨⟨env, s⟩ | ⟨env, i⟩, r⟩ <;> rfl

variable [Carried Ctx]

/-- The certificate of `nest Sol Inn`. -/
@[instance_reducible] def nestIsPoly : IsPolyQ (nest Sol Inn) where
  enc := (inferInstance : Enc ((List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ)))
  carried := (inferInstance : Carried ((List Ctx × Sol.σ) ⊕ (List Ctx × Inn.σ)))
  init := nest_init_poly Sol Inn
  step := nest_step_poly Sol Inn
  out := nest_out_poly Sol Inn
  ask := nest_ask_poly Sol Inn
  resume := nest_resume_poly Sol Inn

/-- The certificate of the tower. -/
@[instance_reducible] def towerIsPoly : IsPolyQ (tower Sol Inn) :=
  letI := nestIsPoly Sol Inn
  { enc := (inferInstance : Enc (List (nest Sol Inn).σ))
    carried := (inferInstance : Carried (List (nest Sol Inn).σ))
    init := by
      have h1 := IsPolyQ.init (M := nest Sol Inn)
      exact PolyT.cons' (PolyT.comp h1 (by fun_prop : PolyT fun c : Ctx => (Sum.inl ([], c) : NIn Ctx Q))) (PolyT.const [])
    step := rstep_poly (nest Sol Inn)
    out := rout_poly (nest Sol Inn)
    ask := rask_poly (nest Sol Inn)
    resume := rresume_poly (nest Sol Inn) }

/-- The tower has polynomial-time steps, once and for all depths, if the solver and the procedure
have. -/
theorem towerPoly : TowerPoly := fun _ _ _ _ _ _ _ _ _ _ Sol Inn ⟨hS⟩ ⟨hI⟩ => ⟨@towerIsPoly _ _ _ _ _ _ _ _ _ Sol Inn hS hI _⟩

end QueryMachines.Tower
