/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Ceiling
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.InnerProduct
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.OfflineStatement
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Pad
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Preprocessing
public import ThreeSumApsp.Programs.Sec4.ChoosingParameters.Statement
public import ThreeSumApsp.Programs.Sec4.Theorem30.Program

/-!
# Corollaries 26, 31 and 32: the concrete program for given parameters

program31 G = base58 (Theorem 5's and Theorem 30's procedures, numbers 0 to 57) followed by the
procedures 58 to 73 of Section 4.4 (`procs31`): copying, filling, m = ⌈log₄ D⌉, padding and the
inner product; the preprocessing pre31Body G at 64 and the query; their main procedures; the offline
routine and its main procedure; the solver of Corollary 26 for all instances with its test; and the
two procedures for L = ⌈am/b⌉ and t = ⌈pm/q⌉ at 72 and 73. The specifications of the preprocessing,
the query and the offline routine hold for it, for all limits, without hypotheses. At the parameters
of Corollary 26 it is `program26`.

With the two end theorems for light programs and the compiler this gives the two statements about
the word RAM from which Corollaries 26, 31 and 32 follow: on every domain of inputs, and for all
bounds that dominate the two costs of Theorem 30 at the parameters G (`CostsWithin`), the compiled
program is a data structure (`isDataStructure_of_costsWithin`) and solves the offline problem
(`solves_of_costsWithin`).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.WordRam

/-! ## Two procedures for Corollary 26

The program carries them for all parameters G. What they do at the parameters of Corollary 26 is
proved in `regimeTest26_meets` and `allInstances26_solves`. -/

/-- regimeTest26(N, D) returns 1 if D^18 ≤ N and 0 if not. It changes no cell. -/
def regimeTest26Body : Stmt := Sec2.regimePow ;; .set 0 (v 9)

/-- allInstances26(N, D, w, U, x, y, wi, wj, out, fr). Locals 0 to 9 are the arguments, which are
passed on as they are; local 10 is the result of the test. -/
def allInstances26Body : Stmt :=
  .call Proc.regimeTest26 [v 0, v 1] 10 ;;
  .ite (k 0 <' v 10)
    (.call Proc.offline32 [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)
    (.call Sec2.pThinBrute [v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9] 0)

/-! ## The program -/

/-- The bodies of the procedures number 58, 59, …, 73 (61 is not used). -/
def procs31 (G : RatParams) : List Stmt :=
  [copyBody, fillBody, log4Body, .skip, padXBody, ipAtBody, pre31Body G, query31Body,
    preMain31Body, queryMain31Body, offline32Body, offlineMain32Body, allInstances26Body,
    regimeTest26Body, ceilMulBody G.a G.b, ceilMulBody G.p G.q]

/-- The program for the parameters G. -/
def program31 (G : RatParams) : Program := base58 ++ procs31 G

/-- The routines stand at their numbers. -/
theorem program31_at (G : RatParams) (n : ℕ) {body : Stmt} (hn : 58 ≤ n := by norm_num)
    (h : (procs31 G)[n - 58]? = some body := by rfl) : (program31 G)[n]? = some body := by
  rw [program31, List.getElem?_append_right (by rw [length_base58]; exact hn), length_base58]
  exact h

/-- **The preprocessing**, for all limits. -/
theorem pre31_program31 (G : RatParams) : ∀ lim, PreSpec31 lim (program31 G) cShared30 G := by
  intro lim N D₀ aX aY fr X Y U μ hin
  have std := hin.lim.std
  have hcopy : CopySpec lim (program31 G) := copy_ok (program31_at G Proc.copy) std
  have hfill : FillSpec lim (program31 G) := fill_ok (program31_at G Proc.fill) std
  have hlog : Log4Spec lim (program31 G) := log4_meets (program31_at G Proc.log4) std
  have hlev : CeilMulSpec lim (program31 G) Proc.levels31 G.a G.b :=
    ceilMul_meets G.hb (program31_at G Proc.levels31)
  have hswi : CeilMulSpec lim (program31 G) Proc.switch31 G.p G.q :=
    ceilMul_meets G.hq (program31_at G Proc.switch31)
  have hpad : PadXSpec lim (program31 G) := padX_meets (program31_at G Proc.padX) hcopy hfill std
  exact pre31_meets G (program31_at G Proc.pre31)
    ⟨hlog, hlev, hswi, hpad, hcopy, hfill, preCore_base58 _ lim⟩ N D₀ aX aY fr X Y U μ hin

/-- **A query**, for all limits. -/
theorem query31_program31 (G : RatParams) : ∀ lim, QuerySpec31 lim (program31 G) G := by
  intro lim N D₀ aX aY fr X Y U μ I J hin
  have hip : IpAtSpec lim (program31 G) := ipAt_meets (program31_at G Proc.ipAt) hin.lim.std
  exact query31_meets G (program31_at G Proc.query31) (queryAt_base58 _ lim) hip
    N D₀ aX aY fr X Y U μ I J hin

/-- **The offline routine**, for all limits. -/
theorem offline32_program31 (G : RatParams) : ∀ lim, OfflineSpec32 lim (program31 G) cShared30 G :=
  fun lim => offline32_meets (program31_at G Proc.offline32) (pre31_program31 G lim)
    (query31_program31 G lim)

theorem preMain31_program31 (G : RatParams) :
    (program31 G)[Proc.preMain31]? = some preMain31Body :=
  program31_at G Proc.preMain31

theorem queryMain31_program31 (G : RatParams) :
    (program31 G)[Proc.queryMain31]? = some queryMain31Body :=
  program31_at G Proc.queryMain31

theorem offlineMain32_program31 (G : RatParams) :
    (program31 G)[Proc.offlineMain32]? = some offlineMain32Body :=
  program31_at G Proc.offlineMain32

/-! ## The program on the word RAM -/

/-- **The program with the parameters G, compiled, is a data structure** on every domain of inputs
with entries bounded by N^e, for all bounds Tp (preprocessing time and space) and Tq (query time)
that dominate the two costs of Theorem 30. The preprocessing program is compiled with the main
procedure preMain31, the query program with queryMain31; queries are put and answered through the
cells -1, -2 and -3. -/
theorem isDataStructure_of_costsWithin (G : RatParams) {C : ℝ} (hC : 0 ≤ C) (e : ℕ)
    {dom : ThinPair → Prop} {Tp Tq : ThinPair → ℝ}
    (hdom : ∀ x, dom x → x.U = x.N ^ e ∧ CostsWithin G C x.N x.D (Tp x) (Tq x)) :
    ∃ (b : ℕ) (A : ℝ), IsDataStructure (compileProgram (program31 G) Proc.preMain31 false)
        (compileProgram (program31 G) Proc.queryMain31 false) (-1) (-2) (-3) b [] dom
        (fun x => A * Tp x) (fun x => A * Tp x) (fun x => A * Tq x) := by
  obtain ⟨A, s, k, htop⟩ := programIsDataStructure_of_costsWithin (P := program31 G)
    (c0 := cShared30) G hC e dom Tp Tq hdom (preMain31_program31 G) (queryMain31_program31 G)
    (pre31_program31 G) (query31_program31 G)
  exact ⟨_, _, isDataStructure_of_program_scaled htop fun x hx =>
    have hcosts := (hdom x hx).2
    ⟨hcosts.one_le_pre, hcosts.one_le_pre, hcosts.one_le_query⟩⟩

/-- **The program with the parameters G, compiled** with the main procedure offlineMain32,
**computes the wanted entries** in time O(|W| Tq + Tp), on every domain of inputs with entries
bounded by N^e and for all bounds Tp and Tq that dominate the two costs of Theorem 30. -/
theorem solves_of_costsWithin (G : RatParams) {C : ℝ} (hC : 0 ≤ C) (e : ℕ)
    {dom : ThinInstance → Prop} {Tp Tq : ThinInstance → ℝ}
    (hdom : ∀ x, dom x → x.U = x.N ^ e ∧ CostsWithin G C x.N x.D (Tp x) (Tq x)) :
    ∃ (b : ℕ) (A : ℝ),
      WordRam.Solves (thinProduct []) (compileProgram (program31 G) Proc.offlineMain32 false) b dom
        fun x => A * ((x.W.length : ℝ) * Tq x + Tp x) := by
  obtain ⟨A, s, k, htop⟩ := programSolves_of_costsWithin (P := program31 G) (c0 := cShared30) G hC e
    dom Tp Tq hdom (offlineMain32_program31 G) (offline32_program31 G)
  have hsolves := solves_of_programSolves_scaled (r := 2) htop (fun x => le_rfl) fun x hx => by
    have hcosts := (hdom x hx).2
    have hpre := hcosts.one_le_pre
    have hquery := hcosts.one_le_query
    have : (0 : ℝ) ≤ (x.W.length : ℝ) * Tq x := by positivity
    linarith
  exact ⟨_, (timeConst (program31 G) false : ℝ) * (A + 1),
    hsolves.mono le_rfl (fun _ hx => hx) fun x _ => le_of_eq (by ring)⟩

end Light.Sec4
