/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import RecursionToBound.Cert.Thresholds
import VariableBound.Cert.Top
import VariableBound.Net.CertEv
import UniformInK.Cert.Top
import ClauseBound.TopN.Cert
import ClauseBound.Alg.Decode
import PaddedDescent.F.CertEval
import ToTuring.Poly.NetFun

/-! # The exponent of the padding string is polynomial-time

`expo_polyT`: for every polynomial-time solver S, every n₁ and all polynomial-time `pick` and `num`,
the exponent `expo S n₁ pick num` of the function of Theorem D (a) along the printed Step 5
(proof/variables/RecursionToBound/Defs.lean) is polynomial-time in the input, **on all inputs**. The
file goes through the definitions in their order.

* `needWalk_polyT`: the exponent for the walk. ⌈ε·n⌉ is computed without fractions
  (`ceil_epsOf_mul`). The bound on the length of the stack has the factors (32α)^(2k), 2^k and
  (n+2)^(k+1): with k in unary these numbers have polynomially many binary digits, and only their
  number of digits enters the exponent.
* `needAtC_polyT`: the exponent for one Δ, for k, n and Δ in unary; from the certificates of the
  bounds U, P, B of Step 3 (proof/variables/VariableBound/Net/CertEv.lean), of the exponent of the
  networks (`VariableBound.CertTop.needNetC_polyT`) and of the number of profiles
  (`PaddedDescent.F.CertEval.nProf_polyT`).
* `deltas_polyT`: the list of the numbers Δ. It is cut off at n + 1, so its length is given in
  unary.
* `needOutputsC_polyT`: the maximum over Δ. The fold of the definition is rewritten as: `none` if
  one of the numbers is `none`, and otherwise the maximum of the list (`foldr_bind_max`). In the
  list, Δ is replaced by min(Δ, n + 1), which is given in unary; on the members of the list the two
  agree.
* `planAt_polyT`, `plan_polyT`, `expo_polyT`: the plan and the exponent. The width read from the
  input is at most 3 plus the number of literals written in the formula, so it is given in unary
  (`widthU_unary`); K at the index picked is given in unary because the solver is polynomial-time
  (`ClauseBound.Alg.Solver.Poly.K`), so `num` gets an argument of polynomial length (`numU_polyT`). -/

public section

namespace RecursionToBound

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.CertEval CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks UniformInK UniformInK.CertTop VariableBound VariableBound.Net VariableBound.Net.CertEv VariableBound.CertTop SparsificationLemma

variable {α : Type} [Enc α]

/-! ### The walk -/

/-- The formula of the bound on the length of the walk's state is polynomial-time when every number
in it is. -/
theorem stackLen_aux {b p m k n : α → ℕ} (hb : PolyT b) (hp : PolyT p) (hm : PolyT m) (hk : PolyT k) (hn : PolyT n) :
    PolyT fun x => (b x * n x + 1) * (p x * m x * (k x * (3 * n x + 5) + 10) + 2 * n x * (2 * (3 * n x + 5) + 10) + 8) + 3 * n x + 16 := by
  have h35 : PolyT fun x => 3 * n x + 5 := ((PolyT.const 3).mul hn).add (PolyT.const 5)
  exact ((((hb.mul hn).add (PolyT.const 1)).mul
    ((((hp.mul hm).mul ((hk.mul h35).add (PolyT.const 10))).add (((PolyT.const 2).mul hn).mul (((PolyT.const 2).mul h35).add (PolyT.const 10)))).add (PolyT.const 8))).add
      ((PolyT.const 3).mul hn)).add (PolyT.const 16)

/-- The bound on the length of the walk's state is polynomial-time jointly in k, τ and n, if k is
given in unary. -/
theorem stackLen_polyT {k τ n : α → ℕ} (hk : Unary k) (hτ : PolyT τ) (hn : PolyT n) : PolyT fun x => stackLenCU (k x) (τ x) (n x) (inLen (k x) (n x)) := by
  have hk' := hk.poly
  have hb : PolyT fun x => τ x ^ (2 * k x) := PolyT.pow_unary hτ ((Unary.const 2).mul hk)
  have hp : PolyT fun x => 2 ^ k x := PolyT.two_pow hk
  have hm : PolyT fun x => (k x * 2 ^ k x + 1) * (n x + 2) ^ (k x + 1) :=
    ((hk'.mul hp).add (PolyT.const 1)).mul (PolyT.pow_unary (hn.add (PolyT.const 2)) (hk.add (Unary.const 1)))
  unfold stackLenCU bsumU inLen
  exact stackLen_aux hb hp hm hk' hn

/-- The exponent for the walk is polynomial-time jointly in k, r and n, if k is given in unary. -/
theorem needWalk_polyT {k n : α → ℕ} {r : α → ℕ × ℕ} (hk : Unary k) (hr : PolyT r) (hn : PolyT n) : PolyT fun x => needWalk (k x) (r x) (n x) := by
  have h1 : PolyT fun x => ceilDiv (min (r x).1 (r x).2 * n x) (r x).2 := ceilDiv_polyT (by fun_prop) (by fun_prop)
  have h2 := stackLen_polyT hk ((PolyT.const 32).mul (alphaC_polyT hk.poly hr)) hn
  have h : PolyT fun x => (ceilDiv (min (r x).1 (r x).2 * n x) (r x).2 + 2) + Nat.size (stackLenCU (k x) (32 * Cal.alphaC (k x) (epsOf (r x))) (n x) (inLen (k x) (n x))) :=
    (h1.add (PolyT.const 2)).add (PolyT.size' h2)
  exact h.congr fun x => by rw [needWalk, ceil_epsOf_mul]

/-! ### One Δ -/

/-- Adding two polynomial-time functions of the first component to the second component is
polynomial-time. -/
theorem add_two_polyT {A B : α → ℕ} (hA : PolyT A) (hB : PolyT B) : PolyT fun q : α × ℕ => q.2 + A q.1 + B q.1 := by
  fun_prop

/-- Adding two polynomial-time numbers to a number that may be missing is polynomial-time. -/
theorem optionMap_add_two {o : α → Option ℕ} {A B : α → ℕ} (ho : PolyT o) (hA : PolyT A) (hB : PolyT B) : PolyT fun x => (o x).map fun v => v + A x + B x :=
  PolyT.optionMap (f := fun x v => v + A x + B x) (add_two_polyT hA hB) ho

/-- The bound on the number of profiles is polynomial-time if K, n and Δ are given in unary. -/
theorem nPrMax_polyT {K n Δ : α → ℕ} (hK : Unary K) (hn : Unary n) (hΔ : Unary Δ) : PolyT fun x => nPrMax (K x) (n x) (Δ x) := by
  unfold nPrMax
  exact nProf_polyT (by fun_prop) (objMax_unary hn hΔ).poly (Unary.const 2)

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-- The exponent for one Δ, computed under a bound, is polynomial-time if the solver, the bound and
the index are and k, n and Δ are given in unary. -/
theorem needAtC_polyT (hP : S.Poly) {b : α → U} {k n Δ : α → ℕ} {i : α → Idx} (hb : PolyT b) (hk : Unary k) (hi : PolyT i) (hn : Unary n) (hΔ : Unary Δ) :
    PolyT fun x => needAtC S (b x) (k x) (i x) (n x) (Δ x) := by
  have hK : Unary fun x => S.K (i x) := hP.K.comp hi
  have hnet := needNetC_polyT S hP hb hi (UbD_unary hk hK hn hΔ) (PbD_unary hK hn hΔ) (BbD_unary hk hn)
  have hA : PolyT fun x => Nat.size (nPrMax (S.K (i x)) (n x) (Δ x)) := PolyT.size' (nPrMax_polyT hK hn hΔ)
  have hn' := hn.poly
  have hB : PolyT fun x => Nat.size (8 * (10 * n x + 1) * (sbMax (Δ x) + 1) * (Nat.size (Δ x * n x) + 2) + 8) :=
    PolyT.size' (((((PolyT.const 8).mul (((PolyT.const 10).mul hn').add (PolyT.const 1))).mul ((sbMax_unary hΔ).poly.add (PolyT.const 1))).mul
      ((PolyT.size' (hΔ.poly.mul hn')).add (PolyT.const 2))).add (PolyT.const 8))
  have h := optionMap_add_two hnet hA hB
  unfold needAtC
  exact h

end

/-! ### All Δ -/

/-- The numbers Δ of the list are at least 2, at most n + 1 and at most the bound on the
occurrences. -/
theorem mem_deltas {k n Δ : ℕ} {r : ℕ × ℕ} (h : Δ ∈ deltas k r n) : 2 ≤ Δ ∧ Δ ≤ n + 1 ∧ Δ ≤ occBound k r := by
  unfold deltas at h
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 h
  have := List.mem_range.1 hj
  omega

/-- The list of the numbers Δ is polynomial-time jointly in k, r and n, if k and n are given in
unary. -/
theorem deltas_polyT {k n : α → ℕ} {r : α → ℕ × ℕ} (hk : Unary k) (hr : PolyT r) (hn : Unary n) : PolyT fun x => deltas (k x) (r x) (n x) := by
  have ho := occBound_polyT hk hr
  have hu : Unary fun x => min (occBound (k x) (r x)) (n x + 1) - 1 :=
    (hn.add (Unary.const 1)).of_le ((PolyT.min' ho (hn.poly.add (PolyT.const 1))).sub (PolyT.const 1)) fun x => by omega
  unfold deltas
  exact PolyT.map (f := fun _ j => j + 2) (by fun_prop) (PolyT.range hu)

/-- The fold of `needOutputsC`, as a function of the list of the numbers that may be missing. -/
theorem foldr_bind_max_map (f : ℕ → Option ℕ) (l : List ℕ) :
    l.foldr (fun a o => o.bind fun v => (f a).map (max v)) (some 0) =
      if (l.map f).all (fun o => o.isSome) then some (((l.map f).map fun o => o.getD 0).foldr max 0) else none := by
  simp only [foldr_bind_max, List.all_map, List.map_map, Function.comp_def]

/-- The function whose value is `none` if one of the numbers is `none`, and otherwise the maximum of
the list, is polynomial-time. -/
theorem maxOfOptions_polyT {l : α → List (Option ℕ)} (hl : PolyT l) :
    PolyT fun x => if (l x).all (fun o => o.isSome) then some (((l x).map fun o => o.getD 0).foldr max 0) else none := by
  have h1 : PolyT fun x => ((l x).map fun o => o.getD 0).foldr max 0 := NetE.foldr_max_polyT (by fun_prop)
  fun_prop

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-- The maximum over Δ, computed under a bound, is polynomial-time if the solver, the bound, r and
the index are and k and n are given in unary. -/
theorem needOutputsC_polyT (hP : S.Poly) {b : α → U} {k n : α → ℕ} {r : α → ℕ × ℕ} {i : α → Idx} (hb : PolyT b) (hk : Unary k) (hr : PolyT r) (hi : PolyT i) (hn : Unary n) :
    PolyT fun x => needOutputsC S (b x) (k x) (r x) (i x) (n x) := by
  have hd := deltas_polyT hk hr hn
  have hn' := hn.poly
  have hat : PolyT fun p : α × ℕ => needAtC S (b p.1) (k p.1) (i p.1) (n p.1) (min p.2 (n p.1 + 1)) :=
    needAtC_polyT S hP (by fun_prop) (hk.comp (h := fun p : α × ℕ => p.1) PolyT.id'.fst) (by fun_prop) (hn.comp (h := fun p : α × ℕ => p.1) PolyT.id'.fst)
      (((hn.comp (h := fun p : α × ℕ => p.1) PolyT.id'.fst).add (Unary.const 1)).of_le (by fun_prop) fun p => Nat.min_le_right _ _)
  have hl : PolyT fun x => (deltas (k x) (r x) (n x)).map fun Δ => needAtC S (b x) (k x) (i x) (n x) Δ :=
    (PolyT.map (f := fun x Δ => needAtC S (b x) (k x) (i x) (n x) (min Δ (n x + 1))) hat hd).congr fun x =>
      List.map_congr_left fun Δ hΔ => by rw [Nat.min_eq_left (mem_deltas hΔ).2.1]
  exact (maxOfOptions_polyT hl).congr fun x => by rw [needOutputsC, foldr_bind_max_map]

/-! ### The plan and the exponent -/

/-- The plan is polynomial-time if the solver, the index and r are and k and n are given in unary. -/
theorem planAt_polyT (hP : S.Poly) (n₁ : ℕ) {k n : α → ℕ} {i : α → Idx} {r : α → ℕ × ℕ} (hk : Unary k) (hn : Unary n) (hi : PolyT i) (hr : PolyT r) :
    PolyT fun x => planAt S n₁ (k x) (n x) (i x) (r x) := by
  have hn' := hn.poly
  have hout := needOutputsC_polyT S hP (b := fun x => List.replicate (n x) ()) hn hk hr hi hn
  have hw := needWalk_polyT hk hr hn'
  have hsum : PolyT fun q : α × ℕ => q.2 + needWalk (k q.1) (r q.1) (n q.1) :=
    PolyT.add PolyT.id'.snd (PolyT.comp (f := fun x => needWalk (k x) (r x) (n x)) hw PolyT.id'.fst)
  have hn2 : PolyT fun q : α × ℕ => n q.1 := PolyT.comp (f := n) hn' PolyT.id'.fst
  unfold planAt
  exact PolyT.ite' (PolyT.decide_le (PolyT.const n₁) hn')
    (PolyT.optionBind (PolyT.ite' (PolyT.decide_le hsum hn2) (PolyT.some' hsum) (PolyT.const none)) hout) (PolyT.const none)

end

/-- The largest number of literals in a clause is at most the number of all literals written in the
formula. -/
theorem foldr_max_length_le (ψ : Fml) : (ψ.map List.length).foldr max 0 ≤ (ψ.flatMap fun C => C).length := by
  induction ψ with
  | nil => exact le_rfl
  | cons C ψ ih =>
    simp only [List.map_cons, List.foldr_cons, List.flatMap_cons, List.length_append] at ih ⊢
    omega

/-- The width of Step 5 is polynomial-time with its value written in unary. -/
theorem widthOr3F_unary {ψ : α → Fml} (hψ : PolyT ψ) : Unary fun x => widthOr3F (ψ x) :=
  Unary.of_le (g := fun x => ((ψ x).flatMap fun C => C).length + 3) ((Unary.of_length (by fun_prop)).add (Unary.const 3))
    ((PolyT.max' (PolyT.const 3) (NetE.foldr_max_polyT (l := fun x => (ψ x).map List.length) (by fun_prop))).congr fun x => (widthOr3F_eq (ψ x)).symm)
    fun x => by
      have := foldr_max_length_le (ψ x)
      rw [widthOr3F_eq]
      omega

/-- The width read from the input is given in unary. -/
theorem widthU_unary : Unary widthU := widthOr3F_unary Decode.stCertDecM.2.snd

/-- The number of variables read from the input is given in unary. -/
theorem nU_unary : Unary nU := Unary.of_length Decode.stCertDecM.2.fst

/-- The width read from the input, cut off at ⌊log₂(n+1)⌋, is given in unary. -/
theorem widthCut_unary : Unary fun x : List Bool => kcU (widthU x) (nU x) := kcU_unary widthU_unary nU_unary.poly

/-- 2 to the width cut off is given in unary. -/
theorem powWidthCut_unary : Unary fun x : List Bool => 2 ^ kcU (widthU x) (nU x) := powKcU_unary widthU_unary nU_unary

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-- The level picked for n and its index are polynomial-time in the input. -/
theorem level_polyT {pick : U → U × Idx} (hpick : PolyT pick) : PolyT fun x : List Bool => pick (root17 (nU x)) :=
  PolyT.comp hpick (root17_polyT nU_unary)

/-- The index picked for n is polynomial-time in the input. -/
theorem idxU_polyT {pick : U → U × Idx} (hpick : PolyT pick) : PolyT (idxU pick) := (level_polyT hpick).snd

/-- The number in [e, 2e] for the level picked is polynomial-time in the input: its argument is (ℓ,
K_ℓ) in unary, and K is given in unary for a polynomial-time solver. -/
theorem numU_polyT (hP : S.Poly) {pick : U → U × Idx} {num : U × U → ℕ × ℕ} (hpick : PolyT pick) (hnum : PolyT num) : PolyT (numU S pick num) := by
  unfold numU
  exact PolyT.comp hnum (PolyT.prodMk (level_polyT hpick).fst (hP.K.comp (idxU_polyT hpick)))

/-- The plan is polynomial-time in the input. -/
theorem plan_polyT (hP : S.Poly) (n₁ : ℕ) {pick : U → U × Idx} {num : U × U → ℕ × ℕ} (hpick : PolyT pick) (hnum : PolyT num) : PolyT (plan S n₁ pick num) :=
  planAt_polyT S hP n₁ widthCut_unary nU_unary (idxU_polyT hpick) (numU_polyT S hP hpick hnum)

/-- The exponent of the padding string is polynomial-time in the input. -/
theorem expo_polyT (hP : S.Poly) (n₁ : ℕ) {pick : U → U × Idx} {num : U × U → ℕ × ℕ} (hpick : PolyT pick) (hnum : PolyT num) : PolyT (expo S n₁ pick num) := by
  unfold expo
  exact PolyT.optionGetD (plan_polyT S hP n₁ hpick hnum) nU_unary.poly

end

end RecursionToBound
