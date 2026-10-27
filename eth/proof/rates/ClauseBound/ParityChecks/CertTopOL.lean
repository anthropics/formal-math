/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.TopDefs
public import ClauseBound.TopN.Cert
public import ClauseBound.Inst.RecArith

/-! # The function `AO` and its exponent function `eO` are polynomial-time

`stCertO : StCertCountOL → StCertO`. The file parallels proof/rates/ClauseBound/TopN/Cert.lean: the
walk, the decoder, exhaustive counting, the output word and the exponent of the networks under a
bound have their
certificates there and in proof/consequences/CountKSatRate/; the count of one sparse formula has its
certificate as a hypothesis. This file shows that the bounds for the networks of three layers are
given in unary, that the exponent for
everything but the networks is polynomial-time, and that so are the five tests of `planAtO`, by
which it chooses between the networks and trying all assignments. -/

public section

namespace ClauseBound.ParityChecks.CertTopOL

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks

variable {α : Type} [Enc α]

/-! ### Logarithms -/

/-- ⌊log₂ n⌋ is the number of binary digits of n, less one. -/
theorem log_two_eq (n : ℕ) : Nat.log 2 n = Nat.size n - 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h1 : Nat.size n ≤ Nat.log 2 n + 1 := Nat.size_le.2 (Nat.lt_pow_succ_log_self (by norm_num) n)
    have h2 : Nat.log 2 n < Nat.size n := Nat.lt_size.2 (Nat.pow_log_le_self 2 (by omega))
    omega

theorem log_polyT {f : α → ℕ} (hf : PolyT f) : PolyT fun x => Nat.log 2 (f x) := by
  have h : PolyT fun x => Nat.size (f x) - 1 := by fun_prop
  exact h.congr fun x => (log_two_eq _).symm

theorem clog_polyT {f : α → ℕ} (hf : PolyT f) : PolyT fun x => Nat.clog 2 (f x) := by
  have h : PolyT fun x => Nat.size (f x - 1) := by fun_prop
  exact h.congr fun x => (ClauseBound.Inst.Rec.clog_two_eq _).symm

theorem clog_le_self (n : ℕ) : Nat.clog 2 n ≤ n := by
  rw [ClauseBound.Inst.Rec.clog_two_eq]
  exact (Nat.size_le.2 Nat.lt_two_pow_self).trans (Nat.sub_le _ _)

theorem clog_unary {f : α → ℕ} (hf : Unary f) : Unary fun x => Nat.clog 2 (f x) :=
  hf.of_le (clog_polyT hf.poly) fun _ => clog_le_self _

theorem max_unary {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary fun x => max (f x) (g x) :=
  (hf.add hg).of_le (PolyT.max' hf.poly hg.poly) fun _ => max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)

/-! ### The parameters of the networks of three layers -/

section par
variable {K n s D : α → ℕ}

theorem LD_polyT (hD : PolyT D) : PolyT fun x => LD (D x) := by
  unfold LD
  exact clog_polyT ((PolyT.const 2).mul hD)

theorem LD_unary (hD : Unary D) : Unary fun x => LD (D x) := by
  unfold LD
  exact clog_unary ((Unary.const 2).mul hD)

theorem blkOL_unary (hD : Unary D) : Unary fun x => blkOL (D x) := by
  have h := LD_unary hD
  unfold blkOL
  exact ((((Unary.const 2).mul hD).add (((Unary.const 16).mul hD).mul h)).add (Unary.const 1))

theorem bitOL_unary (hD : Unary D) : Unary fun x => bitOL (D x) := by
  unfold bitOL
  exact clog_unary (blkOL_unary hD)

theorem colMax_unary (hn : Unary n) (hD : Unary D) : Unary fun x => colMax (n x) (D x) := by
  unfold colMax
  exact ((clog_unary (((Unary.const 16).mul hD).mul hn)).add ((Unary.const 18).mul (LD_unary hD))).add (Unary.const 2)

theorem rowMax_unary (hn : Unary n) (hD : Unary D) : Unary fun x => rowMax (n x) (D x) := by
  unfold rowMax
  exact ((clog_unary ((Unary.const 96).mul hn)).add (((Unary.const 3).mul hD).mul (LD_unary hD))).add (Unary.const 2)

theorem occOL_unary (hn : Unary n) (hD : Unary D) : Unary fun x => occOL (n x) (D x) := by
  unfold occOL
  exact max_unary (hD.mul ((Unary.const 2).add (colMax_unary hn hD))) (rowMax_unary hn hD)

/-- The bound on the shared bits is given in unary. -/
theorem UbOL_unary (k : ℕ) (hK : Unary K) (hn : Unary n) (hD : Unary D) : Unary fun x => UbOL k (K x) (n x) (D x) := by
  have h1 := bitOL_unary hD
  unfold UbOL Ub; fun_prop

/-- The bound on the size is given in unary. -/
theorem PbOL_unary (hK : Unary K) (hn : Unary n) (hD : Unary D) : Unary fun x => PbOL (K x) (n x) (D x) := by
  have h1 := bitOL_unary hD
  have h2 := occOL_unary hn hD
  have hK' : PolyT K := hK.poly
  unfold PbOL Pb Mark.qv; fun_prop

/-- The formula of the exponent for everything but the networks, for any polynomial-time numbers. -/
theorem restO_aux (k : ℕ) {Z₁ Z₂ B z q : α → ℕ} (hK : PolyT K) (h1 : PolyT Z₁) (h2 : PolyT Z₂) (hB : PolyT B) (hz : PolyT z) (hn : PolyT n) (hq : PolyT q) :
    PolyT fun x => 3 * K x ^ 8 * (3 * K x ^ 8) * 3 * Z₁ x + (3 * Z₂ x + 3 * z x + 12) + (n x / q x + 2) + (B x + 5 * k + 10 + (k + 3) * z x) := by
  have h8 : PolyT fun x => 3 * K x ^ 8 := (PolyT.const 3).mul (hK.pow_const 8)
  exact (((((h8.mul h8).mul (PolyT.const 3)).mul h1).add ((((PolyT.const 3).mul h2).add ((PolyT.const 3).mul hz)).add (PolyT.const 12))).add
    ((PolyT.div hn hq).add (PolyT.const 2))).add (((hB.add (PolyT.const (5 * k))).add (PolyT.const 10)).add ((PolyT.const (k + 3)).mul hz))

/-- The exponent for everything but the networks is polynomial-time. -/
theorem restO_polyT (k : ℕ) (hK : Unary K) (hn : Unary n) (hs : Unary s) : PolyT fun x => restO k (K x) (n x) (s x) := by
  have hD := blockN_unary k hn hs
  have hn' := hn.poly
  unfold restO
  exact restO_aux k hK.poly (PolyT.size' ((blkOL_unary hD).poly.mul (((PolyT.const 7).mul hn').add (PolyT.const 1)))) (PolyT.size' (hD.poly.mul hn'))
    (betaN_unary k hs).poly (PolyT.size' hn') hn' (pow_polyT (PolyT.const 2) hs)

end par

/-- A case distinction on five tests, for tests that are not looked into. -/
theorem ite_five {β : Type} [Enc β] {p₁ p₂ p₃ p₄ p₅ : α → Prop} [DecidablePred p₁] [DecidablePred p₂] [DecidablePred p₃] [DecidablePred p₄] [DecidablePred p₅]
    {u v : α → β} (h1 : PolyT fun x => decide (p₁ x)) (h2 : PolyT fun x => decide (p₂ x)) (h3 : PolyT fun x => decide (p₃ x)) (h4 : PolyT fun x => decide (p₄ x))
    (h5 : PolyT fun x => decide (p₅ x)) (hu : PolyT u) (hv : PolyT v) : PolyT fun x => if p₁ x ∧ p₂ x ∧ p₃ x ∧ p₄ x ∧ p₅ x then u x else v x :=
  PolyT.ite' (PolyT.decide_and h1 (PolyT.decide_and h2 (PolyT.decide_and h3 (PolyT.decide_and h4 h5)))) hu hv

/-! ### The function and its exponent -/

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-- The plan, jointly in n and s in unary and the index. -/
theorem planAtO_polyT (hP : S.Poly) (c n₀ k : ℕ) {n s : α → ℕ} {i : α → Idx} (hn : Unary n) (hi : PolyT i) (hs : Unary s) :
    PolyT fun x => planAtO S c n₀ k (n x) (i x) (s x) := by
  have hK : Unary fun x => S.K (i x) := hP.K.comp hi
  have hD := blockN_unary k hn hs
  have hU := UbOL_unary k hK hn hD
  have hQ := PbOL_unary hK hn hD
  have hr := restO_polyT k hK hn hs
  have hnet := needNetC_polyT S hP (b := fun x => List.replicate (n x) ()) hn hi hU hQ
  have hn' : PolyT n := hn.poly
  have hs' : PolyT s := hs.poly
  have hpow : PolyT fun x => 2 ^ betaN k (s x) := pow_polyT (PolyT.const 2) (betaN_unary k hs)
  have hc1 : PolyT fun x => decide (s0K k ≤ s x) := PolyT.decide_le (PolyT.const _) hs'
  have hc2 : PolyT fun x => decide (2 ^ betaN k (s x) ≤ n x + 1) := PolyT.decide_le hpow (PolyT.add hn' (PolyT.const 1))
  have hc3 : PolyT fun x => decide (n₀ ≤ n x) := PolyT.decide_le (PolyT.const _) hn'
  have hc4 : PolyT fun x => decide (2 ^ betaN k (s x) ≤ (Nat.log 2 (n x) + 1) ^ c) :=
    PolyT.decide_le hpow (((log_polyT hn').add (PolyT.const 1)).pow_const c)
  have hc5 : PolyT fun x => decide (2 * LD (2 ^ betaN k (s x)) ≤ n x) := PolyT.decide_le ((PolyT.const 2).mul (LD_polyT hpow)) hn'
  have hsum : PolyT fun q : α × ℕ => q.2 + restO k (S.K (i q.1)) (n q.1) (s q.1) :=
    PolyT.add PolyT.id'.snd (PolyT.comp (f := fun x => restO k (S.K (i x)) (n x) (s x)) hr PolyT.id'.fst)
  have hn2 : PolyT fun q : α × ℕ => n q.1 := PolyT.comp (f := n) hn' PolyT.id'.fst
  have hin : PolyT fun x => (needNetC S (List.replicate (n x) ()) (i x) (UbOL k (S.K (i x)) (n x) (blockN k (n x) (s x))) (PbOL (S.K (i x)) (n x) (blockN k (n x) (s x))) 0).bind fun v =>
      if v + restO k (S.K (i x)) (n x) (s x) ≤ n x then some (v + restO k (S.K (i x)) (n x) (s x)) else none :=
    PolyT.optionBind (PolyT.ite' (PolyT.decide_le hsum hn2) (PolyT.some' hsum) (PolyT.const none)) hnet
  unfold planAtO
  exact ite_five hc1 hc2 hc3 hc4 hc5 hin (PolyT.const none)

end

/-- The function of (input, pad) and the exponent function of the input are polynomial-time. -/
theorem stCertO (hC : StCertCountOL) : StCertO := by
  intro Idx _ S hP c n₀ k pick slU hpick hsl
  have hd0 : PolyT (decU k) := stCertDecU k
  have hn0 : Unary (nK k) := Unary.of_length hd0.fst
  have hlv0 : PolyT fun x : List Bool => pick (root17 (nK k x)) := PolyT.comp hpick (root17_polyT hn0)
  have hi0 : PolyT (idxN k pick) := hlv0.snd
  have hs0 : Unary (precN k pick slU) := Unary.of_length (PolyT.comp hsl hlv0.fst)
  have hpl : PolyT (planO S c n₀ k pick slU) := planAtO_polyT S hP c n₀ k hn0 hi0 hs0
  constructor
  · have hd := decU_pad_polyT k
    have hn := nK_unary k
    have hp : PolyT fun p : List Bool × U => p.2 := by fun_prop
    have hs : Unary fun p : List Bool × U => precN k pick slU p.1 := hs0.comp PolyT.id'.fst
    have hl := leafM_polyT
    have hn1 : Unary fun q : (List Bool × U) × CNode => nK k q.1.1 := hn.comp (h := fun q : (List Bool × U) × CNode => q.1) (by fun_prop)
    have hs1 : Unary fun q : (List Bool × U) × CNode => precN k pick slU q.1.1 := hs.comp (h := fun q : (List Bool × U) × CNode => q.1) (by fun_prop)
    have hD1 := blockN_unary k hn1 hs1
    have hi1 : PolyT fun q : (List Bool × U) × CNode => idxN k pick q.1.1 := PolyT.comp (g := fun q : (List Bool × U) × CNode => q.1.1) hi0 (by fun_prop)
    have hv : PolyT fun q : (List Bool × U) × CNode => valO S k q.1.2 (idxN k pick q.1.1) (nK k q.1.1) (precN k pick slU q.1.1) q.2 := by
      have hg : PolyT fun q : (List Bool × U) × CNode => (q.1.2, idxN k pick q.1.1,
          (List.replicate (nK k q.1.1) (), List.replicate (blockN k (nK k q.1.1) (precN k pick slU q.1.1)) ()), leafM q.2) :=
        PolyT.prodMk (by fun_prop) (PolyT.prodMk hi1 (PolyT.prodMk (PolyT.prodMk hn1 hD1) (by fun_prop)))
      refine (PolyT.comp (hC Idx S hP k) hg).congr fun q => ?_
      simp only [List.length_replicate]
      rfl
    have hnum : PolyT fun p : List Bool × U => numOL S k (idxN k pick p.1) (precN k pick slU p.1) p := by
      have h := numC_polyT_aux stCertWalkS k (d := fun p : List Bool × U => decU k p.1) (pad := fun p => p.2)
        (τ := fun p => tauOf (precN k pick slU p.1)) (val := fun p => valO S k p.2 (idxN k pick p.1) (nK k p.1) (precN k pick slU p.1)) hd hp (tauOf_polyT hs) hv
      unfold numOL
      exact h
    have hno : PolyT fun p : List Bool × U => (planO S c n₀ k pick slU p.1).isNone := PolyT.optionIsNone (PolyT.comp hpl PolyT.id'.fst)
    unfold AO
    exact PolyT.comp outW_polyT (PolyT.prodMk hd (PolyT.cond' hno (bruteN_polyT k) hnum))
  · unfold eO
    exact PolyT.optionGetD hpl hn0.poly

end ClauseBound.ParityChecks.CertTopOL
