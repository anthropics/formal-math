/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Count.Defs
public import PaddedDescent.F.FuelCert

/-! # One sparse formula counted as in Steps 1 to 4 of Appendix D: the certificate

Proves `VariableBound.StCertCountD`: the program `countD` is polynomial-time (`PolyT`) in the pad,
jointly in the width k, the index of the clique solver, n and Δ (k, n, Δ in unary) and the formula,
for a polynomial-time clique solver (`S.Poly`), given the certificates of
its parts: one evaluation by networks (`Net.StCertEvD`), the search (`StCertSearchD`), the listed
family of Lemma 13 (`Fld.StCertFamD`) and the parameters (`StCertParam`). The proof is a
composition. Two
closure lemmas come first: the remainder of an integer modulo a power of two, and the logarithm of a
number given in unary; they are copies of lemmas of
proof/rates/ClauseBound/ParityChecks/CertLib.lean. -/

public section

namespace VariableBound.Count

open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg AppVariables VariableBound.Net

variable {α : Type} [Enc α]

/-! ### Two closure lemmas -/

/-- The remainder of an integer modulo a natural number, by cases on the sign. -/
theorem emod_natCast (a : ℤ) (b : ℕ) :
    a % (b : ℤ) = if 0 ≤ a then ((a.toNat % b : ℕ) : ℤ) else if b = 0 then a else ((b - 1 - (a.natAbs - 1) % b : ℕ) : ℤ) := by
  cases a with
  | ofNat m =>
    have h0 : (0 : ℤ) ≤ Int.ofNat m := Int.natCast_nonneg m
    rw [if_pos h0]
    simp
  | negSucc m =>
    have h0 : ¬ (0 : ℤ) ≤ Int.negSucc m := by simp
    rw [if_neg h0]
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · rw [if_neg (by omega), Int.negSucc_emod m (by exact_mod_cast hb), ← Int.natCast_mod]
      have h1 := Nat.mod_lt m hb
      have h2 : (Int.negSucc m).natAbs - 1 = m := by simp
      rw [h2]
      omega

/-- The remainder of an integer modulo a natural number is polynomial-time. -/
theorem modZ_polyT {a : α → ℤ} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) : PolyT fun x => a x % (b x : ℤ) := by
  have h1 : PolyT fun x => (a x).toNat % b x := PolyT.mod (PolyT.toNat ha) hb
  have h2 : PolyT fun x => b x - 1 - ((a x).natAbs - 1) % b x :=
    PolyT.sub (PolyT.sub hb (PolyT.const 1)) (PolyT.mod (PolyT.sub (PolyT.natAbs ha) (PolyT.const 1)) hb)
  exact (PolyT.ite' (PolyT.decide_leZ (PolyT.const 0) ha) (PolyT.natCast h1)
    (PolyT.ite' (PolyT.decide_eq hb (PolyT.const 0)) ha (PolyT.natCast h2))).congr fun x => (emod_natCast _ _).symm

/-- The remainder of an integer modulo a power of 2 is polynomial-time, for the exponent in unary. -/
theorem mod_two_pow_polyT {a : α → ℤ} {k : α → ℕ} (ha : PolyT a) (hk : Unary k) : PolyT fun x => a x % 2 ^ k x :=
  (modZ_polyT ha (PolyT.pow_unary (PolyT.const 2) hk)).congr fun x => by push_cast; rfl

/-- ⌊log₂ n⌋ is given in unary if n is. -/
theorem log_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => Nat.log 2 (n x) :=
  Unary.of_le hn ((PolyT.log2' hn.poly).congr fun _ => Nat.log2_eq_log_two) fun _ => Nat.log_le_self _ _

/-! ### The program -/

variable {Idx : Type} [Enc Idx] {S : Solver Idx}

/-- The program for X(𝓛) is polynomial-time, given the certificate of one evaluation and a
polynomial-time solver; k, n, Δ, β in unary. -/
theorem evX_polyT (hEv : Net.StCertEvD) (hP : S.Poly) {k n Δ nb M β : α → ℕ} {pad : α → U} {i : α → Idx} {D : α → Dat} (hk : Unary k) (hn : Unary n) (hΔ : Unary Δ)
    (hnb : PolyT nb) (hM : PolyT M) (hβ : Unary β) (hp : PolyT pad) (hi : PolyT i) (hD : PolyT D) :
    PolyT fun x => evX S (k x) (pad x) (i x) (n x) (Δ x) (nb x) (M x) (β x) (D x) := by
  unfold evX
  exact mod_two_pow_polyT (hEv Idx S hP α k n Δ nb M pad i (fun _ => false) D hk hn hΔ hnb hM hp hi (PolyT.const false) hD) hβ

/-- The program for F(𝓛) is polynomial-time, given the certificate of one evaluation and a
polynomial-time solver; k, n, Δ in unary. -/
theorem evF_polyT (hEv : Net.StCertEvD) (hP : S.Poly) {k n Δ nb M : α → ℕ} {pad : α → U} {i : α → Idx} {D : α → Dat} (hk : Unary k) (hn : Unary n) (hΔ : Unary Δ)
    (hnb : PolyT nb) (hM : PolyT M) (hp : PolyT pad) (hi : PolyT i) (hD : PolyT D) :
    PolyT fun x => evF S (k x) (pad x) (i x) (n x) (Δ x) (nb x) (M x) (D x) := by
  unfold evF
  exact mod_two_pow_polyT (hEv Idx S hP α k n Δ nb M pad i (fun _ => true) D hk hn hΔ hnb hM hp hi (PolyT.const true) hD) (hn.add (Unary.const 1))

/-- The count is polynomial-time, given the four certificates and a polynomial-time solver; k, n, Δ
in unary. -/
theorem countD_polyT (hEv : Net.StCertEvD) (hS : StCertSearchD) (hFam : Fld.StCertFamD) (hPar : StCertParam) (hP : S.Poly) {k n Δ : α → ℕ} {pad : α → U} {i : α → Idx}
    {ψ : α → Fml} (hk : Unary k) (hn : Unary n) (hΔ : Unary Δ) (hp : PolyT pad) (hi : PolyT i) (hψ : PolyT ψ) :
    PolyT fun x => countD S (k x) (pad x) (i x) (n x) (Δ x) (ψ x) := by
  have hm : Unary fun x => (ψ x).length := Unary.of_length hψ
  have hnb : Unary fun x => nbD (n x) (Δ x) := (hPar α n Δ n n n n hn hΔ hn hn hn hn).1
  have hβ : Unary fun x => beta (n x) (ψ x).length (nbD (n x) (Δ x)) := (hPar α n Δ _ n _ n hn hΔ hm hn hnb hn).2.1
  have hrb : Unary fun x => rbD (beta (n x) (ψ x).length (nbD (n x) (Δ x))) := (hPar α n Δ n _ n n hn hΔ hn hβ hn hn).2.2.1
  have htb : Unary fun x => tbD (ψ x).length (nbD (n x) (Δ x)) (rbD (beta (n x) (ψ x).length (nbD (n x) (Δ x)))) :=
    (hPar α n Δ _ n _ _ hn hΔ hm hn hnb hrb).2.2.2
  have hM : PolyT fun x => Mb (beta (n x) (ψ x).length (nbD (n x) (Δ x))) (rbD (beta (n x) (ψ x).length (nbD (n x) (Δ x)))) := by
    unfold Mb
    exact PolyT.sub (PolyT.add hrb.poly hβ.poly) (PolyT.const 1)
  have hfam : PolyT fun x => Fld.famD (ψ x).length (Nat.log 2 (nbD (n x) (Δ x))) := hFam α _ _ hm (log_unary hnb)
  have hX : PolyT fun p : α × List (List ℕ) => evX S (k p.1) (pad p.1) (i p.1) (n p.1) (Δ p.1) (nbD (n p.1) (Δ p.1))
      (Mb (beta (n p.1) (ψ p.1).length (nbD (n p.1) (Δ p.1))) (rbD (beta (n p.1) (ψ p.1).length (nbD (n p.1) (Δ p.1)))))
      (beta (n p.1) (ψ p.1).length (nbD (n p.1) (Δ p.1))) (ψ p.1, p.2) :=
    evX_polyT hEv hP (hk.comp PolyT.id'.fst) (hn.comp PolyT.id'.fst) (hΔ.comp PolyT.id'.fst) (hnb.comp PolyT.id'.fst).poly (PolyT.comp hM PolyT.id'.fst)
      (hβ.comp PolyT.id'.fst) (PolyT.comp hp PolyT.id'.fst) (PolyT.comp hi PolyT.id'.fst) (PolyT.prodMk (PolyT.comp hψ PolyT.id'.fst) PolyT.id'.snd)
  have hsearch := hS α pad (fun x L => evX S (k x) (pad x) (i x) (n x) (Δ x) (nbD (n x) (Δ x))
      (Mb (beta (n x) (ψ x).length (nbD (n x) (Δ x))) (rbD (beta (n x) (ψ x).length (nbD (n x) (Δ x)))))
      (beta (n x) (ψ x).length (nbD (n x) (Δ x))) (ψ x, L)) _ _ _ _ _ _ hp hX hfam hm hnb hβ hrb htb
  simp only [countD]
  exact PolyT.cond' (PolyT.decide_le hm.poly hnb.poly)
    (PolyT.toNat (evF_polyT hEv hP hk hn hΔ hnb.poly hM hp hi (PolyT.prodMk hψ (PolyT.const []))))
    (PolyT.toNat (evF_polyT hEv hP hk hn hΔ hnb.poly hM hp hi (PolyT.prodMk hψ hsearch)))

end VariableBound.Count

namespace VariableBound

open Groundwork Groundwork.Prog PaddedDescent.F

/-- Steps 1 to 4 of Appendix D: for every polynomial-time clique solver, the count of one sparse
formula is polynomial-time, jointly in its input, given the certificates of one evaluation by
networks (`Net.StCertEvD`), of the search
(`StCertSearchD`), of the listed family of Lemma 13 (`Fld.StCertFamD`) and of the parameters
(`StCertParam`). -/
theorem stCertCountD (hEv : Net.StCertEvD) (hS : StCertSearchD) (hFam : Fld.StCertFamD) (hPar : StCertParam) : StCertCountD := by
  intro Idx _ S hP
  exact Count.countD_polyT hEv hS hFam hPar hP (k := fun x : U × U × Idx × (U × U) × Fml => x.1.length) (Unary.of_length PolyT.id'.fst)
    (Unary.of_length PolyT.id'.snd.snd.snd.fst.fst) (Unary.of_length PolyT.id'.snd.snd.snd.fst.snd) PolyT.id'.snd.fst PolyT.id'.snd.snd.fst PolyT.id'.snd.snd.snd.snd

end VariableBound
