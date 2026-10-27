/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Inst.HalfPart
public import PaddedDescent.F.FuelCert

/-! # The numbers of partitions and the table of all partitions are polynomial-time

Certificates (`PolyT`, `Unary`) for the functions of proof/rates/ClauseBound/Inst/HalfPart.lean.
Without a pad: the table p(0), …, p(W) with W in unary (`pTab_polyT`; its entries have at most W + 1
binary digits
because p(E) ≤ 2^E), the number `hF c₀ lam` with lam in unary (`hF_unary`), the sums `RrowF`,
`RcolF` with h in unary (`RrowF_polyT`, `RcolF_polyT`). With the pad: the table of all partitions
(`allTabF_polyT`), a fold inside a fold, each with its state cut off by the pad after every step. -/

public section

namespace ClauseBound.Inst.Half

open Groundwork PaddedDescent.F ClauseBound.Part Partitions

variable {α : Type} [Enc α]

/-! ### Without a pad -/

/-- The next entry of the table of numbers. -/
theorem nextP_polyT {T : α → List ℕ} (hT : PolyT T) : PolyT fun x => nextP (T x) := by
  have hT1 : PolyT fun q : α × ℕ => T q.1 := PolyT.comp hT PolyT.id'.fst
  have hT2 : PolyT fun r : (α × ℕ) × ℕ => T r.1.1 := PolyT.comp hT PolyT.id'.fst.fst
  have hv : PolyT fun r : (α × ℕ) × ℕ => r.1.2 + 1 := PolyT.add PolyT.id'.fst.snd (PolyT.const 1)
  have hk : PolyT fun r : (α × ℕ) × ℕ => r.2 + 1 := PolyT.add PolyT.id'.snd (PolyT.const 1)
  have hin : PolyT fun r : (α × ℕ) × ℕ => (r.1.2 + 1) * (T r.1.1).getD ((T r.1.1).length - (r.2 + 1) * (r.1.2 + 1)) 0 :=
    PolyT.mul hv (PolyT.getD hT2 (PolyT.sub hT2.length (PolyT.mul hk hv)) (PolyT.const 0))
  have hr : PolyT fun q : α × ℕ => List.range ((T q.1).length / (q.2 + 1)) :=
    PolyT.range (unary_div (Unary.of_length hT1) (PolyT.add PolyT.id'.snd (PolyT.const 1)))
  have hmid : PolyT fun q : α × ℕ => ((List.range ((T q.1).length / (q.2 + 1))).map fun k =>
      (q.2 + 1) * (T q.1).getD ((T q.1).length - (k + 1) * (q.2 + 1)) 0).sum := PolyT.sum (PolyT.map hin hr)
  unfold nextP
  exact PolyT.div (PolyT.sum (PolyT.map hmid (PolyT.range (Unary.of_length hT)))) hT.length

/-- The word of the table p(0), …, p(j) has length at most (j + 1) * (3 * (j + 1) + 4) + 2. -/
theorem len_pTab_le (j : ℕ) : len (pTab j) ≤ (j + 1) * (3 * (j + 1) + 4) + 2 := by
  have h := len_le_of_forall (c := 3 * (j + 1) + 2) (pTab j) fun a ha => by
    rw [pTab_eq] at ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    have hi' := List.mem_range.1 hi
    have : Nat.size (p i) ≤ j + 1 := Nat.size_le.2 ((p_le_two_pow i).trans_lt (Nat.pow_lt_pow_right (by norm_num) hi'))
    rw [len_nat]
    omega
  rw [length_pTab] at h
  exact h

/-- The table p(0), …, p(W) is polynomial-time in W in unary. -/
theorem pTab_polyT {W : α → ℕ} (hW : Unary W) : PolyT fun x => pTab (W x) := by
  obtain ⟨t, ht, -, hlen⟩ := PolyT.len_bound hW
  have hWt : ∀ x, W x ≤ t (len x) := fun x => by
    have := (length_le_len (List.replicate (W x) ())).trans (hlen x)
    simpa using this
  have hg : PolyT fun q : α × List ℕ × ℕ => q.2.1 ++ [nextP q.2.1] :=
    PolyT.append PolyT.id'.snd.fst (PolyT.cons' (nextP_polyT PolyT.id'.snd.fst) (PolyT.const []))
  unfold pTab
  refine PolyT.foldl (l := fun x => List.range (W x)) (a := fun _ => [1]) (g := fun _ T _ => T ++ [nextP T]) (PolyT.range hW)
    (PolyT.const _) hg ⟨fun n => (t n + 1) * (3 * (t n + 1) + 4) + 2, ?_, fun x k => ?_⟩
  · exact ((ht.add (PB.const 1)).mul (((PB.const 3).mul (ht.add (PB.const 1))).add (PB.const 4))).add (PB.const 2)
  · rw [List.take_range]
    have h1 : min k (W x) + 1 ≤ t (len x) + 1 := Nat.succ_le_succ ((min_le_right _ _).trans (hWt x))
    exact (len_pTab_le (min k (W x))).trans
      (Nat.add_le_add_right (Nat.mul_le_mul h1 (Nat.add_le_add_right (Nat.mul_le_mul_left 3 h1) 4)) 2)

/-- Reading a table of numbers at an integer. -/
theorem pzF_polyT {T : α → List ℕ} {E : α → ℤ} (hT : PolyT T) (hE : PolyT E) : PolyT fun x => pzF (T x) (E x) := by
  unfold pzF; fun_prop

/-- `hF c₀ lam` is polynomial-time in lam in unary. -/
theorem hF_polyT (c₀ : ℕ) {lam : α → ℕ} (hl : Unary lam) : PolyT fun x => hF c₀ (lam x) := by
  have hN : Unary fun x => c₀ * lam x ^ 2 := (Unary.const c₀).mul (unary_pow_const hl 2)
  have hT : PolyT fun x => pTab (c₀ * lam x ^ 2) := pTab_polyT hN
  have hpow : PolyT fun x => 2 ^ lam x := pow_polyT (PolyT.const 2) hl
  have hr : PolyT fun x => List.range (c₀ * lam x ^ 2 + 1) := PolyT.range (hN.add (Unary.const 1))
  have hpred : PolyT fun q : α × ℕ => decide (2 ≤ q.2) && decide (2 ^ lam q.1 ≤ (pTab (c₀ * lam q.1 ^ 2)).getD q.2 0) := by
    have h1 : PolyT fun q : α × ℕ => pTab (c₀ * lam q.1 ^ 2) := PolyT.comp (f := fun x => pTab (c₀ * lam x ^ 2)) hT PolyT.id'.fst
    have h2 : PolyT fun q : α × ℕ => 2 ^ lam q.1 := PolyT.comp (f := fun x => 2 ^ lam x) hpow PolyT.id'.fst
    exact PolyT.and' (PolyT.decide_le (PolyT.const 2) PolyT.id'.snd) (PolyT.decide_le h2 (PolyT.getD h1 PolyT.id'.snd (PolyT.const 0)))
  unfold hF
  exact PolyT.optionGetD (PolyT.find? hpred hr) (PolyT.const 2)

/-- `hF c₀ lam` is given in unary if lam is. -/
theorem hF_unary (c₀ : ℕ) {lam : α → ℕ} (hl : Unary lam) : Unary fun x => hF c₀ (lam x) :=
  (((Unary.const c₀).mul (unary_pow_const hl 2)).add (Unary.const 2)).of_le (hF_polyT c₀ hl) fun x => hF_le c₀ (lam x)

/-- The sum of the row-wise pieces is polynomial-time in h in unary and s. -/
theorem RrowF_polyT {h : α → ℕ} {s : α → ℤ} (hh : Unary h) (hs : PolyT s) : PolyT fun x => RrowF (h x) (s x) := by
  have hT : PolyT fun x => pTab (4 * h x) := pTab_polyT ((Unary.const 4).mul hh)
  have hr : PolyT fun x => List.range (2 * h x + 1) := PolyT.range (((Unary.const 2).mul hh).add (Unary.const 1))
  have hf : PolyT fun q : α × ℕ => pzF (pTab (4 * h q.1)) (s q.1 + (q.2 : ℤ)) :=
    pzF_polyT (PolyT.comp (f := fun x => pTab (4 * h x)) hT PolyT.id'.fst) (PolyT.addZ (PolyT.comp hs PolyT.id'.fst) (PolyT.natCast PolyT.id'.snd))
  unfold RrowF
  exact PolyT.sum (PolyT.map hf hr)

/-- The sum of the column-wise pieces is polynomial-time in h in unary and s. -/
theorem RcolF_polyT {h : α → ℕ} {s : α → ℤ} (hh : Unary h) (hs : PolyT s) : PolyT fun x => RcolF (h x) (s x) := by
  have hT : PolyT fun x => pTab (4 * h x) := pTab_polyT ((Unary.const 4).mul hh)
  have hr : PolyT fun x => List.range (2 * h x + 1) := PolyT.range (((Unary.const 2).mul hh).add (Unary.const 1))
  have hh' : PolyT fun q : α × ℕ => ((h q.1 : ℕ) : ℤ) := PolyT.natCast (PolyT.comp hh.poly PolyT.id'.fst)
  have hf : PolyT fun q : α × ℕ => pzF (pTab (4 * h q.1)) (2 * (h q.1 : ℤ) - s q.1 - (q.2 : ℤ)) :=
    pzF_polyT (PolyT.comp (f := fun x => pTab (4 * h x)) hT PolyT.id'.fst)
      (PolyT.subZ (PolyT.subZ (PolyT.mulZ (PolyT.const 2) hh') (PolyT.comp hs PolyT.id'.fst)) (PolyT.natCast PolyT.id'.snd))
  unfold RcolF
  exact PolyT.sum (PolyT.map hf hr)

/-! ### With the pad -/

/-- The table before the first round. -/
theorem initT_polyT {W : α → ℕ} (hW : Unary W) : PolyT fun x => initT (W x) := by
  have hr : PolyT fun x => List.range (W x + 1) := PolyT.range (hW.add (Unary.const 1))
  have hf : PolyT fun q : α × ℕ => if q.2 = 0 then [([] : List ℕ)] else [] :=
    PolyT.ite' (PolyT.decide_eq PolyT.id'.snd (PolyT.const 0)) (PolyT.const _) (PolyT.const _)
  unfold initT
  exact PolyT.map hf hr

/-- One step of a round. -/
theorem stepE_polyT {k E : α → ℕ} {old new : α → PT} (hk : PolyT k) (ho : PolyT old) (hn : PolyT new) (hE : PolyT E) :
    PolyT fun x => stepE (k x) (old x) (new x) (E x) := by
  unfold stepE; fun_prop

/-- One round with the pad. -/
theorem roundF_polyT {pad : α → U} {W k : α → ℕ} {old : α → PT} (hp : PolyT pad) (hW : Unary W) (hk : PolyT k) (ho : PolyT old) :
    PolyT fun x => roundF (pad x) (W x) (k x) (old x) := by
  unfold roundF
  exact foldl_cap (pad := pad) (l := fun x => List.range (W x + 1)) (a := fun _ => ([] : PT))
    (g := fun x new E => stepE (k x) (old x) new E) [] hp (PolyT.range (hW.add (Unary.const 1))) (PolyT.const _)
    (stepE_polyT (PolyT.comp hk PolyT.id'.fst) (PolyT.comp ho PolyT.id'.fst) PolyT.id'.snd.fst PolyT.id'.snd.snd)

/-- The table of all partitions of 0, …, W with the pad is polynomial-time in the pad and W in
unary. -/
theorem allTabF_polyT {pad : α → U} {W : α → ℕ} (hp : PolyT pad) (hW : Unary W) : PolyT fun x => allTabF (pad x) (W x) := by
  unfold allTabF
  exact foldl_cap (pad := pad) (l := fun x => List.range (W x)) (a := fun x => initT (W x))
    (g := fun x old k => roundF (pad x) (W x) (k + 1) old) [] hp (PolyT.range hW) (initT_polyT hW)
    (roundF_polyT (PolyT.comp hp PolyT.id'.fst) (hW.comp PolyT.id'.fst) (PolyT.add PolyT.id'.snd.snd (PolyT.const 1)) PolyT.id'.snd.fst)

end ClauseBound.Inst.Half
