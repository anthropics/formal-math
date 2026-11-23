/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Paper.Heavy

/-!
# The paper, proof of Proposition prop:pieces: "Part (d) gives the last claim"

From the parents and the loads, the pieces are computed by binary operations.
-/

set_option linter.unusedSectionVars false

namespace Paper

open Finset Unc Nc.Tow Nc.Cut

/-- The same program on a larger alphabet. -/
theorem slp_cast {Inp ι : Type} {D D' p : ℕ} {inp : ι → Inp → Fin D} {inp' : ι → Inp → Fin D'} {H : Set (Inp → ℕ)}
    (hD : D ≤ D') (hinp : ∀ i x, (inp' i x : ℕ) = inp i x) (h : SlpN inp p H) : SlpN inp' p H := by
  obtain ⟨fn, h1, h2⟩ := h
  let cast : Fin D → Fin D' := fun a => ⟨a.1, lt_of_lt_of_le a.2 hD⟩
  refine ⟨fun k x => cast (fn k x), fun k hk => ?_, fun f hf => ?_⟩
  · rcases h1 k hk with ⟨i, e⟩ | ⟨c, e⟩ | ⟨i, hi, j, hj, φ, e⟩
    · exact Or.inl ⟨i, funext fun x => Fin.ext (by rw [hinp]; simp [cast, e])⟩
    · exact Or.inr (Or.inl ⟨cast c, funext fun x => by simp [e]⟩)
    · refine Or.inr (Or.inr ⟨i, hi, j, hj, fun a b => if ha : a.1 < D then
        (if hb : b.1 < D then cast (φ ⟨a, ha⟩ ⟨b, hb⟩) else a) else a, fun x => ?_⟩)
      simp only []
      rw [dif_pos (show (cast (fn i x)).1 < D from (fn i x).2), dif_pos (show (cast (fn j x)).1 < D from (fn j x).2)]
      exact congrArg cast (e x)
  · obtain ⟨k, hk, e⟩ := h2 f hf
    exact ⟨k, hk, e⟩

namespace Staged

variable {Inp ι : Type} {D Y : ℕ} {inp : ι → Inp → Fin D} {p c : ℕ} {H : Set (Inp → ℕ)} {P : ℕ}
  {T : Inp → Staged P} {st : Fin P → ℕ} {dp : ℕ} {rt : Fin P}
  (hst : ∀ x, (T x).stage = st) (hdp : ∀ x, (T x).depth = dp) (hrt : ∀ x, (T x).root = rt)
  (hA : Alph D Y) (hP : P ≤ Y)
include hst hdp hrt hA hP

omit hst hdp in
/-- The indicators "q is j steps below p". -/
theorem anc_stage (hS : SY inp Y p c H) (hpar : ∀ q q', ind (fun x => (T x).par q = q') ∈ H) (t : ℕ) :
    ∃ H', SY inp Y p (c + t) H' ∧ H ⊆ H' ∧ ∀ j < t, ∀ q q', ind (fun x => (T x).nxt^[j] q = q') ∈ H' := by
  classical
  induction t with
  | zero => exact ⟨H, hS, subset_rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ t ih =>
    obtain ⟨H0, s0, u0, f0⟩ := ih
    have hY := hA.pos
    have hκ : Fintype.card (Fin P × Fin P) ≤ Y ^ 2 := by
      rw [Fintype.card_prod, Fintype.card_fin, pow_two]
      exact Nat.mul_le_mul hP hP
    obtain ⟨H1, s1, u1, f1⟩ := s0.add hA (fun q : Fin P × Fin P => ind fun x => (T x).nxt^[t] q.1 = q.2) (a := 3) (e := 2)
      hκ (fun q => by
        cases t with
        | zero => exact (((PY.const hA (q.1 = q.2)).congr fun x => Iff.rfl).toCY).mono hY (Nat.zero_le 3)
        | succ t =>
          have h1 : PY D H0 Y 3 fun x => ∃ q', (T x).nxt^[t] q.1 = q' ∧ (T x).nxt q' = q.2 :=
            PY.exists_univ hA (by simpa using hP) fun q' => PY.and hA (PY.base (f0 t (Nat.lt_succ_self t) q.1 q') hY) (by
              by_cases h : q' = rt
              · refine (PY.const hA (q' = q.2)).congr fun x => ?_
                unfold nxt
                rw [if_pos (h.trans (hrt x).symm)]
              · refine (PY.base (u0 (hpar q' q.2)) hY).congr fun x => ?_
                unfold nxt
                rw [if_neg fun e => h (e.trans (hrt x))])
          refine (h1.congr fun x => ?_).toCY
          rw [Function.iterate_succ_apply']
          exact ⟨fun ⟨q', e, e'⟩ => e ▸ e', fun e => ⟨_, rfl, e⟩⟩) (by omega)
    refine ⟨H1, s1, u0.trans u1, fun j hj q q' => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact u1 (f0 j hj q q')
    · exact f1 (q, q')

variable {giv : Fin P → ℕ} {u : Inp → Fin P → ℕ} {M Yh k : ℕ}

open Classical in
/-- The program of the pieces. -/
theorem piece_prog (hS : SY inp Y p c H) (hpar : ∀ q q', ind (fun x => (T x).par q = q') ∈ H)
    (hu : ∀ q, (fun x => u x q) ∈ H) (hgiv : ∀ q, giv q ≤ 1) (hub : ∀ x q, u x q ≤ Y) :
    ∃ H', SY inp Y p (c + 2 * dp + 9) H' ∧ H ⊆ H' ∧
      ∀ q, (fun x => (T x).piece giv (u x) M Yh k q) ∈ H' := by
  have hY := hA.pos
  have hPc : Fintype.card (Fin P) ≤ Y ^ 1 := by rwa [Fintype.card_fin, pow_one]
  have hPP : Fintype.card (Fin P × Fin P) ≤ Y ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_fin, pow_two]
    exact Nat.mul_le_mul hP hP
  have hsum : ∀ (f : Fin P → ℕ), (∀ q, f q ≤ Y) → ∑ q, f q < D := fun f hf => by
    refine hA.lt_of_le3 ?_
    calc ∑ q, f q ≤ ∑ _q : Fin P, Y := Finset.sum_le_sum fun q _ => hf q
      _ = P * Y := by simp
      _ ≤ Y * Y := Nat.mul_le_mul_right _ hP
      _ ≤ 2 * Y ^ 3 := by
          have : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY (by omega)
          rw [pow_two] at this
          omega
  obtain ⟨H1, s1, u1, f1⟩ := anc_stage hrt hA hP hS hpar (dp + 1)
  -- below
  have hB : ∀ q q', PY D H1 Y 0 fun x => (T x).Below q q' := fun q q' => by
    by_cases h : st q ≤ st q'
    · have h1 : st q' - st q < dp + 1 ∨ ∀ x : Inp, False := by
        by_cases hne : Nonempty Inp
        · obtain ⟨x⟩ := hne
          left
          have := (T x).stage_le q'
          rw [hst, hdp] at this
          omega
        · exact Or.inr fun x => hne ⟨x⟩
      rcases h1 with h1 | h1
      · refine (PY.base (f1 _ h1 q q') hY).congr fun x => ?_
        unfold Below
        rw [hst]
        exact ⟨fun e => ⟨h, e⟩, fun e => e.2⟩
      · exact (PY.const hA True).congr fun x => (h1 x).elim
    · refine (PY.const hA False).congr fun x => ⟨False.elim, fun e => h ?_⟩
      rw [← hst x]
      exact e.1
  have hbel : ∀ f : Inp → Fin P → ℕ, (∀ q, CY D H1 Y 0 fun x => f x q) → (∀ x q, f x q ≤ Y) →
      ∀ q', CY D H1 Y 3 fun x => (T x).below (f x) q' := by
    intro f hf hf' q'
    have e : ∀ x, (T x).below (f x) q' = ∑ q ∈ univ, ind (fun x => (T x).Below q q') x * f x q := fun x => by
      unfold below
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases h : (T x).Below q q'
      · rw [if_pos h, ind_true (P := fun x => (T x).Below q q') h, one_mul]
      · rw [if_neg h, ind_false (P := fun x => (T x).Below q q') h, zero_mul]
    refine CY.congr ?_ fun x => (e x).symm
    have hle : ∀ x q, ind (fun x => (T x).Below q q') x * f x q ≤ Y := fun x q =>
      (Nat.mul_le_mul (ind_le _ _) (hf' x q)).trans (le_of_eq (one_mul _))
    exact CY.sum hA univ (by simpa using hP)
      (fun q _ => CY.op hA (fun a b => a * b) (hB q q').toCY (hf q) fun x => hA.lt_of_le (hle x q))
      fun x => hsum _ (hle x)
  obtain ⟨H2, s2, u2, f2⟩ := s1.add hA (fun q x => (T x).below giv q) (a := 3) (e := 1) hPc
    (hbel (fun _ => giv) (fun q => CY.const _ (hA.lt_of_le ((hgiv q).trans hY))) fun x q => (hgiv q).trans hY) (by omega)
  obtain ⟨H3, s3, u3, f3⟩ := s2.add hA (fun q x => (T x).below (u x) q) (a := 3) (e := 1) hPc
    (fun q => (hbel u (fun q => CY.base (u1 (hu q)) hY) hub q).weaken u2) (by omega)
  -- heavy and heads
  obtain ⟨H4, s4, u4, f4⟩ := s3.add hA (fun q => ind fun x => (T x).Heavy giv (u x) M Yh k q) (a := 1) (e := 1) hPc
    (fun q => by
      by_cases h : q = rt
      · exact ((((PY.const hA True).congr fun x => ⟨fun _ => Or.inl (h.trans (hrt x).symm), fun _ => trivial⟩)).toCY).mono hY
          (Nat.zero_le 1)
      · refine ((PY.rel hA (fun a b => 8 * M * Yh < k * (a * (2 * Yh) + b * (4 * M))) (CY.base (u3 (f2 q)) hY)
          (CY.base (f3 q) hY)).congr fun x => ?_).toCY
        exact ⟨Or.inr, fun e => e.resolve_left fun e => h (e.trans (hrt x))⟩) (by omega)
  obtain ⟨H5, s5, u5, f5⟩ := s4.add hA (fun q => ind fun x => (T x).Head giv (u x) M Yh k q) (a := 3) (e := 1) hPc
    (fun q => by
      by_cases h : q = rt
      · exact ((((PY.const hA True).congr fun x => ⟨fun _ => Or.inl (h.trans (hrt x).symm), fun _ => trivial⟩)).toCY).mono hY
          (Nat.zero_le 3)
      · have h1 : PY D H4 Y 3 fun x => ∃ q', (T x).par q = q' ∧ (T x).Heavy giv (u x) M Yh k q' :=
          PY.exists_univ hA (by simpa using hP) fun q' =>
            PY.and hA (PY.base (u4 (u3 (u2 (u1 (hpar q q'))))) hY) (PY.base (f4 q') hY)
        refine (h1.congr fun x => ?_).toCY
        exact ⟨fun ⟨q', e, e'⟩ => Or.inr (e ▸ e'),
          fun e => ⟨_, rfl, e.resolve_left fun e => h (e.trans (hrt x))⟩⟩) (by omega)
  -- the head above
  have htop : ∀ t, ∃ H', SY inp Y p (c + (dp + 1) + 1 + 1 + 1 + 1 + t) H' ∧ H5 ⊆ H' ∧
      ∀ d < t, ∀ q q', ind (fun x => (T x).top giv (u x) M Yh k d q = q') ∈ H' := by
    intro t
    induction t with
    | zero => exact ⟨H5, s5, subset_rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    | succ t ih =>
      obtain ⟨H0, s0, u0, f0⟩ := ih
      obtain ⟨H', s', u', f'⟩ := s0.add hA
        (fun q : Fin P × Fin P => ind fun x => (T x).top giv (u x) M Yh k t q.1 = q.2) (a := 5) (e := 2) hPP (fun q => by
        cases t with
        | zero => exact (((PY.const hA (q.1 = q.2)).congr fun x => Iff.rfl).toCY).mono hY (Nat.zero_le 5)
        | succ t =>
          have hd : PY D H0 Y 0 fun x => (T x).Head giv (u x) M Yh k q.1 := PY.base (u0 (f5 q.1)) hY
          have h1 : PY D H0 Y 3 fun x => ∃ q', (T x).par q.1 = q' ∧ (T x).top giv (u x) M Yh k t q' = q.2 :=
            PY.exists_univ hA (by simpa using hP) fun q' =>
              PY.and hA (PY.base (u0 (u5 (u4 (u3 (u2 (u1 (hpar q.1 q'))))))) hY)
                (PY.base (f0 t (Nat.lt_succ_self t) q' q.2) hY)
          have h2 := PY.or hA
            ((PY.and hA hd (PY.const hA (q.1 = q.2))).mono hY (show 1 ≤ 4 by omega))
            (PY.and hA ((PY.not hA hd).mono hY (show 1 ≤ 3 by omega)) h1)
          refine (h2.congr fun x => ?_).toCY
          rw [top]
          by_cases h : (T x).Head giv (u x) M Yh k q.1
          · rw [if_pos h]
            exact ⟨fun e => e.elim (fun e => e.2) fun e => absurd h e.1, fun e => Or.inl ⟨h, e⟩⟩
          · rw [if_neg h]
            exact ⟨fun e => e.elim (fun e => absurd e.1 h) fun ⟨_, q', e, e'⟩ => e ▸ e',
              fun e => Or.inr ⟨h, _, rfl, e⟩⟩) (by omega)
      refine ⟨H', s', u0.trans u', fun d hd q q' => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hd with hd | rfl
      · exact u' (f0 d hd q q')
      · exact f' (q, q')
  obtain ⟨H6, s6, u6, f6⟩ := htop (dp + 1)
  obtain ⟨H7, s7, u7, f7⟩ := s6.add hA (fun q x => (T x).rank giv (u x) M Yh k q) (a := 2) (e := 1) hPc (fun q => by
    have e : ∀ x, (T x).rank giv (u x) M Yh k q = ∑ q' ∈ univ.filter (fun q' => q' < q),
        ind (fun x => (T x).Head giv (u x) M Yh k q') x := by
      intro x
      unfold rank
      rw [Finset.card_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun q' _ => ?_
      by_cases h : (T x).Head giv (u x) M Yh k q'
      · by_cases h' : q' < q
        · rw [if_pos ⟨h, h'⟩, if_pos h', ind_true (P := fun x => (T x).Head giv (u x) M Yh k q') h]
        · rw [if_neg fun e => h' e.2, if_neg h']
      · rw [if_neg fun e => h e.1, ind_false (P := fun x => (T x).Head giv (u x) M Yh k q') h]
        split_ifs <;> rfl
    refine CY.congr ?_ fun x => (e x).symm
    refine CY.sum hA _ ((card_filter_le _ _).trans (by simpa using hP)) (fun q' _ => CY.base (u6 (f5 q')) hY) fun x => ?_
    refine hA.lt_of_le ((Finset.sum_le_sum fun q' _ => ind_le _ x).trans ?_)
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    exact (card_filter_le _ _).trans (by simpa using hP)) (by omega)
  obtain ⟨H8, s8, u8, f8⟩ := s7.add hA (fun q x => (T x).piece giv (u x) M Yh k q) (a := 3) (e := 1) hPc (fun q => by
    have e : ∀ x, (T x).piece giv (u x) M Yh k q =
        ∑ q' ∈ univ, ind (fun x => (T x).top giv (u x) M Yh k (dp - st q) q = q') x *
          (T x).rank giv (u x) M Yh k q' := by
      intro x
      have e0 : (T x).hd giv (u x) M Yh k q = (T x).top giv (u x) M Yh k (dp - st q) q := by
        unfold hd
        rw [hdp, hst]
      rw [piece, e0, Finset.sum_eq_single ((T x).top giv (u x) M Yh k (dp - st q) q)]
      · rw [ind_true (P := fun y => (T y).top giv (u y) M Yh k (dp - st q) q = (T x).top giv (u x) M Yh k (dp - st q) q) rfl,
          one_mul]
      · intro q' _ hne
        rw [ind_false (P := fun y => (T y).top giv (u y) M Yh k (dp - st q) q = q') hne.symm, zero_mul]
      · exact fun hn => absurd (mem_univ _) hn
    refine CY.congr ?_ fun x => (e x).symm
    have hle : ∀ x q', ind (fun x => (T x).top giv (u x) M Yh k (dp - st q) q = q') x *
        (T x).rank giv (u x) M Yh k q' ≤ Y := fun x q' => by
      refine (Nat.mul_le_mul_right _ (ind_le _ x)).trans ?_
      rw [one_mul]
      unfold rank
      exact (card_filter_le _ _).trans (by simpa using hP)
    exact CY.sum hA univ (by simpa using hP) (fun q' _ => CY.op hA (fun a b => a * b)
      (CY.base (u7 (f6 _ (by omega) q q')) hY) (CY.base (f7 q') hY) fun x => hA.lt_of_le (hle x q'))
      fun x => hsum _ (hle x)) (by omega)
  exact ⟨H8, s8.le hA (by omega),
    u1.trans (u2.trans (u3.trans (u4.trans (u5.trans (u6.trans (u7.trans u8)))))), f8⟩

end Staged

end Paper
