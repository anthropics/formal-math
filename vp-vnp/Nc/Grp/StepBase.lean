/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.SumBase

/-!
# The step of a base party
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset Nc.G Nc.Cut

variable {A : Type} [CommRing A] {θ : List Bool → A}
variable {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {A' K E U0 U1 ub c T : ℕ} {Gr : Type} [DecidableEq Gr]
  {mu : Letter S Unit Γ → Matrix Q Q A} {cb : Option Γ → Fin c → Bool} {kinds : List (Σ L : G.Law A, L.Ro)}
  {M : Sys A (K + K + A') E} {q : Fin (K + 1) → Q} {x : Fin K → List Γ}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)}
  {o : M.N → Fin U1} {grp : Fin (K + K + A') → Gr} {g : Gr}
  {key : Cell M U0 U1 → List Bool} {dkey : Fin (K + K) × Fin U0 → List Bool}

theorem ofBits_injective : Function.Injective ofBits := by
  intro v w h
  rw [← path_ofBits v, h, path_ofBits]

variable (θ mu cb kinds T key) in
/-- The instructions do what the step does. -/
def StepOK (I : List Ins) (s : WStep A (Cell M U0 U1) (UW ub)) : Prop :=
  ∀ (t : Tree) (σ : Cell M U0 U1 → UW ub) (Ψ : Tree → A) (Ψ' : (Cell M U0 U1 → UW ub) → A), Rep ub key t σ →
    (∀ t' σ', Rep ub key t' σ' → Ψ t' = Ψ' σ') →
    sumL (scriptSem (S := S) θ mu cb kinds T ub I t) Ψ = ∑ ω ∈ s.Om, s.w ω σ * Ψ' (ovr s.wr (s.v ω σ) σ)

theorem mem_kRl {p b : Fin (K + K)} {k : List Bool} :
    k ∈ kRl n key p b ↔ ∃ i : Fin U0, i.1 < (n p b).1 ∧ k = key (Fin.castAdd A' p, .init p b i) := by
  simp only [kRl, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

theorem mem_kCl {p b : Fin (K + K)} {k : List Bool} :
    k ∈ kCl n key dkey p b ↔ ∃ i : Fin U0, i.1 < (n b p).1 ∧
      k = if b = p then dkey (p, i) else key (Fin.castAdd A' p, .init b p i) := by
  simp only [kCl, List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩

theorem getElem_map_filter {U d : ℕ} (h : d ≤ U) (f : Fin U → List Bool) (i : Fin U) (hi : i.1 < d) :
    (((List.finRange U).filter fun k => k.1 < d).map f)[i.1]? = some (f i) := by
  rw [filter_finRange h, List.map_ofFn, List.getElem?_eq_getElem (by simpa using hi)]
  simp

section keys

variable (hkey : Function.Injective (Sum.elim key dkey))

include hkey

theorem key_injective : Function.Injective key := fun a b h => by
  have := hkey (a₁ := Sum.inl a) (a₂ := Sum.inl b) h
  simpa using this

theorem dkey_injective : Function.Injective dkey := fun a b h => by
  have := hkey (a₁ := Sum.inr a) (a₂ := Sum.inr b) h
  simpa using this

theorem key_ne_dkey (a : Cell M U0 U1) (b : Fin (K + K) × Fin U0) : key a ≠ dkey b := fun h => by
  have := hkey (a₁ := Sum.inl a) (a₂ := Sum.inr b) h
  simp at this

theorem nodup_PR (p : Fin (K + K)) (R : Option S → Fin (K + K) → List Γ) :
    ((PR n key cb p R).flatMap Prod.fst).Nodup := by
  have hk := key_injective hkey
  rw [PR, List.ofFn_eq_map, List.flatMap_map, List.nodup_flatMap]
  refine ⟨fun b _ => ?_, (List.nodup_finRange _).imp fun {b b'} hb => ?_⟩
  · refine ((List.nodup_finRange _).filter _).map fun i j h => ?_
    have := hk h
    simpa using this
  · rw [Function.onFun, List.disjoint_left]
    intro k hk1 hk2
    obtain ⟨i, -, rfl⟩ := mem_kRl.1 hk1
    obtain ⟨j, -, h⟩ := mem_kRl.1 hk2
    have := hk h
    simp only [Prod.mk.injEq, true_and, G.Uid.init.injEq] at this
    exact hb this.1

theorem nodup_PC (p : Fin (K + K)) (C : Option S → Fin (K + K) → List Γ) :
    ((PC n key dkey cb p C).flatMap Prod.fst).Nodup := by
  have hk := key_injective hkey
  have hd := dkey_injective hkey
  rw [PC, List.ofFn_eq_map, List.flatMap_map, List.nodup_flatMap]
  refine ⟨fun b _ => ?_, (List.nodup_finRange _).imp fun {b b'} hb => ?_⟩
  · refine ((List.nodup_finRange _).filter _).map fun i j h => ?_
    by_cases hbp : b = p
    · simp only [hbp, if_true] at h
      have := hd h
      simpa using this
    · simp only [hbp, if_false] at h
      have := hk h
      simpa using this
  · rw [Function.onFun, List.disjoint_left]
    intro k hk1 hk2
    obtain ⟨i, -, h1⟩ := mem_kCl.1 hk1
    obtain ⟨j, -, h2⟩ := mem_kCl.1 hk2
    rw [h1] at h2
    by_cases hbp : b = p
    · have hbp' : b' ≠ p := fun h => hb (hbp.trans h.symm)
      rw [if_pos hbp, if_neg hbp'] at h2
      exact key_ne_dkey hkey _ _ h2.symm
    · rw [if_neg hbp] at h2
      by_cases hbp' : b' = p
      · rw [if_pos hbp'] at h2
        exact key_ne_dkey hkey _ _ h2
      · rw [if_neg hbp'] at h2
        have := hk h2
        simp only [Prod.mk.injEq, true_and, G.Uid.init.injEq] at this
        exact hb this.1

theorem mem_PR {p : Fin (K + K)} {R : Option S → Fin (K + K) → List Γ} {k : List Bool} :
    k ∈ (PR n key cb p R).flatMap Prod.fst ↔ ∃ b, ∃ i : Fin U0, i.1 < (n p b).1 ∧
      k = key (Fin.castAdd A' p, .init p b i) := by
  rw [PR, List.ofFn_eq_map, List.flatMap_map, List.mem_flatMap]
  simp only [List.mem_finRange, true_and, mem_kRl]

theorem mem_PC {p : Fin (K + K)} {C : Option S → Fin (K + K) → List Γ} {k : List Bool} :
    k ∈ (PC n key dkey cb p C).flatMap Prod.fst ↔ ∃ b, ∃ i : Fin U0, i.1 < (n b p).1 ∧
      k = if b = p then dkey (p, i) else key (Fin.castAdd A' p, .init b p i) := by
  rw [PC, List.ofFn_eq_map, List.flatMap_map, List.mem_flatMap]
  simp only [List.mem_finRange, true_and, mem_kCl]

/-- The trie after a base party. -/
noncomputable def baseT (ub : ℕ) (n : Fin (K + K) → Fin (K + K) → Fin (U0 + 1)) (key : Cell M U0 U1 → List Bool)
    (dkey : Fin (K + K) × Fin U0 → List Bool) (cb : Option Γ → Fin c → Bool) (p : Fin (K + K))
    (R C : Option S → Fin (K + K) → List Γ) (t : Tree) : Tree :=
  putsAll ub (PC n key dkey cb p C) (putsAll ub (PR n key cb p R) t)

theorem baseT_R (p b : Fin (K + K)) (R C : Option S → Fin (K + K) → List Γ) (t : Tree) (i : Fin U0)
    (hi : i.1 < (n p b).1) : tget (key (Fin.castAdd A' p, .init p b i)) (baseT ub n key dkey cb p R C t) =
      ofBits (uwBits (unitsOf ub (strOf cb fun s => R s b) i)) := by
  rw [baseT, tget_putsAll_not (nodup_PC hkey p C)]
  · have hmem : (kRl n key p b, strOf cb fun s => R s b) ∈ PR n key cb p R :=
      List.mem_ofFn.2 ⟨b, rfl⟩
    exact tget_putsAll (nodup_PR hkey p R) hmem (getElem_map_filter (by have := (n p b).2; omega) _ i hi) t
  · rw [mem_PC hkey]
    rintro ⟨b', j, -, h⟩
    by_cases hb : b' = p
    · rw [if_pos hb] at h
      exact key_ne_dkey hkey _ _ h
    · rw [if_neg hb] at h
      have := key_injective hkey h
      simp only [Prod.mk.injEq, true_and, G.Uid.init.injEq] at this
      exact hb this.1.symm

theorem baseT_C (p b : Fin (K + K)) (R C : Option S → Fin (K + K) → List Γ) (t : Tree) (i : Fin U0)
    (hi : i.1 < (n b p).1) : tget (if b = p then dkey (p, i) else key (Fin.castAdd A' p, .init b p i))
      (baseT ub n key dkey cb p R C t) = ofBits (uwBits (unitsOf ub (strOf cb fun s => C s b) i)) := by
  rw [baseT]
  have hmem : (kCl n key dkey p b, strOf cb fun s => C s b) ∈ PC n key dkey cb p C :=
    List.mem_ofFn.2 ⟨b, rfl⟩
  exact tget_putsAll (nodup_PC hkey p C) hmem (getElem_map_filter (by have := (n b p).2; omega)
    (fun k => if b = p then dkey (p, k) else key (Fin.castAdd A' p, .init b p k)) i hi) _

theorem baseT_not (p : Fin (K + K)) (R C : Option S → Fin (K + K) → List Γ) (t : Tree) {k : List Bool}
    (h1 : ∀ b, ∀ i : Fin U0, i.1 < (n p b).1 → k ≠ key (Fin.castAdd A' p, .init p b i))
    (h2 : ∀ b, ∀ i : Fin U0, i.1 < (n b p).1 → k ≠ if b = p then dkey (p, i) else key (Fin.castAdd A' p, .init b p i)) :
    tget k (baseT ub n key dkey cb p R C t) = tget k t := by
  rw [baseT, tget_putsAll_not (nodup_PC hkey p C), tget_putsAll_not (nodup_PR hkey p R)]
  · rw [mem_PR hkey]
    rintro ⟨b, i, hi, h⟩
    exact h1 b i hi h
  · rw [mem_PC hkey]
    rintro ⟨b, i, hi, h⟩
    exact h2 b i hi h

/-- The contents after a base party. -/
theorem rep_baseT {p : Fin (K + K)} (hp : grp (Fin.castAdd A' p) = g) (R C : Option S → Fin (K + K) → List Γ) {t : Tree}
    {σ : Cell M U0 U1 → UW ub} (h : Rep ub key t σ) : Rep ub key (baseT ub n key dkey cb p R C t)
      (ovr ((dom n o grp g).filter fun c => c.1 = Fin.castAdd A' p ∧ isInit c.2 = true)
        (fun c => initV cb ub M.N U0 U1 R C p c.2) σ) := by
  refine ⟨h.1.putsAll.putsAll, fun c' => ?_⟩
  obtain ⟨a, id⟩ := c'
  by_cases hc : (a, id) ∈ (dom n o grp g).filter fun c => c.1 = Fin.castAdd A' p ∧ isInit c.2 = true
  · rw [ovr, if_pos hc]
    obtain ⟨h1, h2, h3⟩ := mem_filter.1 hc
    simp only at h2
    subst h2
    cases id with
    | new _ _ => simp [isInit] at h3
    | init a' b' k =>
      have hk : k.1 < (n a' b').1 := G.Plan.init_mem_seenAt.1 (mem_dom.1 h1).2.1
      simp only [initV]
      by_cases hap : a' = p
      · subst hap
        rw [if_pos rfl]
        exact baseT_R hkey a' b' R C t k hk
      · rw [if_neg hap]
        have hbp : b' = p := by
          rcases (mem_dom.1 h1).2.2 with h | h
          · exact absurd (Fin.castAdd_injective _ _ h).symm hap
          · exact (Fin.castAdd_injective _ _ h).symm
        subst hbp
        have := baseT_C (cb := cb) (ub := ub) hkey b' a' R C t k hk
        rw [if_neg hap] at this
        exact this
  · rw [ovr, if_neg hc, ← h.2]
    refine baseT_not hkey p R C t (fun b i hi he => hc ?_) fun b i hi he => hc ?_
    · have := key_injective hkey he
      rw [this]
      exact mem_filter.2 ⟨mem_dom.2 ⟨hp, G.Plan.init_mem_seenAt.2 hi, Or.inl rfl⟩, rfl, rfl⟩
    · by_cases hb : b = p
      · rw [if_pos hb] at he
        exact absurd he (key_ne_dkey hkey _ _)
      · rw [if_neg hb] at he
        have := key_injective hkey he
        rw [this]
        exact mem_filter.2 ⟨mem_dom.2 ⟨hp, G.Plan.init_mem_seenAt.2 hi, Or.inr rfl⟩, rfl, rfl⟩

/-- The comparison of the second copies. -/
theorem diag_iff (hub : 0 < ub) {p : Fin (K + K)} {R C : Option S → Fin (K + K) → List Γ}
    (hR : ucount ub (strOf cb fun s => R s p) = n p p) (hC : ucount ub (strOf cb fun s => C s p) = n p p) (t : Tree) :
    (∀ k ∈ (List.finRange U0).filter fun k => k.1 < (n p p).1,
      tget (key (Fin.castAdd A' p, .init p p k)) (baseT ub n key dkey cb p R C t) =
        tget (dkey (p, k)) (baseT ub n key dkey cb p R C t)) ↔
      ∀ k : Fin U0, unitsOf ub (strOf cb fun s => R s p) k = unitsOf ub (strOf cb fun s => C s p) k := by
  constructor
  · intro h k
    by_cases hk : k.1 < (n p p).1
    · have h1 := h k (by simp [hk])
      rw [baseT_R hkey p p R C t k hk] at h1
      have h2 := baseT_C (cb := cb) (ub := ub) hkey p p R C t k hk
      rw [if_pos rfl] at h2
      rw [h2] at h1
      refine G.uwBits_inj ?_ ?_ (ofBits_injective h1)
      · rw [Ne, unitsOf_eq_none]
        omega
      · rw [Ne, unitsOf_eq_none]
        omega
    · rw [unitsOf_eq_none.2 (by omega), unitsOf_eq_none.2 (by omega)]
  · intro h k hk
    have hk' : k.1 < (n p p).1 := by simpa using hk
    have h2 := baseT_C (cb := cb) (ub := ub) hkey p p R C t k hk'
    rw [if_pos rfl] at h2
    rw [h2, baseT_R hkey p p R C t k hk', h k]

end keys

open Classical in
/-- What a base party does with given letters. -/
theorem base_core (hkey : Function.Injective (Sum.elim key dkey)) (hub : 0 < ub) {p : Fin (K + K)}
    (hp : grp (Fin.castAdd A' p) = g) (hρ : ∀ s, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2)
    {wl rl : Option S → List Γ} (hwl : ∀ s, (wl s).length ≤ T) (hrl : ∀ s, (rl s).length ≤ T) {out : Outs S}
    (h1 : ∀ i, out (Fin.castAdd (nT S) i) = ((wl ((tapes S).get i)).map (code cb)).reverse)
    (h2 : ∀ i, out (Fin.natAdd (nT S) i) = ((rl ((tapes S).get i)).map (code cb)).reverse) {t : Tree}
    {σ : Cell M U0 U1 → UW ub} (h : Rep ub key t σ) {Ψ : Tree → A} {Ψ' : (Cell M U0 U1 → UW ub) → A}
    (hΨ : ∀ t' σ', Rep ub key t' σ' → Ψ t' = Ψ' σ') :
    sumL (packSem A (sepOf cb) ub (bodyOf ρ n key dkey p) out t) (fun t' =>
        if ∀ k ∈ (List.finRange U0).filter fun k => k.1 < (n p p).1,
          tget (key (Fin.castAdd A' p, .init p p k)) t' = tget (dkey (p, k)) t' then Ψ t' else 0) =
      ∑ R : Segs S Γ (K + K) T, ∑ C : Segs S Γ (K + K) T,
        if (∀ s, cat (R.words s) = wl s) ∧ (∀ s, cat (C.words s) = rl s) ∧
          InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s p) p R.words C.words then
          Ψ' (ovr ((dom n o grp g).filter fun c => c.1 = Fin.castAdd A' p ∧ isInit c.2 = true)
            (fun c => initV cb ub M.N U0 U1 R.words C.words p c.2) σ) else 0 := by
  have hK : 0 < K + K := Nat.lt_of_le_of_lt (Nat.zero_le _) p.2
  rw [sumL_pack hub hK hρ hwl hrl h1 h2]
  refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun C _ => ?_
  by_cases hc : (∀ s, cat (R.words s) = wl s) ∧ (∀ s, cat (C.words s) = rl s) ∧ (∀ s, RowOk (ρ s p) (R.words s)) ∧
          (∀ b, ucount ub (strOf cb fun s => R.words s b) = n p b) ∧
          (∀ b, ucount ub (strOf cb fun s => C.words s b) = n b p)
  · rw [if_pos hc]
    obtain ⟨c1, c2, c3, c4, c5⟩ := hc
    have hd := diag_iff (cb := cb) hkey hub (c4 p) (c5 p) t
    by_cases hdiag : ∀ k : Fin U0, unitsOf ub (strOf cb fun s => R.words s p) k = unitsOf ub (strOf cb fun s => C.words s p) k
    · refine (if_pos (hd.2 hdiag)).trans ?_
      rw [if_pos ⟨c1, c2, c3, c4, c5, hdiag⟩]
      exact hΨ _ _ (rep_baseT hkey hp R.words C.words h)
    · refine (if_neg fun hh => hdiag (hd.1 hh)).trans ?_
      rw [if_neg (fun hh => hdiag hh.2.2.2.2.2)]
  · rw [if_neg hc, if_neg fun hh => hc ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1⟩]

theorem length_wr (w : List (Letter S Unit Γ)) (s : Option S) : (wr w s).length ≤ w.length := by
  cases s with
  | none => exact Nat.zero_le _
  | some s => exact length_emit_le w _

theorem length_rdr (w : List (Letter S Unit Γ)) (s : Option S) : (rdr w s).length ≤ w.length := by
  cases s with
  | none => exact length_emit_le w _
  | some s => exact length_emit_le w _

theorem emit_eq_vec {m : ℕ} (w : List (Letter S Unit Γ)) (R C : Option S → Fin m → List Γ) :
    ((∀ s, cat (R s) = wr w s) ∧ ∀ s, cat (C s) = rdr w s) ↔ (∀ b, R none b = []) ∧ emit w = vec R C := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨cat_eq_nil.1 (h1 none), funext fun z => ?_⟩
    cases z with
    | tp s b =>
      cases b with
      | false => exact (h1 (some s)).symm
      | true => exact (h2 (some s)).symm
    | inp u => exact (h2 none).symm
  · rintro ⟨h1, h2⟩
    refine ⟨fun s => ?_, fun s => ?_⟩
    · cases s with
      | none => exact cat_eq_nil.2 h1
      | some s => exact (congrFun h2 (.tp s false)).symm
    · cases s with
      | none => exact (congrFun h2 (.inp ())).symm
      | some s => exact (congrFun h2 (.tp s true)).symm

open Classical in
/-- **The step of a base party.** -/
theorem stepOK_base (hkey : Function.Injective (Sum.elim key dkey)) (hub : 0 < ub)
    (hmu : ∀ z q q', ∃ e : WE, e.val θ = mu z q q') (hx : ∀ κ, (x κ).length ≤ T) {p : Fin (K + K)}
    (hp : grp (Fin.castAdd A' p) = g) (hρ : ∀ s, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) :
    StepOK θ T mu cb kinds key (baseIns (fun z => (qn Q z : ℕ)) cb q x ρ n key dkey p)
      (baseStep mu T cb q x ρ n o grp g ub p) := by
  intro t σ Ψ Ψ' hrep hΨ
  -- the right side
  have hR : ∑ ω ∈ (baseStep mu T cb q x ρ n o grp g ub p).Om, (baseStep mu T cb q x ρ n o grp g ub p).w ω σ *
      Ψ' (ovr (baseStep mu T cb q x ρ n o grp g ub p).wr ((baseStep mu T cb q x ρ n o grp g ub p).v ω σ) σ) =
      ∑ R : Segs S Γ (K + K) T, ∑ C : Segs S Γ (K + K) T,
        (if InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s p) p R.words C.words then
          partyW mu T q x p R.words C.words else 0) *
          Ψ' (ovr ((dom n o grp g).filter fun c => c.1 = Fin.castAdd A' p ∧ isInit c.2 = true)
            (fun c => initV cb ub M.N U0 U1 R.words C.words p c.2) σ) := by
    show ∑ ω ∈ (Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T) ×ˢ
      (Fintype.piFinset fun _ : Option S => Fintype.piFinset fun _ : Fin (K + K) => wordsLe Γ T), _ = _
    rw [Finset.sum_product, sum_pi_pi_coe]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [sum_pi_pi_coe]
    rfl
  rw [hR]
  have hB : (fun t' => sumL (scriptSem (S := S) θ mu cb kinds T ub (((List.finRange U0).filter fun k => k.1 < (n p p).1).map
      fun k => Ins.both (key (Fin.castAdd A' p, .init p p k)) (dkey (p, k))) t') Ψ) =
      fun t' => if ∀ k ∈ (List.finRange U0).filter fun k => k.1 < (n p p).1,
        tget (key (Fin.castAdd A' p, .init p p k)) t' = tget (dkey (p, k)) t' then Ψ t' else 0 := by
    funext t'
    rw [sumL_boths]
    by_cases hh : ∀ k ∈ (List.finRange U0).filter fun k => k.1 < (n p p).1,
        tget (key (Fin.castAdd A' p, .init p p k)) t' = tget (dkey (p, k)) t'
    · rw [if_pos hh, if_pos hh]
    · rw [if_neg hh, if_neg hh]
  unfold baseIns
  rw [sumL_script_cons, hB]
  refine Fin.addCases (motive := fun p => grp (Fin.castAdd A' p) = g → (∀ s, (ρ s p).1 = false → (ρ s p).2.1 ≤ (ρ s p).2.2) →
    sumL (insSem θ mu cb kinds T ub (Fin.addCases (motive := fun _ => Ins)
      (fun κ => .block (qn Q (q κ.castSucc)) (qn Q (q κ.succ)) (bodyOf ρ n key dkey (Fin.castAdd K κ)))
      (fun κ => .input ((x κ).map fun a => List.ofFn (cb (some a))).reverse (bodyOf ρ n key dkey (Fin.natAdd K κ))) p) t)
      (fun t' => if ∀ k ∈ (List.finRange U0).filter fun k => k.1 < (n p p).1,
        tget (key (Fin.castAdd A' p, .init p p k)) t' = tget (dkey (p, k)) t' then Ψ t' else 0) =
    ∑ R : Segs S Γ (K + K) T, ∑ C : Segs S Γ (K + K) T,
        (if InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s p) p R.words C.words then
          partyW mu T q x p R.words C.words else 0) *
          Ψ' (ovr ((dom n o grp g).filter fun c => c.1 = Fin.castAdd A' p ∧ isInit c.2 = true)
            (fun c => initV cb ub M.N U0 U1 R.words C.words p c.2) σ)) ?_ ?_ p hp hρ
  · intro κ hp hρ
    rw [Fin.addCases_left, insSem, dif_pos ⟨(qn Q _).2, (qn Q _).2⟩, sumL_bindL, sumL_simSem mu cb hmu]
    have h1 : ∀ w : Fin T → Letter S Unit Γ, sumL (packSem A (sepOf cb) ub (bodyOf ρ n key dkey (Fin.castAdd K κ))
        (outsOf cb (List.ofFn w)) t) (fun t' => if ∀ k ∈ (List.finRange U0).filter fun k =>
          k.1 < (n (Fin.castAdd K κ) (Fin.castAdd K κ)).1, tget (key (Fin.castAdd A' (Fin.castAdd K κ),
          .init (Fin.castAdd K κ) (Fin.castAdd K κ) k)) t' = tget (dkey (Fin.castAdd K κ, k)) t' then Ψ t' else 0) = _ :=
      fun w => base_core (n := n) (o := o) hkey hub hp hρ (T := T) (wl := wr (List.ofFn w)) (rl := rdr (List.ofFn w))
        (fun s => (length_wr _ s).trans (by simp)) (fun s => (length_rdr _ s).trans (by simp))
        (outsOf_left cb _) (outsOf_right cb _) hrep hΨ
    simp only [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [partyW_block, blockW]
    by_cases hi : InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s (Fin.castAdd K κ)) (Fin.castAdd K κ) R.words C.words
    · rw [if_pos hi]
      by_cases hn : ∀ b, R.words none b = []
      · rw [if_pos hn, Finset.sum_mul]
        refine Finset.sum_congr rfl fun w _ => ?_
        have he := emit_eq_vec (List.ofFn w) R.words C.words
        by_cases hw : emit (List.ofFn w) = vec R.words C.words
        · obtain ⟨e1, e2⟩ := he.2 ⟨hn, hw⟩
          rw [if_pos hw, if_pos ⟨e1, e2, hi⟩]
        · rw [if_neg hw, if_neg fun hh => hw (he.1 ⟨hh.1, hh.2.1⟩).2, mul_zero, zero_mul]
      · rw [if_neg hn, zero_mul]
        refine Finset.sum_eq_zero fun w _ => ?_
        rw [if_neg fun hh => hn ((emit_eq_vec (List.ofFn w) R.words C.words).1 ⟨hh.1, hh.2.1⟩).1, mul_zero]
    · rw [if_neg hi, zero_mul]
      refine Finset.sum_eq_zero fun w _ => ?_
      rw [if_neg fun hh => hi hh.2.2, mul_zero]
  · intro κ hp hρ
    rw [Fin.addCases_right, insSem]
    have h1 := base_core (n := n) (o := o) hkey hub hp hρ (T := T) (wl := fun s => if s = none then x κ else []) (rl := fun _ => [])
      (out := inOuts (S := S) ((x κ).map (code cb)).reverse)
      (fun s => by split_ifs; exacts [hx κ, Nat.zero_le _]) (fun s => Nat.zero_le _)
      (fun i => inOuts_left cb (x κ) i) (fun i => inOuts_right cb (x κ) i) hrep hΨ
    refine h1.trans ?_
    refine Finset.sum_congr rfl fun R _ => Finset.sum_congr rfl fun C _ => ?_
    rw [partyW_input]
    have he : ((∀ s, cat (R.words s) = if s = none then x κ else []) ∧ ∀ s, cat (C.words s) = []) ↔
        (∀ s b, R.words (some s) b = []) ∧ (∀ s b, C.words s b = []) ∧ cat (R.words none) = x κ := by
      constructor
      · rintro ⟨a, b⟩
        refine ⟨fun s => cat_eq_nil.1 ?_, fun s => cat_eq_nil.1 (b s), ?_⟩
        · have := a (some s)
          simpa using this
        · have := a none
          simpa using this
      · rintro ⟨a, b, d⟩
        refine ⟨fun s => ?_, fun s => cat_eq_nil.2 (b s)⟩
        cases s with
        | none => simpa using d
        | some s => simpa using cat_eq_nil.2 (a s)
    by_cases hi : InitC cb ub U0 (fun a b => (n a b).1) (fun s => ρ s (Fin.natAdd K κ)) (Fin.natAdd K κ) R.words C.words
    · rw [if_pos hi]
      by_cases hw : (∀ s b, R.words (some s) b = []) ∧ (∀ s b, C.words s b = []) ∧ cat (R.words none) = x κ
      · rw [if_pos hw, if_pos ⟨(he.2 hw).1, (he.2 hw).2, hi⟩, one_mul]
      · rw [if_neg hw, if_neg fun hh => hw (he.1 ⟨hh.1, hh.2.1⟩), zero_mul]
    · rw [if_neg hi, if_neg fun hh => hi hh.2.2, zero_mul]

end Nc.Grp
