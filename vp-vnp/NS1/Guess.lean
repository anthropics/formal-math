/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Postpone

/-!
# Guessing the budgets and multiplying by the powers of the constants
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R]

namespace KT

/-- The constants `c, c², c⁴, …` (`n` of them); the names are `0, 10, 110, …`. -/
def comb (c : R) : ℕ → KT R
  | 0 => none
  | n + 1 => node (leaf c) (comb (c ^ 2) n)

/-- The powers `c ^ (2 ^ b)`, `b < B`, of all constants. -/
def expand (B : ℕ) : KT R → KT R
  | none => none
  | leaf c => comb c B
  | node l r => node (l.expand B) (r.expand B)

/-- The power of `c` that has a given name. -/
def combVal (c : R) : List Bool → R
  | [] => 0
  | [false] => c
  | false :: _ :: _ => 0
  | true :: p => combVal (c ^ 2) p

/-- The constant with a given name: `l ++ 1^b ++ 0` names the power `2 ^ b` of the constant with the name `l`. -/
def lk : KT R → List Bool → R
  | none, _ => 0
  | leaf c, p => combVal c p
  | node _ _, [] => 0
  | node _ r, true :: p => r.lk p
  | node l _, false :: p => l.lk p

/-- The name of the power `2 ^ b`. -/
def pw (b : ℕ) : List Bool := List.replicate b true ++ [false]

/-- Names of powers `2 ^ b`, `b < B`, of the constants. -/
def InB (B : ℕ) : KT R → List Bool → Prop
  | none, _ => False
  | leaf _, p => ∃ b < B, p = pw b
  | node _ _, [] => False
  | node _ r, true :: p => r.InB B p
  | node l _, false :: p => l.InB B p

/-- Names of the constants. -/
def Leaf : KT R → List Bool → Prop
  | none, _ => False
  | leaf _, p => p = []
  | node _ _, [] => False
  | node _ r, true :: p => r.Leaf p
  | node l _, false :: p => l.Leaf p

theorem Leaf.inB {K : KT R} {p : List Bool} (h : K.Leaf p) {b B : ℕ} (hb : b < B) : K.InB B (p ++ pw b) := by
  induction K generalizing p with
  | none => exact h.elim
  | leaf c =>
    have h : p = [] := h
    subst h
    exact ⟨b, hb, rfl⟩
  | node l r ihl ihr =>
    cases p with
    | nil => exact h.elim
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem pw_succ (b : ℕ) : pw (b + 1) = true :: pw b := rfl

theorem combVal_pw (c : R) (b : ℕ) : combVal c (pw b) = c ^ 2 ^ b := by
  induction b generalizing c with
  | zero => simp [pw, combVal]
  | succ b ih => rw [pw_succ, combVal, ih, ← pow_mul, pow_succ' 2 b]

theorem Leaf.lk {K : KT R} {p : List Bool} (h : K.Leaf p) : ∃ c, ∀ i, K.lk (p ++ pw i) = c ^ 2 ^ i := by
  induction K generalizing p with
  | none => exact h.elim
  | leaf c =>
    have h : p = [] := h
    subst h
    exact ⟨c, fun i => combVal_pw c i⟩
  | node l r ihl ihr =>
    cases p with
    | nil => exact h.elim
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem lookup_comb (c : R) {B b : ℕ} (h : b < B) : (comb c B).lookup (pw b) = combVal c (pw b) := by
  induction b generalizing c B with
  | zero =>
    cases B with
    | zero => omega
    | succ B => rfl
  | succ b ih =>
    cases B with
    | zero => omega
    | succ B =>
      rw [pw_succ, comb, lookup, combVal]
      exact ih _ (by omega)

theorem lookup_expand {B : ℕ} {K : KT R} {p : List Bool} (h : K.InB B p) : K.lk p = (K.expand B).lookup p := by
  induction K generalizing p with
  | none => exact h.elim
  | leaf c =>
    obtain ⟨b, hb, rfl⟩ := h
    rw [expand, lookup_comb c hb, lk]
  | node l r ihl ihr =>
    cases p with
    | nil => exact h.elim
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem InB.mono {B B' : ℕ} (hB : B ≤ B') {K : KT R} {p : List Bool} (h : K.InB B p) : K.InB B' p := by
  induction K generalizing p with
  | none => exact h
  | leaf c =>
    obtain ⟨b, hb, rfl⟩ := h
    exact ⟨b, lt_of_lt_of_le hb hB, rfl⟩
  | node l r ihl ihr =>
    cases p with
    | nil => exact h
    | cons a p =>
      cases a with
      | true => exact ihr h
      | false => exact ihl h

theorem nds_comb (c : R) (n : ℕ) : (comb c n).nds = 2 * n + 1 := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [comb, nds, ih]; omega

theorem nds_pos (K : KT R) : 0 < K.nds := by cases K <;> simp [nds]

theorem nds_expand (B : ℕ) (K : KT R) : (K.expand B).nds ≤ K.nds * (2 * B + 1) := by
  induction K with
  | none => simp [expand, nds]
  | leaf c => simp [expand, nds, nds_comb]
  | node l r ihl ihr =>
    simp only [expand, nds]
    nlinarith

theorem ht_comb (c : R) (n : ℕ) : (comb c n).ht ≤ n := by
  induction n generalizing c with
  | zero => exact le_rfl
  | succ n ih =>
    have := ih (c ^ 2)
    simp only [comb, ht]
    omega

theorem ht_expand (B : ℕ) (K : KT R) : (K.expand B).ht ≤ K.ht + B := by
  induction K with
  | none => simp [expand, ht]
  | leaf c =>
    have := ht_comb c B
    simp only [expand, ht]
    omega
  | node l r ihl ihr =>
    simp only [expand, ht]
    omega

theorem length_words {J : ℕ} {w : List Bool} (h : w ∈ words J) : w.length = J := by
  induction J generalizing w with
  | zero => simp [words] at h; simp [h]
  | succ J ih =>
    simp only [words, List.mem_flatMap, List.mem_map] at h
    obtain ⟨b, -, v, hv, rfl⟩ := h
    simp [ih hv]

theorem ht_budg {J : ℕ} {K : KT R} {q : Bt × R} (h : q ∈ K.budg J) : q.1.ht ≤ K.ht + J + 1 := by
  induction K generalizing q with
  | none =>
    simp only [budg, List.mem_singleton] at h
    subst h
    simp [Bt.ht]
  | leaf c =>
    simp only [budg, List.mem_map] at h
    obtain ⟨w, hw, rfl⟩ := h
    simp [Bt.ht, length_words hw, ht]
  | node l r ihl ihr =>
    simp only [budg, List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hp, q', hq, rfl⟩ := h
    have h1 := ihl hp
    have h2 := ihr hq
    simp only [Bt.ht, ht]
    omega

theorem nds_budg {J : ℕ} {K : KT R} {q : Bt × R} (h : q ∈ K.budg J) : q.1.nds ≤ K.nds * (J + 1) := by
  induction K generalizing q with
  | none =>
    simp only [budg, List.mem_singleton] at h
    subst h
    simp [Bt.nds, nds]
  | leaf c =>
    simp only [budg, List.mem_map] at h
    obtain ⟨w, hw, rfl⟩ := h
    simp [Bt.nds, length_words hw, nds]
  | node l r ihl ihr =>
    simp only [budg, List.mem_flatMap, List.mem_map] at h
    obtain ⟨p, hp, q', hq, rfl⟩ := h
    have h1 := ihl hp
    have h2 := ihr hq
    simp only [Bt.nds, nds]
    nlinarith

end KT

section Formulas

/-- Guess a bit; if it is 1, multiply by the constant with the name `p`. -/
def gbit (p : List Bool) : Fm := .ite .guess (.cons (.mul (.quote (ofBits p))) (.quote .nil)) (.quote .nil)

theorem gbit_ev (p : List Bool) (x : Tree) : Ev θ (gbit p) x [⟨3, 1, [], .nil⟩, ⟨6, 1, [p], one⟩] := by
  have h1 : Ev θ (.cons (.mul (.quote (ofBits p))) (.quote .nil)) x [⟨4, 1, [p], one⟩] := by
    have := Ev.cons (Ev.mul (Ev.quote (θ := θ) (ofBits p) x)) (Ev.quote .nil x)
    simpa [Run.det, Run.seq, Run.tick, one] using this
  have := Ev.ite (L := fun r => if r.out = .nil then [.det 1 .nil] else [⟨4, 1, [p], one⟩]) (Ev.guess (θ := θ) x)
    (b := .cons (.mul (.quote (ofBits p))) (.quote .nil)) (c := .quote .nil)
    (fun r _ h => by rw [if_neg h]; exact h1) (fun r _ h => by rw [if_pos h]; exact Ev.quote .nil x)
  simpa [Run.det, Run.seq, Run.tick, one, gbit] using this

/-- Guess the digits of a number; multiply by the powers of a constant. `ν i` is the exponent in the name that is
used for the power `2 ^ i`. -/
def gw (ν : ℕ → ℕ) (pre : List Bool) (b : ℕ) : ℕ → ℕ → Fm
  | _, 0 => .quote .nil
  | j, n + 1 => .cons (gbit (pre ++ KT.pw (ν (b + j)))) (gw ν pre b (j + 1) n)

/-- The budgets of the powers of a constant. -/
def gcomb (ν : ℕ → ℕ) (J : ℕ) (pre : List Bool) : ℕ → ℕ → Fm
  | _, 0 => .quote .nil
  | b, n + 1 => .cons (.cons (.cons (.quote .nil) (gw ν pre b 0 J)) (gcomb ν J pre (b + 1) n)) (.quote .nil)

/-- The budgets of all powers `2 ^ b`, `b < B`, of all constants. -/
def gt (ν : ℕ → ℕ) (J B : ℕ) : KT R → List Bool → Fm
  | .none, _ => .quote .nil
  | .leaf _, pre => gcomb ν J pre 0 B
  | .node l r, pre => .cons (.cons (gt ν J B l (pre ++ [false])) (gt ν J B r (pre ++ [true]))) (.quote .nil)

/-- A run that guesses a budget and multiplies by the powers of the constants. -/
structure RelG (κ : List Bool → R) (P : List Bool → Prop) (c : ℕ) (r : Run A) (q : Bt × R) : Prop where
  th : r.th = 1
  out : r.out = q.1.enc
  bill : (r.bill.map κ).prod = q.2
  names : ∀ p ∈ r.bill, P p
  cost : r.cost ≤ c

variable {κ : List Bool → R} {P : List Bool → Prop} {ν : ℕ → ℕ}

theorem gw_ev {pre : List Bool} {b : ℕ} {c : R} (x : Tree) {n j : ℕ}
    (h : ∀ i < j + n, κ (pre ++ KT.pw (ν (b + i))) = c ^ 2 ^ (b + i) ∧ P (pre ++ KT.pw (ν (b + i)))) :
    ∃ l, Ev θ (gw ν pre b j n) x l ∧ List.Forall₂ (fun r w => r.th = 1 ∧ r.out = ofBits w ∧
      (r.bill.map κ).prod = (c ^ 2 ^ (b + j)) ^ KT.val w ∧ (∀ p ∈ r.bill, P p) ∧ r.cost ≤ 8 * n + 1) l (KT.words n) := by
  induction n generalizing j with
  | zero => exact ⟨_, .quote .nil x, .cons ⟨rfl, rfl, by simp [Run.det, KT.val], by simp [Run.det], by simp [Run.det]⟩ .nil⟩
  | succ n ih =>
    obtain ⟨l, e, hl⟩ := ih (j := j + 1) (fun i hi => h i (by omega))
    obtain ⟨hκ, hP⟩ := h j (by omega)
    refine ⟨_, Ev.cons (gbit_ev _ x) e, ?_⟩
    simp only [KT.words, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine List.rel_append ?_ ?_
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine hl.imp fun r w hr => ?_
      obtain ⟨h1, h2, h3, h4, h5⟩ := hr
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [Run.seq, Run.tick, h1]
      · simp [Run.seq, Run.tick, h2, ofBits, bit]
      · simp only [Run.seq, Run.tick, List.nil_append, h3, KT.val, Bool.false_eq_true, if_false, zero_add, ← pow_mul]
        congr 1
        rw [← add_assoc, pow_succ]
        ring
      · simpa [Run.seq, Run.tick] using h4
      · simp only [Run.seq, Run.tick]
        omega
    · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine hl.imp fun r w hr => ?_
      obtain ⟨h1, h2, h3, h4, h5⟩ := hr
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [Run.seq, Run.tick, h1]
      · simp [Run.seq, Run.tick, h2, ofBits, bit]
      · simp only [Run.seq, Run.tick, List.singleton_append, List.map_cons, List.prod_cons, h3, hκ, KT.val, if_true,
          ← pow_mul, ← pow_add]
        congr 1
        rw [← add_assoc, pow_succ]
        ring
      · intro p hp
        simp only [Run.seq, Run.tick, List.singleton_append, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact hP
        · exact h4 p hp
      · simp only [Run.seq, Run.tick]
        omega

theorem node_rel {f g : Fm} {x : Tree} {lf lg : List (Run A)} {Qf Qg : List (Bt × R)} {cf cg : ℕ}
    (hf : Ev θ f x lf) (hg : Ev θ g x lg) (rf : List.Forall₂ (RelG κ P cf) lf Qf)
    (rg : List.Forall₂ (RelG κ P cg) lg Qg) : ∃ l, Ev θ (.cons (.cons f g) (.quote .nil)) x l ∧
      List.Forall₂ (RelG κ P (cf + cg + 3)) l
        (Qf.flatMap fun p => Qg.map fun q => (Bt.node p.1 q.1, p.2 * q.2)) := by
  refine ⟨_, Ev.cons (Ev.cons hf hg) (Ev.quote .nil x), ?_⟩
  rw [List.flatMap_assoc]
  refine forall₂_flatMap rf fun r _ p _ hr => ?_
  have e : ((lg.map fun s => (r.seq s).tick (.cons r.out s.out)).flatMap fun u =>
      [Run.det 1 Tree.nil].map fun s => (u.seq s).tick (.cons u.out s.out)) =
      lg.map fun s => ((r.seq s).tick (.cons r.out s.out)).seq (.det 1 .nil) |>.tick (.cons (.cons r.out s.out) .nil) := by
    rw [List.flatMap_map]
    simp only [List.map_cons, List.map_nil]
    exact flatMap_single _ _
  rw [e, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine rg.imp fun s q hs => ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Run.seq, Run.tick, Run.det, hr.th, hs.th]
  · simp [Run.tick, hr.out, hs.out, Bt.enc]
  · simp [Run.seq, Run.tick, Run.det, hr.bill, hs.bill]
  · intro p hp
    simp only [Run.seq, Run.tick, Run.det, List.append_nil, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hr.names p hp
    · exact hs.names p hp
  · have h1 := hr.cost
    have h2 := hs.cost
    simp only [Run.seq, Run.tick, Run.det]
    omega

theorem gcomb_ev {J : ℕ} {pre : List Bool} {c : R} (x : Tree) {n b : ℕ}
    (h : ∀ i < b + n + J, κ (pre ++ KT.pw (ν i)) = c ^ 2 ^ i ∧ P (pre ++ KT.pw (ν i))) :
    ∃ l, Ev θ (gcomb ν J pre b n) x l ∧
      List.Forall₂ (RelG κ P ((8 * J + 10) * n + 1)) l ((KT.comb (c ^ 2 ^ b) n).budg J) := by
  induction n generalizing b with
  | zero =>
    refine ⟨_, .quote .nil x, .cons ⟨rfl, rfl, ?_, ?_, ?_⟩ .nil⟩ <;> simp [Run.det]
  | succ n ih =>
    obtain ⟨lg, eg, rg⟩ := ih (b := b + 1) (fun i hi => h i (by omega))
    obtain ⟨lw, ew, rw'⟩ := gw_ev (θ := θ) (κ := κ) (P := P) (ν := ν) (pre := pre) (b := b) (c := c) x (n := J) (j := 0)
      (fun i hi => h (b + i) (by omega))
    have ef := Ev.cons (Ev.quote (θ := θ) .nil x) ew
    have rf : List.Forall₂ (RelG κ P (8 * J + 3)) ([Run.det 1 Tree.nil].flatMap fun r => lw.map fun s =>
        (r.seq s).tick (.cons r.out s.out)) ((KT.leaf (c ^ 2 ^ b)).budg J) := by
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, KT.budg]
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      refine rw'.imp fun r w hr => ?_
      obtain ⟨h1, h2, h3, h4, h5⟩ := hr
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [Run.seq, Run.tick, Run.det, h1]
      · simp [Run.tick, Run.det, h2, Bt.enc]
      · simpa [Run.seq, Run.tick, Run.det] using h3
      · simpa [Run.seq, Run.tick, Run.det] using h4
      · simp only [Run.seq, Run.tick, Run.det]
        omega
    obtain ⟨l, e, r⟩ := node_rel ef eg rf rg
    refine ⟨l, e, ?_⟩
    have hc : (c ^ 2 ^ b) ^ 2 = c ^ 2 ^ (b + 1) := by rw [← pow_mul, ← pow_succ]
    simp only [KT.comb, KT.budg, hc] at r ⊢
    refine r.imp fun s q hs => ⟨hs.th, hs.out, hs.bill, hs.names, hs.cost.trans ?_⟩
    ring_nf
    omega

/-- Runs of `gt` = budgets. The hypothesis: the names that are used name the right powers. -/
theorem gt_ev {J B : ℕ} (x : Tree) (K : KT R) (pre : List Bool)
    (h : ∀ p, K.Leaf p → ∀ i < B + J,
      κ (pre ++ (p ++ KT.pw (ν i))) = K.lk (p ++ KT.pw i) ∧ P (pre ++ (p ++ KT.pw (ν i)))) :
    ∃ l, Ev θ (gt ν J B K pre) x l ∧
      List.Forall₂ (RelG κ P ((8 * J + 10) * (K.expand B).nds)) l ((K.expand B).budg J) := by
  induction K generalizing pre with
  | none =>
    refine ⟨_, .quote .nil x, .cons ⟨rfl, rfl, ?_, ?_, ?_⟩ .nil⟩
    · simp [Run.det]
    · simp [Run.det]
    · simp [Run.det, KT.expand, KT.nds]
  | leaf c =>
    have h' : ∀ i < B + J, κ (pre ++ KT.pw (ν i)) = c ^ 2 ^ i ∧ P (pre ++ KT.pw (ν i)) := by
      intro i hi
      have := h [] rfl i hi
      simpa [KT.lk, KT.combVal_pw] using this
    obtain ⟨l, e, r⟩ := gcomb_ev (θ := θ) (J := J) (pre := pre) (c := c) x (n := B) (b := 0)
      (fun i hi => h' i (by omega))
    refine ⟨l, e, ?_⟩
    simp only [pow_zero, pow_one] at r
    refine r.imp fun s q hs => ⟨hs.th, hs.out, hs.bill, hs.names, hs.cost.trans ?_⟩
    simp only [KT.expand, KT.nds_comb]
    nlinarith
  | node l r ihl ihr =>
    obtain ⟨ll, el, rl⟩ := ihl (pre ++ [false]) (fun p hp i hi => by
      have := h (false :: p) hp i hi
      simpa [KT.lk] using this)
    obtain ⟨lr, er, rr⟩ := ihr (pre ++ [true]) (fun p hp i hi => by
      have := h (true :: p) hp i hi
      simpa [KT.lk] using this)
    obtain ⟨l', e', r'⟩ := node_rel el er rl rr
    refine ⟨l', e', r'.imp fun s q hs => ⟨hs.th, hs.out, hs.bill, hs.names, hs.cost.trans ?_⟩⟩
    simp only [KT.expand, KT.nds]
    nlinarith

end Formulas

section Sizes

theorem size_num (k : ℕ) : (num k).size = 2 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [num, Tree.size, ih]; omega

theorem size_gw (ν : ℕ → ℕ) (pre : List Bool) (b N : ℕ) (n j : ℕ) (h : ∀ i < j + n, ν (b + i) ≤ N) :
    (gw ν pre b j n).code.size ≤ n * (4 * (pre.length + N) + 100) + 4 := by
  induction n generalizing j with
  | zero => simp [gw, Fm.code, Tree.size, size_num]
  | succ n ih =>
    have h1 := ih (j + 1) (fun i hi => h i (by omega))
    have h2 := size_ofBits (pre ++ KT.pw (ν (b + j)))
    have h3 := h j (by omega)
    simp only [KT.pw, List.length_append, List.length_replicate, List.length_singleton] at h2
    simp only [gw, gbit, Fm.code, Tree.size, size_num, KT.pw]
    nlinarith

theorem size_gcomb (ν : ℕ → ℕ) (J : ℕ) (pre : List Bool) (N : ℕ) (n b : ℕ) (h : ∀ i < b + n + J, ν i ≤ N) :
    (gcomb ν J pre b n).code.size ≤ n * ((J + 1) * (4 * (pre.length + N) + 100)) + 4 := by
  induction n generalizing b with
  | zero => simp [gcomb, Fm.code, Tree.size, size_num]
  | succ n ih =>
    have h1 := ih (b + 1) (fun i hi => h i (by omega))
    have h2 := size_gw ν pre b N J 0 (fun i hi => h _ (by omega))
    simp only [gcomb, Fm.code, Tree.size, size_num]
    nlinarith

theorem size_gt (ν : ℕ → ℕ) (J B : ℕ) (K : KT R) (pre : List Bool) (N : ℕ) (h : ∀ i < B + J, ν i ≤ N) :
    (gt ν J B K pre).code.size ≤ (K.expand B).nds * ((J + 1) * (4 * (pre.length + K.ht + N) + 100)) := by
  induction K generalizing pre with
  | none =>
    simp only [gt, Fm.code, Tree.size, size_num, KT.expand, KT.nds, KT.ht]
    nlinarith
  | leaf c =>
    have h1 := size_gcomb ν J pre N B 0 (fun i hi => h i (by omega))
    simp only [gt, KT.expand, KT.nds_comb, KT.ht, add_zero] at h1 ⊢
    refine h1.trans ?_
    have : 100 ≤ (J + 1) * (4 * (pre.length + N) + 100) := by nlinarith
    nlinarith
  | node l r ihl ihr =>
    have h1 := ihl (pre ++ [false])
    have h2 := ihr (pre ++ [true])
    simp only [List.length_append, List.length_singleton] at h1 h2
    simp only [gt, Fm.code, Tree.size, size_num, KT.expand, KT.nds, KT.ht]
    have e1 : (J + 1) * (4 * (pre.length + 1 + l.ht + N) + 100) ≤
        (J + 1) * (4 * (pre.length + (max l.ht r.ht + 1) + N) + 100) := by
      apply Nat.mul_le_mul_left
      have := le_max_left l.ht r.ht
      omega
    have e2 : (J + 1) * (4 * (pre.length + 1 + r.ht + N) + 100) ≤
        (J + 1) * (4 * (pre.length + (max l.ht r.ht + 1) + N) + 100) := by
      apply Nat.mul_le_mul_left
      have := le_max_right l.ht r.ht
      omega
    have e3 : 100 ≤ (J + 1) * (4 * (pre.length + (max l.ht r.ht + 1) + N) + 100) := by nlinarith
    have e4 := h1.trans (Nat.mul_le_mul_left _ e1)
    have e5 := h2.trans (Nat.mul_le_mul_left _ e2)
    nlinarith

end Sizes

end NS1
