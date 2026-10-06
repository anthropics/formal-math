/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Assigns
public import ThreeSumApsp.Lang.Rules

/-!
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The list of the locals -/

/-- The list of the locals after an assignment of z to local x.  A list that is too short is filled
up with zeros. -/
@[simp] def setLocal : List ℤ → ℕ → ℤ → List ℤ
  | [], 0, z => [z]
  | [], x + 1, z => 0 :: setLocal [] x z
  | _ :: l, 0, z => z :: l
  | a :: l, x + 1, z => a :: setLocal l x z

/-- Reading a local after an assignment. -/
theorem frame_setLocal : ∀ (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ),
    frame (setLocal l x z) y = if y = x then z else frame l y
  | [], 0, z, 0 => by simp
  | [], 0, z, y + 1 => by simp
  | [], x + 1, z, 0 => by simp
  | [], x + 1, z, y + 1 => by simpa using frame_setLocal [] x z y
  | a :: l, 0, z, 0 => by simp
  | a :: l, 0, z, y + 1 => by simp
  | a :: l, x + 1, z, 0 => by simp
  | a :: l, x + 1, z, y + 1 => by simpa using frame_setLocal l x z y

/-- An assignment to a local, in terms of the list. -/
theorem update_frame_setLocal (l : List ℤ) (x : ℕ) (z : ℤ) :
    Function.update (frame l) x z = frame (setLocal l x z) := by
  funext y
  rw [frame_setLocal, Function.update_apply]

/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : frame (l ++ List.replicate n 0) = frame l := by
  funext y
  simp only [frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

/-! ## The value of an expression -/

/-- The evaluation of e in σ stays within the limits and gives z. -/
@[simp] def Expr.Gives (lim : Limits) (σ : State) (e : Expr) (z : ℤ) : Prop :=
  e.Safe lim σ ∧ e.val σ = z

/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}

/-- `x := e`, where e gives z, for locals that are not given as a list. -/
theorem Ends.setVal {loc : ℕ → ℤ} {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨Function.update loc x z, μ⟩)
    (he : e.Gives lim ⟨loc, μ⟩ z := by light_side) (hT : e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.set x e) ⟨loc, μ⟩ T Q :=
  Ends.set he.1 hT (he.2 ▸ h)

/-- `x := e ; s`, where e gives z, for locals that are not given as a list. -/
theorem Ends.setValThen {loc : ℕ → ℤ} {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨Function.update loc x z, μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨loc, μ⟩ z := by light_side) (hT : e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.set x e ;; s) ⟨loc, μ⟩ T Q :=
  Ends.next _ (Ends.setVal z h he le_rfl) hT

/-- `x := e`, where e gives z. -/
theorem Ends.setTo {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨frame (setLocal l x z), μ⟩)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by light_side)
    (hT : e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.set x e) ⟨frame l, μ⟩ T Q := by
  refine Ends.set he.1 hT ?_
  rw [he.2]
  simp only [update_frame_setLocal]
  exact h

/-- `x := e ; s`, where e gives z.  The rest s of the text gets the steps that are left. -/
theorem Ends.setToThen {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨frame (setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by light_side)
    (hT : e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.set x e ;; s) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.setTo z h he le_rfl) hT

/-- `mem[a] := e`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeTo {a e : Expr} (b : ℕ) (z : ℤ) (h : Q ⟨frame l, Function.update μ b z⟩)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      light_side)
    (hT : a.cost + e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.store a e) ⟨frame l, μ⟩ T Q := by
  obtain ⟨⟨ha, hav⟩, ⟨he, hev⟩, hb⟩ := he
  refine Ends.store ha he ?_ hT ?_
  · rw [hav]
    exact ⟨Int.natCast_nonneg b, by exact_mod_cast hb⟩
  · rw [hav, hev, Int.toNat_natCast]
    exact h

/-- `mem[a] := e ; s`, where a gives the address b, which lies in the memory, and e gives z. -/
theorem Ends.storeToThen {a e : Expr} {s : Stmt} (b : ℕ) (z : ℤ)
    (h : Ends lim P d s ⟨frame l, Function.update μ b z⟩ (T - (a.cost + e.cost + 1)) Q)
    (he : a.Gives lim ⟨frame l, μ⟩ b ∧ e.Gives lim ⟨frame l, μ⟩ z ∧ b < lim.space := by
      light_side)
    (hT : a.cost + e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.store a e ;; s) ⟨frame l, μ⟩ T Q :=
  Ends.next _ (Ends.storeTo b z h he le_rfl) hT

/-- **Counting loops whose body is a block that changes no local variable**, with the locals as a
list.  Before round j the locals are the given ones with j in the counter, and I j holds of the
memory.  The bound hi gives n, and n fits in a word.  The round is a goal about the body, for the
rules of this file, and its time is body.blockCost, so that no number is typed.  A loop or a call
counts 0 steps in blockCost; for a body that contains one use Ends.forShape. -/
theorem Ends.forFrame {i : ℕ} {hi : Expr} {body : Stmt} (I : ℕ → (ℕ → ℤ) → Prop) (n : ℕ)
    (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨frame (setLocal l i j), μ'⟩ body.blockCost fun σ' =>
        σ'.loc = frame (setLocal l i j) ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨frame (setLocal l i n), μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Gives lim ⟨frame (setLocal l i j), μ'⟩ n := by intros; light_side)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + body.blockCost + 7) + hi.cost + 5 ≤ T := by light_time) :
    Ends lim P d (Stmt.for i hi body) ⟨frame l, μ⟩ T Q := by
  refine Ends.forMem I n body.blockCost start ?_ ?_ ?_ hn hT
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact round j μ' hj hI
  · intro μ' hI
    rw [update_frame_setLocal]
    exact done μ' hI
  · intro j μ' hj hI
    rw [update_frame_setLocal]
    exact bound j μ' hj hI

/-- **Counting loops whose body may change scratch variables.**  S j s μ' is the state before round
j, with the values s of the scratch variables and the memory μ'; I j holds of the memory.  The
counter of S j s μ' holds j, and S (j + 1) s μ' is S j s μ' with the counter increased; for a shape
fun j s μ' => ⟨frame [.., j, s], μ'⟩ both are proved by default.  The bound hi gives n, n fits in a
word, and the body keeps the shape and takes at most b steps. -/
theorem Ends.forShape {β : Type} {loc : ℕ → ℤ} {i : ℕ} {hi : Expr} {body : Stmt}
    (S : ℕ → β → (ℕ → ℤ) → State) (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (s₀ : β) (start : I 0 μ)
    (round : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body (S j s μ') b fun σ' => ∃ s' μ'', σ' = S j s' μ'' ∧ I (j + 1) μ'')
    (done : ∀ (s : β) (μ' : ℕ → ℤ), I n μ' → Q (S n s μ'))
    (first : (⟨Function.update loc i 0, μ⟩ : State) = S 0 s₀ μ := by
      first | (simp only [update_frame_setLocal]; rfl) | simp [update_frame_setLocal])
    (bound : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), j ≤ n → I j μ' → hi.Gives lim (S j s μ') n := by
      intros; light_side)
    (counter : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ), (S j s μ').loc i = j := by intros; simp)
    (next : ∀ (j : ℕ) (s : β) (μ' : ℕ → ℤ),
      (⟨Function.update (S j s μ').loc i ((j : ℤ) + 1), (S j s μ').mem⟩ : State) =
        S (j + 1) s μ' := by
      intros; first | (simp only [update_frame_setLocal]; rfl) | simp [update_frame_setLocal])
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by light_time) :
    Ends lim P d (Stmt.for i hi body) ⟨loc, μ⟩ T Q := by
  refine Ends.for (fun j σ' => ∃ s μ', σ' = S j s μ' ∧ I j μ') n b ⟨s₀, μ, first, start⟩ ?_ ?_ ?_
    hn hT
  · rintro j _ hj - ⟨s, μ', rfl, hI⟩
    refine (round j s μ' hj hI).mono le_rfl ?_
    rintro _ ⟨s', μ'', rfl, hI'⟩
    exact ⟨counter j s' μ'', s', μ'', next j s' μ'', hI'⟩
  · rintro _ - ⟨s, μ', rfl, hI⟩
    exact done s μ' hI
  · rintro j _ hj - ⟨s, μ', rfl, hI⟩
    exact bound j s μ' hj hI

end rules

/-! ## Locals by name, and locals whose values do not matter -/

/-- The list of the locals after several assignments, each given as a local and its value. -/
@[simp] def setLocals (l : List ℤ) : List (ℕ × ℤ) → List ℤ
  | [] => l
  | p :: ps => setLocals (setLocal l p.1 p.2) ps

/-- The local variables after several assignments, each given as a local and its value. -/
@[simp] def updateLocals (loc : ℕ → ℤ) : List (ℕ × ℤ) → ℕ → ℤ
  | [] => loc
  | p :: ps => updateLocals (Function.update loc p.1 p.2) ps

/-- Several assignments, in terms of the list. -/
theorem updateLocals_frame : ∀ (ps : List (ℕ × ℤ)) (l : List ℤ),
    updateLocals (frame l) ps = frame (setLocals l ps)
  | [], _ => rfl
  | p :: ps, l => by
    rw [updateLocals, update_frame_setLocal, updateLocals_frame ps, setLocals]

/-- The list `l` of the locals, with the entries `xs` read from `loc`. -/
@[simp] def refreshLocals (l : List ℤ) (loc : ℕ → ℤ) : List ℕ → List ℤ
  | [] => l
  | x :: xs => refreshLocals (setLocal l x (loc x)) loc xs

/-- Reading a local of `refreshLocals l loc xs`. -/
theorem frame_refreshLocals (loc : ℕ → ℤ) (y : ℕ) : ∀ (xs : List ℕ) (l : List ℤ),
    frame (refreshLocals l loc xs) y = if y ∈ xs then loc y else frame l y
  | [], l => by simp
  | x :: xs, l => by
    rw [refreshLocals, frame_refreshLocals loc y xs, frame_setLocal]
    by_cases hx : y = x
    · subst hx
      simp
    · simp [hx]

/-- Two lists give the same local variables: they are equal up to zeros at the end. -/
def SameFrame (l m : List ℤ) : Prop := frame l = frame m

/-- The empty list gives the same locals as itself. -/
@[simp] theorem sameFrame_nil : SameFrame [] [] := rfl

/-- Two lists give the same locals if their heads are equal and their tails give the same locals. -/
@[simp] theorem sameFrame_cons_cons {a b : ℤ} {l m : List ℤ} :
    SameFrame (a :: l) (b :: m) ↔ a = b ∧ SameFrame l m :=
  ⟨fun h => ⟨congrFun h 0, funext fun i => congrFun h (i + 1)⟩, fun h => funext fun i => by
    cases i with
    | zero => exact h.1
    | succ i => exact congrFun h.2 i⟩

/-- A list gives the same locals as the empty list if all its entries are 0. -/
@[simp] theorem sameFrame_cons_nil {a : ℤ} {l : List ℤ} :
    SameFrame (a :: l) [] ↔ a = 0 ∧ SameFrame l [] :=
  ⟨fun h => ⟨congrFun h 0, funext fun i => congrFun h (i + 1)⟩, fun h => funext fun i => by
    cases i with
    | zero => exact h.1
    | succ i => exact congrFun h.2 i⟩

/-- The empty list gives the same locals as a list all of whose entries are 0. -/
@[simp] theorem sameFrame_nil_cons {b : ℤ} {m : List ℤ} :
    SameFrame [] (b :: m) ↔ b = 0 ∧ SameFrame [] m :=
  ⟨fun h => ⟨(congrFun h 0).symm, funext fun i => congrFun h (i + 1)⟩, fun h => funext fun i => by
    cases i with
    | zero => exact h.1.symm
    | succ i => exact congrFun h.2 i⟩

/-- The local variables `loc` are those of the list `l`, except perhaps the locals `xs`. -/
def LocalsBut (xs : List ℕ) (l : List ℤ) (loc : ℕ → ℤ) : Prop :=
  ∀ y ∉ xs, loc y = frame l y

section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}

/-- Locals that agree with a list except at `xs` are themselves given by a list. -/
theorem LocalsBut.eq_frame (h : LocalsBut xs l loc) : loc = frame (refreshLocals l loc xs) := by
  funext y
  rw [frame_refreshLocals]
  split_ifs with hy
  · rfl
  · exact h y hy

/-- An assignment, on both sides. -/
theorem LocalsBut.update (h : LocalsBut xs l loc) (x : ℕ) (z : ℤ) :
    LocalsBut xs (setLocal l x z) (Function.update loc x z) := by
  intro y hy
  rw [frame_setLocal, Function.update_apply, h y hy]

/-- Two lists agree except at `xs` if they give the same locals once these entries are copied.  For
two lists that are written out, the hypothesis amounts to the equations between their entries, where
an entry that is missing counts as 0. -/
theorem LocalsBut.of_eq (h : SameFrame (refreshLocals l (frame l') xs) l') :
    LocalsBut xs l (frame l') := by
  intro y hy
  have hread := frame_refreshLocals (frame l') y xs l
  rw [h, if_neg hy] at hread
  exact hread

/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : Stmt} {Q R : State → Prop}

/-- **From locals that are described by `LocalsBut` to a list.**  The entries `xs` of the list are
read from `loc`. -/
theorem Ends.asFrame (h : LocalsBut xs l loc)
    (hs : Ends lim P d s ⟨frame (refreshLocals l loc xs), μ⟩ T Q) :
    Ends lim P d s ⟨loc, μ⟩ T Q := by
  rw [h.eq_frame]
  exact hs

/-- **A piece of text that assigns only the locals `xs`**, at the end of the program.  `h` is the
lemma about the piece.  Afterwards the locals are the list `l` with the entries `xs` read from the
locals `loc'` of which the lemma speaks. -/
theorem Ends.pieceTo (xs : List ℕ) (h : Ends lim P d s ⟨frame l, μ⟩ T₁ R)
    (done : ∀ loc' μ', R ⟨loc', μ'⟩ → Q ⟨frame (refreshLocals l loc' xs), μ'⟩)
    (hxs : s.assigns ⊆ xs := by simp) (hT : T₁ ≤ T := by light_time) :
    Ends lim P d s ⟨frame l, μ⟩ T Q := by
  refine h.keeping.mono hT ?_
  rintro ⟨loc', μ'⟩ ⟨hR, hkeep⟩
  have hloc : LocalsBut xs l loc' := fun y hy => hkeep y fun hmem => hy (hxs hmem)
  rw [hloc.eq_frame]
  exact done loc' μ' hR

/-- **A piece of text that assigns only the locals `xs`**, followed by the rest of the program,
which gets the steps that are left. -/
theorem Ends.pieceToThen (xs : List ℕ) (h : Ends lim P d s₁ ⟨frame l, μ⟩ T₁ R)
    (rest : ∀ loc' μ', R ⟨loc', μ'⟩ →
      Ends lim P d s₂ ⟨frame (refreshLocals l loc' xs), μ'⟩ (T - T₁) Q)
    (hxs : s₁.assigns ⊆ xs := by simp) (hT : T₁ ≤ T := by light_time) :
    Ends lim P d (s₁ ;; s₂) ⟨frame l, μ⟩ T Q :=
  Ends.next T₁ (Ends.pieceTo xs h rest hxs le_rfl) hT

/-! ## Counting loops with scratch variables -/

/-- **Counting loops whose body may change the scratch variables `xs`.**  Before round j the locals
are the given ones with j in the counter and anything in the scratch variables, and I j holds of the
memory.  The round says nothing about the locals.  The counter is not among the scratch variables,
so the body does not assign it.  The bound hi gives n, n fits in a word, and the body takes at most
b steps. -/
theorem Ends.forScratch {i : ℕ} {hi : Expr} {body : Stmt} (xs : List ℕ)
    (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (start : I 0 μ)
    (round : ∀ (j : ℕ) (loc' μ' : ℕ → ℤ), j < n → I j μ' →
      Ends lim P d body ⟨frame (setLocal (refreshLocals l loc' xs) i j), μ'⟩ b fun σ' =>
        I (j + 1) σ'.mem)
    (done : ∀ loc' μ' : ℕ → ℤ, I n μ' → Q ⟨frame (setLocal (refreshLocals l loc' xs) i n), μ'⟩)
    (bound : ∀ (j : ℕ) (loc' μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Gives lim ⟨frame (setLocal (refreshLocals l loc' xs) i j), μ'⟩ n := by intros; light_side)
    (hxs : body.assigns ⊆ xs := by simp) (hcounter : i ∉ xs := by simp)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by light_time) :
    Ends lim P d (Stmt.for i hi body) ⟨frame l, μ⟩ T Q := by
  have shape (j : ℕ) {σ : State} (hσ : LocalsBut (i :: xs) l σ.loc) (hj : σ.loc i = j) :
      σ = ⟨frame (setLocal (refreshLocals l σ.loc xs) i j), σ.mem⟩ := by
    refine congrArg (State.mk · σ.mem) (funext fun y => ?_)
    rw [frame_setLocal, frame_refreshLocals]
    split_ifs with hy hy'
    · rw [hy, hj]
    · rfl
    · exact hσ y (by simp [hy, hy'])
  refine Ends.for (fun j σ => LocalsBut (i :: xs) l σ.loc ∧ I j σ.mem) n b
    ⟨fun y hy => Function.update_of_ne (by simp at hy; exact hy.1) _ _, start⟩ ?_ ?_ ?_ hn hT
  · rintro j σ hj hc ⟨hσ, hI⟩
    rw [shape j hσ hc]
    refine (round j σ.loc σ.mem hj hI).keeping.mono le_rfl ?_
    rintro σ' ⟨hI', hkeep⟩
    have hsame (y : ℕ) (hy : y ∉ xs) : σ'.loc y = σ.loc y := by
      rw [hkeep y fun hmem => hy (hxs hmem), ← shape j hσ hc]
    refine ⟨(hsame i hcounter).trans hc, fun y hy => ?_, hI'⟩
    simp only [List.mem_cons, not_or] at hy
    exact ((Function.update_of_ne hy.1 _ _).trans (hsame y hy.2)).trans
      (hσ y (by simp [hy.1, hy.2]))
  · rintro σ hc ⟨hσ, hI⟩
    rw [shape n hσ hc]
    exact done σ.loc σ.mem hI
  · rintro j σ hj hc ⟨hσ, hI⟩
    rw [shape j hσ hc]
    exact bound j σ.loc σ.mem hj hI

end

end Light
