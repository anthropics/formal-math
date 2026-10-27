/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Wrap.Defs
public import Wrap.Coding
public import Wrap.Sim
public import StepMachines.Prog.Stepped
public import StepMachines.Prog.Comb

/-! # Two machines in alternation, and a choice between two machines: definitions and statements

**The sentences answered.** Proof of Corollary 11: «Run the algorithm of Theorem A (c), with the
pieces of Appendix B, and the algorithm of Theorem D (b) in alternation, one operation of each at a
time, and output the result of the one that stops first.
Both compute the same number. This multiplies the number of operations of the faster one by a
constant». Step 6 of Appendix D: «In the other cases, that is, if n < K₀^17 or this k exceeds (log
n)^(1/4), the algorithm tries all assignments».

**What is used.** proof/machines/Wrap puts a polynomial-time front end and last step around ONE
machine that is only known to exist (`Wrap.EveryMachineCanBeWrapped`); here two such machines are
combined.

**What is stated here.** All machines are Mathlib's (`Turing.TM2ComputableAux Bool Bool`);
`Wrap.Outputs M x y t` says that M, started on the bit string x, halts within t steps with output y.
* `alt K₁ K₂ pre₁ pre₂ post₁ post₂`: the alternation as a computation cut into steps. Its state is a
  pair: a value that stands for a configuration of M₁ and one that stands for a configuration of M₂.
  One step advances BOTH by one step of their machines. It has a result as soon as one of the two
  has halted.
* `Hosts X N q`: the machine N carries out the computation X cut into steps, with a polynomial
  overhead.
* `Alternates M₁ M₂ pre₁ pre₂ post₁ post₂ N q`: whenever M₁ puts out y₁ on `pre₁ x` within t₁ steps,
  M₂ puts out y₂ on `pre₂ x` within t₂ steps, and the two results agree (`post₁ y₁ = post₂ y₂`), N
  puts out that result on x within q·(min(t₁, t₂) + |x| + 1)^q steps.
* `EveryTwoMachinesCanBeAlternated`: for ALL machines M₁, M₂ with finite alphabets and all
  polynomial-time `pre₁`, `pre₂`, `post₁`, `post₂` there are codings K₁, K₂ of their configurations,
  a machine N with finite alphabets and numbers q₀, q such that N carries out `alt K₁ K₂ …` and
  alternates M₁ and M₂.
* `choose K₁ K₂ test …`, `Chooses M₁ M₂ test … N q`, `EveryTwoMachinesCanBeChosenBetween`: the same
  for “M₁ if the test on the input says so, else M₂”.

**What it does not say.** The overhead is a power q, which may depend on the two machines and the
four functions, where the paper has a constant factor. `Alternates` and `Chooses` fix what N puts
out and a bound on its steps, not
the steps themselves; that N carries out the named computation is said by `Hosts`. If the two
results differ, or one of the machines does not halt in the sense of `Wrap.Outputs`, `Alternates`
asks nothing. -/

@[expose] public section

namespace TwoMachines

open Turing Groundwork Wrap

/-! ### The two computations cut into steps -/

section
variable {M₁ M₂ : TM2ComputableAux Bool Bool}

/-- M₁ on `pre₁ x` and M₂ on `pre₂ x` in alternation. A state is a pair of values, the first for a
configuration of M₁, the second for one of M₂. One step applies the coded step of M₁ to the first
and the coded step of M₂ to the second. There is a result once one of the two stands for a halted
configuration: `post₁` of the output of M₁ if M₁ has halted, else `post₂` of the output of M₂. -/
def alt (K₁ : Coding M₁) (K₂ : Coding M₂) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) : Stepped (List Bool) (List Bool) where
  σ := Rep × Rep
  init x := (K₁.init (pre₁ x), K₂.init (pre₂ x))
  step r := (K₁.step r.1, K₂.step r.2)
  out r := match K₁.out r.1 with
    | some y => some (post₁ y)
    | none => (K₂.out r.2).map post₂

/-- M₁ on `pre₁ x` if `test x` is true, else M₂ on `pre₂ x`: `Stepped.ite` of the two simulations
`Wrap.sim`. -/
def choose (K₁ : Coding M₁) (K₂ : Coding M₂) (test : List Bool → Bool) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) : Stepped (List Bool) (List Bool) :=
  Stepped.ite test (sim K₁ pre₁ post₁) (sim K₂ pre₂ post₂)

end

/-- The start configuration of M on the bit string x. -/
def start (M : TM2ComputableAux Bool Bool) (x : List Bool) : M.tm.Cfg := initList M.tm (x.map M.inputAlphabet.invFun)

/-- The machine N carries out the computation X: whenever X ends on x with the result w within T
steps and with all states of size at most S, N puts out w on x within q·(T + 1)·(|x| + S + 1)^q
steps. -/
def Hosts (X : Stepped (List Bool) (List Bool)) (N : TM2ComputableAux Bool Bool) (q : ℕ) : Prop :=
  ∀ (x : List Bool) (T S : ℕ) (w : List Bool), X.Runs x T S w → Outputs N x w (q * (T + 1) * (x.length + S + 1) ^ q)

/-! ### What the machine around the two machines does -/

/-- For all bit strings x, y₁, y₂ and all t₁, t₂: if M₁ puts out y₁ on `pre₁ x` within t₁ steps, M₂
puts out y₂ on `pre₂ x` within t₂ steps, and `post₁ y₁ = post₂ y₂`, then N puts out this bit string
on x within q·(min(t₁, t₂) + |x| + 1)^q steps. -/
def Alternates (M₁ M₂ : TM2ComputableAux Bool Bool) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) (N : TM2ComputableAux Bool Bool) (q : ℕ) : Prop :=
  ∀ (x y₁ y₂ : List Bool) (t₁ t₂ : ℕ), Outputs M₁ (pre₁ x) y₁ t₁ → Outputs M₂ (pre₂ x) y₂ t₂ → post₁ y₁ = post₂ y₂ →
    Outputs N x (post₁ y₁) (q * (min t₁ t₂ + x.length + 1) ^ q)

/-- For all bit strings x, y and all t: if `test x` is true and M₁ puts out y on `pre₁ x` within t
steps, then N puts out `post₁ y` on x within q·(t + |x| + 1)^q steps; if `test x` is false and M₂
puts out y on `pre₂ x` within t steps, then N puts out `post₂ y` on x within q·(t + |x| + 1)^q
steps. -/
def Chooses (M₁ M₂ : TM2ComputableAux Bool Bool) (test : List Bool → Bool) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool) (N : TM2ComputableAux Bool Bool) (q : ℕ) : Prop :=
  ∀ (x y : List Bool) (t : ℕ),
    (test x = true → Outputs M₁ (pre₁ x) y t → Outputs N x (post₁ y) (q * (t + x.length + 1) ^ q)) ∧
    (test x = false → Outputs M₂ (pre₂ x) y t → Outputs N x (post₂ y) (q * (t + x.length + 1) ^ q))

/-- Any two machines with finite alphabets can be run in alternation: for all such M₁, M₂ and all
polynomial-time `pre₁`, `pre₂`, `post₁`, `post₂` there are codings K₁, K₂ of their configurations, a
machine N with finite alphabets and numbers q₀, q such that N carries out the computation
`alt K₁ K₂ pre₁ pre₂ post₁ post₂` and `Alternates M₁ M₂ pre₁ pre₂ post₁ post₂ N q` holds. -/
def EveryTwoMachinesCanBeAlternated : Prop :=
  ∀ M₁ M₂ : TM2ComputableAux Bool Bool, (∀ i, Finite (M₁.tm.Γ i)) → (∀ i, Finite (M₂.tm.Γ i)) →
    ∀ pre₁ pre₂ post₁ post₂ : List Bool → List Bool, PolyT pre₁ → PolyT pre₂ → PolyT post₁ → PolyT post₂ →
      ∃ (K₁ : Coding M₁) (K₂ : Coding M₂) (N : TM2ComputableAux Bool Bool) (q₀ q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧
        Hosts (alt K₁ K₂ pre₁ pre₂ post₁ post₂) N q₀ ∧ Alternates M₁ M₂ pre₁ pre₂ post₁ post₂ N q

/-- A polynomial-time test on the input can choose between any two machines with finite alphabets:
for all such M₁, M₂, every polynomial-time `test` and all polynomial-time `pre₁`, `pre₂`, `post₁`,
`post₂` there are codings K₁, K₂, a machine N with finite alphabets and numbers q₀, q such that N
carries out the computation `choose K₁ K₂ test pre₁ pre₂ post₁ post₂` and
`Chooses M₁ M₂ test pre₁ pre₂ post₁ post₂ N q` holds. -/
def EveryTwoMachinesCanBeChosenBetween : Prop :=
  ∀ M₁ M₂ : TM2ComputableAux Bool Bool, (∀ i, Finite (M₁.tm.Γ i)) → (∀ i, Finite (M₂.tm.Γ i)) →
    ∀ (test : List Bool → Bool) (pre₁ pre₂ post₁ post₂ : List Bool → List Bool), PolyT test → PolyT pre₁ → PolyT pre₂ → PolyT post₁ → PolyT post₂ →
      ∃ (K₁ : Coding M₁) (K₂ : Coding M₂) (N : TM2ComputableAux Bool Bool) (q₀ q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧
        Hosts (choose K₁ K₂ test pre₁ pre₂ post₁ post₂) N q₀ ∧ Chooses M₁ M₂ test pre₁ pre₂ post₁ post₂ N q

end TwoMachines
