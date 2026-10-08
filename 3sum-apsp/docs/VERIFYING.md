# How a routine is verified

The running times of the paper are proved about programs of a small imperative language, which a verified compiler translates to the word RAM ([`docs/MACHINE.md`](MACHINE.md), Part 2). This document shows how a routine of that language is proved correct, with a bound on its steps. It is for a reader who wants to read, check or change a file of `ThreeSumApsp/Lang/` or `ThreeSumApsp/Programs/`. You need not trust it: Lean checks every theorem that is mentioned here, and the statements of `EndStatement.lean` and `PaperStatements.lean` speak of the word RAM only, not of the notions below.

It has four parts: the notions; one small routine, line by line; the conventions of the larger files, for reference; and the way from a routine to a running time.

## 1. The notions

**Programs** (`ThreeSumApsp/Lang/Syntax.lean`). A piece of program text (`Stmt`) is `.skip`, an assignment `.set x e`, a store `.store a e`, a sequence `s₁ ;; s₂`, a branch `.ite c s₁ s₂`, a loop `.while c s`, or a call `.call p args x`. Local variables and procedures are numbers. In an expression, `v x` is the local variable x, `k n` the constant n, `M a` the memory cell at the address a, and `+'`, `-'`, `*'` are the three operations; `<'`, `≤'` and `='` are the tests. The counting loop `.for i hi body` abbreviates `.set i (k 0) ;; .while (v i <' hi) (body ;; .set i (v i +' k 1))`. A program (`Program`) is the list of the bodies of its procedures. A procedure has no return statement: its result is what local 0 holds when the body ends.

**States, steps and limits.** A state ⟨loc, μ⟩ consists of the local variables of the running procedure and the memory, both functions from natural numbers to integers. `Exec lim P d s σ σ' c` says that the text s of the program P, started in σ at nesting depth d of calls, ends in σ' after exactly c steps. Each constant, variable, operation and load of an expression is a step, and so is each comparison, assignment, store and branch; a call costs its arguments and two steps more. A run obeys the limits `lim`: no constant and no result of an operation exceeds lim.word in absolute value, no address that is read or written reaches lim.space, and calls are nested at most lim.depth deep. A run that would break a limit does not exist. So a proof that a routine ends is also a proof that it stays within the limits, which is what the compiler's theorem needs.

**The two judgements**, and three notions about states:

```lean
def Ends (lim : Limits) (P : Program) (d : ℕ) (s : Stmt) (σ : State) (T : ℕ) (Q : State → Prop) : Prop :=
  ∃ σ' c, Exec lim P d s σ σ' c ∧ c ≤ T ∧ Q σ'
def Meets (lim : Limits) (P : Program) (p d : ℕ) (vals : List ℤ) (μ : ℕ → ℤ) (T : ℕ) (R : ℤ → (ℕ → ℤ) → Prop) : Prop :=
  ∃ body, P[p]? = some body ∧ Ends lim P d body ⟨frame vals, μ⟩ T fun σ' => R (σ'.loc 0) σ'.mem
def frame (args : List ℤ) : ℕ → ℤ := fun i => args.getD i 0
def Seg (μ : ℕ → ℤ) (a : ℕ) (l : List ℤ) : Prop := ∀ i (h : i < l.length), μ (a + i) = l[i]
abbrev SameOutside (μ μ' : ℕ → ℤ) (a n : ℕ) : Prop := SameOn (Outside a n) μ μ'
```

`Ends`: the text s, started in σ, ends within T steps in a state that satisfies Q. `Meets` is the *contract* of a procedure: procedure number p, run at depth d on the arguments `vals` in the memory μ, ends within T steps with a result r and a memory μ' that satisfy R r μ'. `frame` l are the locals that hold the list l, and 0 after its end; a procedure that has been called starts with its arguments in this form. `Seg μ a l`: the list l is stored in μ from the address a on. `SameOutside μ μ' a n`: μ' agrees with μ on every cell outside the n cells from a.

**Rules.** Each construct has a rule that turns a goal `Ends … s …` into goals about the parts of s, so a proof follows the program from top to bottom. This is the rule for an assignment that is followed by more text:

```lean
theorem Ends.setToThen {x : ℕ} {e : Expr} {s : Stmt} (z : ℤ)
    (h : Ends lim P d s ⟨frame (setLocal l x z), μ⟩ (T - (e.cost + 1)) Q)
    (he : e.Gives lim ⟨frame l, μ⟩ z := by light_side)
    (hT : e.cost + 1 ≤ T := by light_time) :
    Ends lim P d (.set x e ;; s) ⟨frame l, μ⟩ T Q
```

It is told the value z. The goal h that it leaves is about the rest s, in the state with z in entry x of the list. There are two side conditions: the evaluation of e stays within the limits and gives z (`e.Gives lim σ z` is `e.Safe lim σ ∧ e.val σ = z`), and the time suffices. Both have default proofs. `Exec` and the costs are defined in `ThreeSumApsp/Lang/Syntax.lean`, `Ends` and its basic rules in `ThreeSumApsp/Lang/Logic.lean`, the rules that are used in proofs in `ThreeSumApsp/Lang/Rules.lean` and `ThreeSumApsp/Lang/Frames.lean`, and `Meets` in `ThreeSumApsp/Lang/Calls.lean`.

**Time is handed on, not added up.** The cost of a simple statement is computed from its text (`e.cost + 1` above). The rule asks that it is at most T and leaves T minus the cost for the rest. So no step count of a single statement is written in a proof.

**Calls.** `Meets.of_body` proves a contract from an `Ends` fact about the body. The rule for calls is given the contract of the callee at depth d + 1, charges the caller for the arguments, two steps and the time of the contract, and puts the result into the local x. A caller sees the contract only. So its proof does not depend on the body of the callee, and a program can call a procedure of which only a contract is known.

## 2. One routine, line by line

The routine powTable(dst, L, b) writes the powers 1, b, …, b^(L−1) into the L cells from dst. The lines below are lines of `ThreeSumApsp/Lang/Lib/PowTable.lean`, except the rule `Ends.for`, which is in `ThreeSumApsp/Lang/Rules.lean`; docstrings and attributes are omitted, and the order follows the explanation. The file declares `variable {lim : Limits} {P : Program} {d : ℕ}`, and it opens the namespace `PowTable`, in which the five names of locals and `Filled` are declared.

### The text

```lean
abbrev Dest : ℕ := 0
abbrev Len : ℕ := 1
abbrev Base : ℕ := 2
abbrev Expo : ℕ := 3
abbrev Power : ℕ := 4

def powTableRound : Stmt :=
  .store (v Dest +' v Expo) (v Power) ;;
  .set Power (v Power *' v Base)

def powTableBody : Stmt :=
  .set Power (k 1) ;;
  .for Expo (v Len) powTableRound

def powTableTime (L : ℕ) : ℕ := 17 * L + 8
```

The first three locals are the arguments, in the order of the call. The round has a name of its own, so that the proof can speak of its cost. The numerals 17 and 8 appear here and nowhere else. They can be recomputed. The store costs 3 + 1 + 1 steps and the assignment 3 + 1, which makes 9 for the text of a round. In each round the test costs 3 (counter, bound, comparison), the branch of the loop 1 and the increment 4. At the ends, the first assignment costs 2, the start of the counter 2, and the last test with its branch 4. A sequence costs nothing.

### What is proved

```lean
def powList (b L : ℕ) : List ℤ := (List.range L).map fun j => ((b ^ j : ℕ) : ℤ)

theorem powTable_ends {μ : ℕ → ℤ} {dst L b : ℕ} (e p : ℤ) (t : List ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d powTableBody ⟨frame (dst :: L :: b :: e :: p :: t), μ⟩ (powTableTime L) fun σ' =>
      Seg σ'.mem dst (powList b L) ∧ SameOutside μ σ'.mem dst L := by
```

The state is written out, in the order of the numbers of the locals: the three arguments, then whatever `Expo`, `Power` and the further locals hold (e, p and the list t; they are arbitrary so that the theorem also serves where this body is part of another routine). The three hypotheses are what the limits ask: addresses fit in a word; the L cells lie within the memory; every power up to b^L fits in a word (the last round forms b^L, although it is not stored). The conclusion has the two usual halves: what is stored where afterwards, in terms of a function on lists (`powList`), and which cells are unchanged. In the statements, powers are formed in ℕ and then read as integers.

### The rule for the loop, and the invariant

```lean
theorem Ends.for {σ : State} {i : ℕ} {hi : Expr} {body : Stmt} {T : ℕ} {Q : State → Prop}
    (I : ℕ → State → Prop) (n b : ℕ)
    (start : I 0 { σ with loc := Function.update σ.loc i 0 })
    (round : ∀ (j : ℕ) (σ : State), j < n → σ.loc i = j → I j σ → Ends lim P d body σ b fun σ' =>
      σ'.loc i = j ∧ I (j + 1) { σ' with loc := Function.update σ'.loc i ((j : ℤ) + 1) })
    (done : ∀ σ : State, σ.loc i = n → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : State), j ≤ n → σ.loc i = j → I j σ → hi.Safe lim σ ∧ hi.val σ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by light_time) :
    Ends lim P d (Stmt.for i hi body) σ T Q

def PowTable.Filled (μ : ℕ → ℤ) (dst L b : ℕ) (t : List ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame (dst :: L :: b :: j :: ((b ^ j : ℕ) : ℤ) :: t), μ'⟩ ∧
    (∀ i < j, μ' (dst + i) = ((b ^ i : ℕ) : ℤ)) ∧ SameOutside μ μ' dst L
```

The rule is given an invariant I, where I j holds before round j (rounds are numbered from 0), the number n of rounds, and a bound b on the steps of a round. The test, the increment and their costs are the rule's business. It asks four things by name, and it has two side conditions with default proofs: the number of rounds fits in a word (`hn`), since the counter reaches n, and the time suffices (`hT`). *start*: I 0 holds once the counter is 0. *round*: from a state with j < n, j in the counter and I j, the body ends within b steps, leaves j in the counter, and gives I (j + 1) after the increment. *done*: I n gives Q. *bound*: the expression hi can be evaluated and has the value n. The invariant `Filled` says: the counter holds j and `Power` holds b^j, the first j cells are filled, and nothing outside the L cells has changed. Mind the letters: in the rule, i, hi and b are the counter, the bound of the loop and the cost of a round; in the routine, i is the index of a cell, hi a hypothesis about it, and b the base.

### The proof

Above each step a comment shows the statement that the step treats, in the usual notation, with p for `Power` and j for `Expo`; dst[j] is the cell dst + j. Some Lean notation: `?start` names a goal that `refine` leaves, and `case start =>` takes it up; `(hT := …)` gives an argument by name; in a `rintro` pattern a name or `_` takes a variable or a hypothesis, `-` drops it, `⟨…⟩` opens it, and `rfl` substitutes an equation; a leading dot, as in `.refl`, stands for the namespace that the goal expects; `h ▸ t` rewrites the type of t with h; `Function.update f a z` is f with z at a. A natural number in a list of integers is read as an integer.

```lean
  have h1 : (1 : ℤ) ≤ lim.word := by simpa using hpow 0 (Nat.zero_le _)
  unfold powTableBody powTableTime
  -- p := 1
  light_set 1
  -- for j < L
  refine Ends.for (Filled μ dst L b t) L powTableRound.blockCost ?start ?round ?done ?bound
    (hT := by light_time [powTableRound])
```

`light_set 1` applies `Ends.setToThen` with z = 1. That the constant fits in a word follows from `h1`. The goal that remains amounts to `Ends lim P d (.for Expo (v Len) powTableRound) ⟨frame (dst :: L :: b :: e :: 1 :: t), μ⟩ (17 * L + 8 - 2) …`, with the same conclusion as before. `Ends.for` is given the invariant, the number of rounds, and the cost of a round as computed from its text (`Stmt.blockCost`). The comparison `hT` mentions that cost, so its proof is given here, with the definition to unfold in brackets (the closing tactics take such a list in brackets, the step tactics after `using`). `hn` follows from `hw` and `hdst`.

```lean
  case start => exact ⟨μ, by simp [update_frame_setLocal], fun i hi => absurd hi (by omega), .refl⟩
  case bound =>
    rintro j _ - - ⟨μ', rfl, -⟩
    light_side
  case done =>
    rintro _ - ⟨μ', rfl, powers, same⟩
    exact ⟨fun i hi => by rw [getElem_powList]; exact powers i (by simpa using hi), same⟩
```

*start*: the memory is still μ; the locals are the list of the invariant for j = 0, since `Power` holds 1 = b⁰ (`update_frame_setLocal` turns an update of `frame` l into `frame` of the updated list); no cell has to be filled; μ agrees with itself. *bound*: the patterns take j and the state, drop j ≤ L and the fact on the counter, and open the invariant, so that the state is written out; `light_side` then proves that `v Len` can be evaluated and gives L. *done*: `Seg` asks for entry i of `powList`, which is b^i, in cell dst + i.

```lean
  case round =>
    rintro j _ hj - ⟨μ', rfl, powers, same⟩
    have hfits : (b : ℤ) ^ (j + 1) ≤ lim.word := by exact_mod_cast hpow (j + 1) (by omega)
    have hnonneg : 0 ≤ (b : ℤ) ^ (j + 1) := by positivity
    unfold powTableRound
    -- dst[j] := p
    light_store (dst + j) (b ^ j : ℕ)
    -- p := p * b
    light_set (b ^ (j + 1) : ℕ) using ← pow_succ
    refine ⟨by simp, Function.update μ' (dst + j) (b ^ j : ℕ), by simp [update_frame_setLocal],
      fun i hi => ?_, by light_keep⟩
    obtain hi | rfl := Nat.lt_succ_iff_lt_or_eq.1 hi
    · rw [Function.update_of_ne (by omega)]
      exact powers i hi
    · exact Function.update_self ..
```

*round*: the two `have` lines state, with the power formed in ℤ, that the product that is formed lies between 0 and lim.word; the limit bounds the absolute value, so both sides are needed. `light_store` is told the address and the value. That `v Dest +' v Expo` gives dst + j, that this sum fits in a word, and that the address lies within the memory are side conditions, closed from `hw`, `hdst` and `hj`; reading a local needs no condition. `light_set` is told the value of the product; `using ← pow_succ` names the identity b^j · b = b^(j+1). Here `light_set` treats the last statement (rule `Ends.setTo`), so what remains is what the rule asks of a round: the counter holds j (`by simp`), and `Filled` holds for j + 1. The memory is μ' with one cell changed. `light_keep` proves that it agrees with μ outside the L cells, from `same`, `hj` and the address of the store. The last four lines prove that the first j + 1 cells are filled. An index i < j + 1 is either below j or equal to j. If i < j, cell dst + i is not the cell of the store (Function.update_of_ne), so `powers` applies. If i = j, it is the cell of the store and holds b^j (Function.update_self).

### The contract

```lean
theorem powTable_meets {p : ℕ} (hp : P[p]? = some powTableBody) {μ : ℕ → ℤ} {dst L b : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [(dst : ℤ), L, b] μ (powTableTime L) fun _ μ' =>
      Seg μ' dst (powList b L) ∧ SameOutside μ μ' dst L :=
  .of_body hp (frame_append_zeros [(dst : ℤ), L, b] 2 ▸ powTable_ends 0 0 [] hw hdst hpow)
```

In every program P whose procedure number p has this body, the procedure keeps the promise. The called procedure has 0 in all locals after its arguments, which is the case of `powTable_ends` with 0 for e and p and the empty list for t (`frame_append_zeros l n`: n zeros at the end of the list l do not change `frame`; here n = 2). The theorem about the body is kept beside the contract because a routine for Theorem 5 of the paper contains this body in its own text.

## 3. The conventions of the larger files

**Locals.** Each routine declares its locals by name, in a namespace of its own, and program texts use the names. A routine with few locals writes the list of the state directly, as above; a routine with many writes it by names, `setLocals [] [(Dest, dst), (Count, n), …]`. Where the values of some locals do not matter, as in an invariant, `LocalsBut xs l loc` says that loc agrees with `frame` l except perhaps at the scratch locals xs. A text changes only the locals that it assigns (`Stmt.assigns`). So a lemma about a piece of text that several routines contain says nothing about the other locals, and the rule that uses such a lemma (`Ends.pieceToThen`, applied with `refine`) keeps the caller's list for them.

**The memory.** `ArrayAt μ a l N U top` says that the list l is stored from a on, has N entries of absolute value at most U, and lies below `top`. "These cells are unchanged" is always `SameOn K μ μ'`, mostly under one of its names: `SameOutside`; `Kept μ μ' fr`, all cells below fr; `KeptBut`, the same except an output region. A routine that needs working space is given a *free pointer* fr as an argument: it may write from fr on, and it promises `Kept`. Every fact X about a memory has a lemma X.keep (`Seg.keep` is the model), which carries it to a later memory that agrees on the cells that the fact reads. Regions are given by first address and length; `Inside`, `Outside` and `Apart` abbreviate the inequalities. Further notions of this kind: `MatAt μ a A` (the cells from a on hold the matrix A, row by row), `readSeg μ a n` (the list held by the n cells from a) and `overwrite μ off ws` (the memory μ with the list ws written into the cells from off on). `Std lim` collects the standing assumptions about the limits: every address fits in a word, and lim.word is at least 100.

**The shape of a contract.**

```lean
def XSpec (lim : Limits) (P : Program) : Prop :=
  ∀ (x : XArgs) (μ : ℕ → ℤ), XPre lim μ x →
    ∀ d, d + k ≤ lim.depth →
      Meets lim P pX d x.vals μ (tX x) fun r μ' => …
```

The record XArgs holds the arguments, and the lists that are stored at the addresses among them. XPre holds the assumptions: first one field for each array, then the facts about the data, then inequalities between sizes. A routine with few arguments has no records; its theorem takes the variables and hypotheses directly, in the same order. The number k counts the levels of calls below the routine; if a routine calls nothing, its contract holds at every depth, and the clause is omitted. pX is the number of the procedure in the program for which the file is written; a record of facts `P[pX]? = some xBody` says which body has which number. tX is the time function: it is defined once, beside the routine, from the names of the times of its callees and its own steps.

**Names of theorems.** The theorem about a routine x is mostly called x_spec. Where the kinds are told apart, x_ends is about a piece of text (its conclusion is `Ends`), x_meets or x_entry about a procedure (`Meets`, or a specification of the shape above), and x_solves about a task (`Solves`; see `docs/MACHINE.md`, "Tasks, solvers and hosts").

**The step tactics.** Each treats what is at the head of the program and leaves the goal about the rest of the program, or Q of the state if nothing follows.

| At the head | Tactic | What it is given | Rule |
|---|---|---|---|
| `x := e` | `light_set z` | the value z | `Ends.setToThen`, `Ends.setTo` |
| `mem[a] := e` | `light_store a z` | the address a and the value z | `Ends.storeToThen`, `Ends.storeTo` |
| `if c then … else …` | `light_if h₁ h₂ : φ` | what the test says, as a proposition φ; two goals remain, one for each side with what follows the branch, with h₁ : φ and h₂ : ¬ φ | `Ends.iteIffThen` |
| `x := p(args)` | `light_call fact with r μ' h` | the contract of the callee, applied to its arguments and assumptions; its promises become hypotheses | `Ends.callToThen`, `Ends.callTo` |
| a piece with a lemma of its own, which describes the whole state afterwards | `light_piece fact with σ' h` | the `Ends` fact | `Ends.pieceThen`, `Ends.pieceLast` |
| `skip` | `light_skip` | | `Ends.skip` |

Side conditions are proved by linear arithmetic from the hypotheses. If they need more, the step names it after `using`: the content of a cell that is read, an identity to rewrite with, a definition to unfold.

| Tactic | What it proves or does |
|---|---|
| `light_side` | an expression or a test stays within the limits and has the value given |
| `light_time` | a comparison of step counts |
| `light_arith` | an inequality between addresses and sizes |
| `light_keep` | cells are unchanged, from the promises of the steps in between |
| `light_facts H` | puts the fields of the record H among the hypotheses, without names |

They are defined in `ThreeSumApsp/Lang/Rules.lean`, `ThreeSumApsp/Lang/Tactics.lean` and `ThreeSumApsp/Lang/Regions.lean`.

**Loops** have no tactic; their rules are applied with `refine`. Their parts are called start, round and done, and for a counting loop also bound.

| Rule | The loop |
|---|---|
| `Ends.while`, `Ends.whileConst` | n rounds, with an invariant I j before round j; a cost for each round, or one cost for all |
| `Ends.whileVariant` | the number of rounds depends on the data: every round decreases a quantity |
| `Ends.whileBlock` | the body has no loop and no call, so its cost is computed from its text |
| `Ends.for` | the counting loop, in general |
| `Ends.forMem`, `Ends.forFrame`, `Ends.forShape` | counting loops whose body changes no local, or only scratch locals |
| `Ends.pass` | a loop that writes f 0, …, f (n − 1) into consecutive cells and changes no local but the counter |

**Recursion** needs no rule: a fact about a recursive procedure is proved by induction in Lean, and the rule for calls uses the induction hypothesis as the contract.

**A call**, in the proof of a caller:

```lean
  -- r := x(a, b)
  light_call (hX args μ pre) with r μ₁ ⟨result, same₁⟩
```

Here hX is the specification of x, args the record of its arguments and pre a proof of what it assumes; the tactic supplies the depth d + 1 and proves the clause on the depth from the hypotheses. The proof goes on with the promises as hypotheses. A fact h about cells that the callee leaves alone is carried to the memory μ₁ by h.keep.

## 4. From a routine to a running time

A contract bounds the steps by an explicit function of the arguments. The word size, the cells and the depth that a run needs are bounded in the same way (`Need`). Two more steps lead to a sentence of the paper.

* **Orders of growth.** That a time function is O(…) is proved in a small calculus (`ThreeSumApsp/Util/Asymptotics/Scale.lean`): the proof unfolds the time functions and names a fact for each quantity that is not a sum, a product or a power. It repeats no numeral.
* **To the machine.** `docs/MACHINE.md`, "From a program of the language to a statement", says how a procedure with a contract, a time bound and polynomial needs becomes a program of the word RAM that solves a problem within the time bound.

`docs/PROGRAMS.md` lists every routine with its theorem, the functions of `ThreeSumApsp/Spec/` in which the theorem is stated, and its time function.
