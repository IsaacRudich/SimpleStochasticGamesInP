module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The definitions of `Challenge.lean`, for the proof library

A verbatim copy of the definitions of `Challenge.lean` (everything except the advertised theorems), so that the
declarations `Solution.lean` talks about are identical to the Challenge's. Do not edit by hand: change
`Challenge.lean` and run `python3 scripts/check_defs_sync.py --write`. CI runs the check.
-/

namespace SSG

/-! ## 1. Games -/

/-- the four types of nodes (terminal nodes come in two kinds). -/
inductive NodeType where
  | max | min | average | terminal0 | terminal1
  deriving DecidableEq

/-- a **Simple Stochastic Game** on the nodes `Fin n`: the type of every node, the two children `j = childJ i` and
`k = childK i` of every node (its two out-arcs; terminals have out-degree 0, in the encoding their child fields are
self-arcs and are ignored), and the start node. -/
structure Game (n : Nat) where
  nodeType  : Fin n → NodeType
  childJ    : Fin n → Fin n
  childK    : Fin n → Fin n
  startNode : Fin n

/-- which of the two out-arcs of a node: to child `j` or to child `k`. -/
inductive ArcChoice where
  | j | k
  deriving DecidableEq

/-- the child at the end of the chosen out-arc. -/
def Game.chosen {n : Nat} (G : Game n) (i : Fin n) : ArcChoice → Fin n
  | .j => G.childJ i
  | .k => G.childK i

variable {n : Nat}

/-- terminal nodes (terminal-0 or terminal-1). -/
def isTerminal (G : Game n) (i : Fin n) : Bool :=
  match G.nodeType i with
  | .terminal0 => true
  | .terminal1 => true
  | _ => false

/-- **well-formed**: exactly one terminal-0 node, exactly one terminal-1 node, and the child fields of each terminal
node are self-arcs. -/
def WellFormed (G : Game n) : Prop :=
  (Finset.univ.filter (fun i => G.nodeType i = .terminal0)).card = 1 ∧
  (Finset.univ.filter (fun i => G.nodeType i = .terminal1)).card = 1 ∧
  ∀ i, isTerminal G i = true → G.childJ i = i ∧ G.childK i = i

/-! ## 2. Strategies, Stopping Games, arrival probabilities, the decision problem -/

/-- a **max strategy**: one out-arc `(i, G.chosen i (σ i))` from each max node `i`. -/
abbrev MaxStrategy (n : Nat) := Fin n → ArcChoice

/-- a **min strategy**: one out-arc `(i, G.chosen i (τ i))` from each min node `i`. -/
abbrev MinStrategy (n : Nat) := Fin n → ArcChoice

/-- the arcs of the strategy subgraph `G_{σ,τ}`. -/
def Arc (G : Game n) (σ : MaxStrategy n) (τ : MinStrategy n) (i j : Fin n) : Prop :=
  match G.nodeType i with
  | .max => j = G.chosen i (σ i)
  | .min => j = G.chosen i (τ i)
  | .average => j = G.childJ i ∨ j = G.childK i
  | .terminal0 => False
  | .terminal1 => False

/-- `G_{σ,τ}` contains a path from `i` to a terminal. -/
inductive ReachesTerminal (G : Game n) (σ : MaxStrategy n) (τ : MinStrategy n) : Fin n → Prop
  | terminal (i : Fin n) : isTerminal G i = true → ReachesTerminal G σ τ i
  | step (i j : Fin n) : Arc G σ τ i j → ReachesTerminal G σ τ j → ReachesTerminal G σ τ i

/-- **Stopping Game**: for every pair of strategies, every node has a path to a terminal in `G_{σ,τ}`. -/
def StoppingGame (G : Game n) : Prop :=
  ∀ (σ : MaxStrategy n) (τ : MinStrategy n) (i : Fin n), ReachesTerminal G σ τ i

/-- the probability that the random walk in `G_{σ,τ}` from node `i` has arrived at terminal-1 within `T` steps. -/
def arrivalProb (G : Game n) (σ : MaxStrategy n) (τ : MinStrategy n) : Nat → Fin n → ℚ
  | 0, i => if G.nodeType i = .terminal1 then 1 else 0
  | T + 1, i => match G.nodeType i with
    | .terminal1 => 1
    | .terminal0 => 0
    | .max => arrivalProb G σ τ T (G.chosen i (σ i))
    | .min => arrivalProb G σ τ T (G.chosen i (τ i))
    | .average => (arrivalProb G σ τ T (G.childJ i) + arrivalProb G σ τ T (G.childK i)) / 2

/-- the random walk in `G_{σ,τ}` from node `i` arrives at terminal-1 with probability at least `c`: the probability of
having arrived within `T` steps (`arrivalProb`, nondecreasing in `T`) gets within every `ε > 0` of `c` (or above it)
for `T` large enough. -/
def ArrivesWithProbAtLeast (G : Game n) (σ : MaxStrategy n) (τ : MinStrategy n) (i : Fin n) (c : ℚ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ T : Nat, c - ε ≤ arrivalProb G σ τ T i

/-- the random walk in `G_{σ,τ}` from node `i` arrives at terminal-1 with probability greater than `c`: already within
some number `T` of steps the probability of having arrived exceeds `c`. -/
def ArrivesWithProbGreater (G : Game n) (σ : MaxStrategy n) (τ : MinStrategy n) (i : Fin n) (c : ℚ) : Prop :=
  ∃ T : Nat, c < arrivalProb G σ τ T i

/-- **the decision problem** (paper, §1.1): is there a max strategy that guarantees, against every min strategy, that
a token starting at the start node arrives at terminal-1 with probability at least 1/2? -/
def ValueAtLeastHalf (G : Game n) : Prop :=
  ∃ σ : MaxStrategy n, ∀ τ : MinStrategy n, ArrivesWithProbAtLeast G σ τ G.startNode (1 / 2)

/-- Condon's strict variant: probability greater than 1/2. -/
def ValueGreaterHalf (G : Game n) : Prop :=
  ∃ σ : MaxStrategy n, ∀ τ : MinStrategy n, ArrivesWithProbGreater G σ τ G.startNode (1 / 2)

/-- the yes-instances of the decision problem. -/
def SSGDecision (G : Game n) : Prop := WellFormed G ∧ StoppingGame G ∧ ValueAtLeastHalf G

/-- the yes-instances of the strict variant. -/
def SSGDecisionStrict (G : Game n) : Prop := WellFormed G ∧ StoppingGame G ∧ ValueGreaterHalf G

/-! ## 3. The input encoding

An instance is a pair `⟨n, G⟩` with `G : Game n` (there is no game on `0` nodes, as a game has a start node).
It is written as `n²` blocks of 10 bits, one block for each ordered pair of nodes `(u, v)`, rows `u = 0, …, n-1`
outer, columns `v = 0, …, n-1` inner. The block of `(u, v)` is: the node type of `u` (5 bits, exactly one set:
max, min, average, terminal-0, terminal-1), whether `u` is the start node, whether `v` is child `j` of `u`, whether
`v` is child `k` of `u`, whether `u = v`, whether `v` is the last node `n - 1`. So the word has length `10 n²`, and
`G` can be read off it (row `u` of the child-`j` bits is one-hot with its `true` at `childJ u`, and so on). The last
two bits of each block are redundant (they depend on the position only) and the node type and start bits are
repeated along each row. The word contains nothing but `G`, and its length `10 n²` lies between `n` and a
polynomial in `n`, so "polynomial in the length of the word" is the same as "polynomial in the number of nodes". -/

/-- the one-hot code of a node type: max, min, average, terminal-0, terminal-1. -/
def NodeType.bits : NodeType → List Bool
  | .max       => [true,  false, false, false, false]
  | .min       => [false, true,  false, false, false]
  | .average   => [false, false, true,  false, false]
  | .terminal0 => [false, false, false, true,  false]
  | .terminal1 => [false, false, false, false, true]

/-- the 10-bit block of the ordered node pair `(u, v)`. -/
def pairBits (G : Game n) (u v : Fin n) : List Bool :=
  (G.nodeType u).bits ++
    [decide (G.startNode = u), decide (G.childJ u = v), decide (G.childK u = v), decide (u = v),
     decide ((v : Nat) + 1 = n)]

/-- **the encoding of an instance** as a bit string of length `10 n²`. -/
def encode : (Σ n, Game n) → List Bool
  | ⟨n, G⟩ => (List.finRange n).flatMap fun u => (List.finRange n).flatMap fun v => pairBits G u v

/-! ## 4. The theorem

`PTime` below is Mathlib's notion of polynomial-time computability by a Turing machine
(`Turing.TM2ComputableInPolyTime`, in `Mathlib/Computability/TuringMachine/Computable.lean`: a machine with finitely
many stacks and states that, started on the input word, halts within `p (length of the input)` steps for one fixed
polynomial `p`, with the output word on its output stack), together with the requirement that every stack alphabet is
finite.

This is the same notion as polynomial time on multi-tape Turing machines with a binary alphabet: the community
library cslib-frontier (https://github.com/cslib-community/complexitylib, built on CSLib; commit `ab37a40` of
25 November 2026) proves, for injective encodings such as `encode` (`encode_injective` below),

    Turing.MultiTapeTM.ComputableInPolyTime f encIn encOut ↔
      ∃ h : Turing.TM2ComputableInPolyTime encIn encOut f, ∀ stack, Finite (h.tm.Γ stack)

(`computableInPolyTime_iff_tm2`, `CslibFrontier/Computability/Machines/Turing/TM2/Reverse/Transfer.lean`). The
right-hand side is `PTime`. That library is not imported here; the remark is for the reader. -/

/-- `f` **solves the SSG decision problem**: it answers `true` on exactly the games that are yes-instances. -/
def SolvesSSG (f : (Σ n, Game n) → Bool) : Prop :=
  ∀ x, f x = true ↔ SSGDecision x.2

/-- `f` **solves the strict SSG decision problem** (Condon's form, "greater than 1/2"): it answers `true` on exactly
the games that are yes-instances of `SSGDecisionStrict`. -/
def SolvesSSGStrict (f : (Σ n, Game n) → Bool) : Prop :=
  ∀ x, f x = true ↔ SSGDecisionStrict x.2

/-- `f` is **computable in polynomial time**: Mathlib's `Turing.TM2ComputableInPolyTime`, for games written with
`encode` and answers written as one bit, with every stack alphabet finite. -/
def PTime (f : (Σ n, Game n) → Bool) : Prop :=
  ∃ M : Turing.TM2ComputableInPolyTime encode Computability.encodeBool f, ∀ k, Finite (M.tm.Γ k)

/-! ## 6. Values and optimal strategies -/

/-- an answer for a game on `n` nodes: a value for every node, a max strategy and a min strategy. -/
structure Solution (n : Nat) where
  value       : Fin n → ℚ
  maxStrategy : MaxStrategy n
  minStrategy : MinStrategy n

/-- `s` gives **the values of all nodes and optimal strategies** of `G`: from every node `i`, the max strategy
guarantees arrival at terminal-1 with probability at least `s.value i` against every min strategy, and the min
strategy guarantees, against every max strategy, that arrival at terminal-1 does not have probability greater
than `s.value i`. -/
def IsSolution (G : Game n) (s : Solution n) : Prop :=
  ∀ i : Fin n,
    (∀ τ : MinStrategy n, ArrivesWithProbAtLeast G s.maxStrategy τ i (s.value i)) ∧
    (∀ σ : MaxStrategy n, ¬ ArrivesWithProbGreater G σ s.minStrategy i (s.value i))

/-- the number `m` in binary, lowest bit first, in exactly `w` bits. -/
def natBits (w m : Nat) : List Bool := (List.range w).map fun b => m.testBit b

/-- **the output word** of an answer, of length `4 n² + 2 n`: for every node `i = 0, …, n-1` the value
`s.value i` as a fraction in lowest terms, numerator then denominator, `2 n` bits each; then one bit per node
for the max strategy (`true` = the arc to child `k`); then one bit per node for the min strategy. -/
def encodeSolution (s : Solution n) : List Bool :=
  ((List.finRange n).flatMap fun i =>
      natBits (2 * n) (s.value i).num.toNat ++ natBits (2 * n) (s.value i).den) ++
  ((List.finRange n).map fun i => decide (s.maxStrategy i = .k)) ++
  ((List.finRange n).map fun i => decide (s.minStrategy i = .k))

/-- `f` **solves Simple Stochastic Games**: on a well-formed Stopping Game it writes the output word of an
answer giving the values of all nodes and optimal strategies; on every other input it writes the empty word. -/
def SolvesSSGValues (f : (Σ n, Game n) → List Bool) : Prop :=
  ∀ x : Σ n, Game n,
    (WellFormed x.2 ∧ StoppingGame x.2 → ∃ s : Solution x.1, IsSolution x.2 s ∧ f x = encodeSolution s) ∧
    (¬ (WellFormed x.2 ∧ StoppingGame x.2) → f x = [])

/-- `f` is computable in polynomial time (as `PTime` in §4, with a word as output). -/
def PTimeWord (f : (Σ n, Game n) → List Bool) : Prop :=
  ∃ M : Turing.TM2ComputableInPolyTime encode id f, ∀ k, Finite (M.tm.Γ k)

end SSG
