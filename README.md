# simple stochastic games in P

Lean 4 proofs that stopping simple stochastic games (SSGs) are solved in polynomial time by a Turing machine.

**What was known.** Polynomial time for SSGs is stated in OpenAI's preprint
[Strongly polynomial linear programming](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Strongly-polynomial-linear-programming-November-24-2026/paper.pdf)
(24 November 2026), as a consequence of its theorem on mean-payoff games (introduction, and section "Games on
graphs"). The Lean library released with the preprint formalizes its linear programming results, but not its
results on games. This repository ports the part of that library containing the preprint's search algorithm, applies
the search directly to the value operator of an SSG, and proves the three theorems below. The statements are in
[`Challenge.lean`](Challenge.lean), the proofs in `Solution.lean`, `SSGinP/` (ours) and `OAI/` (ported).

```lean
theorem ssg_in_P : ∃ f, SolvesSSG f ∧ PTime f
theorem ssgStrict_in_P : ∃ f, SolvesSSGStrict f ∧ PTime f
theorem ssg_values_in_P : ∃ f, SolvesSSGValues f ∧ PTimeWord f
```

- `ssg_in_P`: a polynomial-time Turing machine decides whether the max player can guarantee that the token arrives
  at terminal-1 with probability at least 1/2.
- `ssgStrict_in_P`: the same for probability greater than 1/2 (Condon's form of the problem).
- `ssg_values_in_P`: a polynomial-time Turing machine writes the value of every node and an optimal strategy for each
  player.

"Polynomial time" is Mathlib's `Turing.TM2ComputableInPolyTime` with finite alphabets; a game on `n` nodes is given
by `10 n²` bits. `Challenge.lean` also states seven small sanity checks on the input and output encodings.

## Scope

- Stopping games only. A game that is not well formed or not a stopping game is a no-instance of the two decision
  problems and gets the empty output in the third theorem.
- The search engine of the OpenAI preprint is used as a black box. This is not a new algorithm for SSGs.
- This is not a practical solver: the proved polynomial bound is far too large to run.
- Definitions follow Rudich, Rudich, Rue, *Simple Stochastic Stopping Games: A Generator and Benchmark Library*
  (arXiv:2402.02571); the problem is from Condon, *The complexity of stochastic games* (1992).

## Comparison with the standard problem

- **General games.** Condon reduces general SSGs to stopping games. That reduction is not formalized here, so these
  theorems do not by themselves give the result for general SSGs.
- **Threshold.** Condon asks for probability greater than 1/2; arXiv:2402.02571 asks for at least 1/2. Both are proved.
- **Strategies.** Strategies in `Challenge.lean` are positional. The library (not the Challenge) also proves, for
  stopping games, that both decision problems are unchanged when both players may use history-dependent strategies
  (`SSG.valueAtLeastHalf_iff_byPlay`, `SSG.valueGreaterHalf_iff_byPlay` in `SSGinP/Theory/Play.lean`).
- **Encoding.** The `10 n²` bits are an explicit adjacency-style encoding. Its length is at least `n` and at most
  polynomial in `n`, so polynomial time in it is polynomial time in the number of nodes.
- **Malformed words.** Mathlib's notion of computability concerns words that encode a game. The Challenge says
  nothing about other words.
- **Probabilities.** "Arrives with probability at least `c`" is expressed by arrival within `T` steps: for every
  `ε > 0` some `T` reaches `c - ε`. "Greater than `c`" means some `T` exceeds `c`.

## Literature

- Condon (*Inform. and Comput.* 96, 1992) introduced SSGs and placed the threshold problem in NP ∩ coNP.
- Ludwig (*Inform. and Comput.* 117, 1995) gave a subexponential randomized algorithm. Halman (*Algorithmica* 49,
  2007) treats SSGs as LP-type problems. Zwick and Paterson (*Theoret. Comput. Sci.* 158, 1996) and Andersson and
  Miltersen (ISAAC 2009) relate SSGs to discounted and mean-payoff games.
- OpenAI's preprint (24 November 2026) states polynomial time for SSGs; see the beginning of this file. Beyond
  what Lean checks here, we say nothing about the correctness of the preprint. No claim of priority is made.

This is a short list of works, not a survey.

## How the proof goes

1. `SSGinP/Theory`: the value operator of a stopping game has a unique fixed point, which gives the values and
   optimal strategies; whether a game is stopping is decided by peeling.
2. `SSGinP/Search`: the comparison of a value with a threshold is decided by one call of the ported search on `2n+1`
   goods, whose replies evaluate the value operator.
3. `SSGinP/Machine`: the oracle is replaced by procedures that compute the replies from the encoded game, giving a
   machine without an oracle that halts in polynomial time.
4. `SSGinP/Bridge`: the machine is turned into a Mathlib `TM2` machine on the encoding of `Challenge.lean`.
5. `SSGinP/Values`: the exact values are found by bisection with threshold tests, followed by the reconstruction of a
   fraction of bounded denominator; greedy strategies are then read off.

## The seven sanity checks

`encode_length` and `encode_injective`: the input word has length `10 n²` and determines the game.
`encodeSolution_length`, `encodeSolution_injective`: the output word has length `4 n² + 2 n` and determines the
answer among the answers of one game. `isSolution_value_unique`: the values in an answer are unique.
`isSolution_value_bits`: for a stopping game the `2 n` bits per numerator and denominator lose nothing.
`ssgDecision_iff_value`: if an answer exists, the decision problem is "well formed, stopping, and the value of the
start node is at least 1/2".

## Build and check

Lean 4.35.0 and Mathlib v4.35.0 (pinned in `lean-toolchain` and `lake-manifest.json`).

```text
python3 scripts/check-lean-sources.py     # module headers and file sizes
python3 scripts/check_defs_sync.py        # SSGinP/Defs.lean is a verbatim copy of the Challenge definitions
lake exe cache get
lake build
lake env lean test/Axioms.lean            # axioms of the ten compared theorems
./scripts/verify-comparator.sh            # lake comparator on comparator.json (Linux, needs bwrap)
```

`comparator.json` lists the ten theorems of `Challenge.lean` and permits only `propext`, `Quot.sound` and
`Classical.choice`. The repository follows the [Palomar](https://palomar-registry.org/) template; submissions go
through https://submit.palomar-registry.org/.

## Licence and attribution

Apache-2.0 (`LICENSE`). The files under `OAI/` come from the [openai/math](https://github.com/openai/math)
repository (Apache-2.0, OpenAI) and were modified for this port: see `NOTICE` and `PORTED_FILES.md`.

## AI assistance

The Lean proofs and the port were written by AI agents (Anthropic's Claude, run with Claude Code) under the direction
of a human author, who read and accepted the definitions and statements in `Challenge.lean`. Details are in
`formalization.yaml`.
