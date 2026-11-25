module

public import SSGinP.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# SSGinP.GameFacts: Simple Stochastic Games, in the terminology of
# Rudich, Rudich, Rue, "Simple Stochastic Stopping Games: A Generator and Benchmark Library" (arXiv:2402.02571, §1.1)

A Simple Stochastic Game (SSG) is a directed graph `G` with four types of nodes: max, min, average and terminal nodes.
Each max, min and average node `i` has exactly two out-arcs, leading to its two children `j = G.childJ i` and
`k = G.childK i`; there are two kinds of terminal nodes, terminal-0 and terminal-1, with fixed values 0 and 1.
Terminals have out-degree 0; in the encoding their child fields are self-arcs and are ignored.  The paper numbers the nodes `1, …, n` with
terminal-0 and terminal-1 numbered `n-1` and `n`; here the nodes are `Fin n = {0, …, n-1}`, and `WellFormed G` asks
for exactly one terminal-0 node and exactly one terminal-1 node (their position does not matter: every notion below is
invariant under renaming the nodes, `GameIso`), and that the child fields of each terminal node are self-arcs.

The max player chooses the arc at max nodes, the min player at min nodes, and at average nodes each arc is taken with
probability 1/2.  A max strategy `σ` is a set of arcs consisting of one arc `(i, G.chosen i (σ i))` from each max node
`i`, where `σ i : ArcChoice` selects the arc to child `j` or to child `k`; a min strategy likewise at min nodes
(`MaxStrategy`, `MinStrategy`; the entries of `σ` at other nodes are not used).  `G_{σ,τ}` is the subgraph keeping only the chosen arcs at max and min nodes (`Arc G σ τ`).

## Primary definitions (the paper's form)
* `StoppingGame G`       : for every pair of strategies `(σ, τ)` and every node, `G_{σ,τ}` has a path from that node
                           to a terminal (`ReachesTerminal`).
* `arrivalProb G σ τ T i`: the probability that the random walk in `G_{σ,τ}` from node `i` has arrived at terminal-1
                           within `T` steps (a rational, by the plain one-step recurrence); it is nondecreasing in `T`
                           (`arrivalProb_mono`) with values in `[0,1]` (`arrivalProb_mem`), and the probability of
                           arrival is its supremum over `T`.
* `ArrivesWithProbAtLeast`, `ArrivesWithProbGreater` : the random walk arrives at terminal-1 with probability `≥ c`, resp. `> c`
                           (audit lemmas `arrivesWithProbGreater_iff`, `arrivesWithProbAtLeast_iff_forall_lt`).
* `ValueAtLeastHalf G`   : THE DECISION PROBLEM of the paper: there is a max strategy that guarantees, against every
                           min strategy, that a token starting at the start node arrives at terminal-1 with probability
                           at least 1/2.  `ValueGreaterHalf G`: the same with "greater than 1/2" (Condon).
* `SSGDecision G`        : `WellFormed G ∧ StoppingGame G ∧ ValueAtLeastHalf G`;  `SSGDecisionStrict` with `> 1/2`.

## Secondary definitions (history-dependent strategies)
`HStrategy n` (the chosen arc may depend on the whole history), `win1`, `unabs`, `StoppingByPlay`,
`ValueAtLeastHalfByPlay`, `ValueGreaterHalfByPlay`.  `SSGinP.Theory.Play` proves that they agree with the primary ones on
stopping games.

## Invariance
`GameIso` (renaming of nodes) preserves all of the above: `wellFormed_iso`, `stoppingGame_iso`,
`valueAtLeastHalf_iso`, `valueGreaterHalf_iso`, `ssgDecision_iso`, `ssgDecisionStrict_iso`, and the by-play variants.
-/

namespace SSG

variable {n m : Nat}

instance (G : Game n) : Decidable (WellFormed G) := by unfold WellFormed; infer_instance

/-! ## strategies, strategy subgraphs, stopping games -/

/-! ## arrival probabilities and the decision problem -/

/-- audit lemma: the probabilities lie in `[0,1]`. -/
theorem arrivalProb_mem (G : Game n) (σ : MaxStrategy n) (τ : MinStrategy n) :
    ∀ T i, 0 ≤ arrivalProb G σ τ T i ∧ arrivalProb G σ τ T i ≤ 1 := by
  intro T
  induction T with
  | zero => intro i; simp only [arrivalProb]; split <;> norm_num
  | succ T ih =>
    intro i
    simp only [arrivalProb]
    cases G.nodeType i with
    | terminal1 => norm_num
    | terminal0 => norm_num
    | max => exact ih _
    | min => exact ih _
    | average =>
      have a := ih (G.childJ i); have b := ih (G.childK i)
      constructor <;> linarith [a.1, a.2, b.1, b.2]

/-- audit lemma: arrival within `T` steps implies arrival within `T + 1` steps. -/
theorem arrivalProb_succ (G : Game n) (σ : MaxStrategy n) (τ : MinStrategy n) :
    ∀ T i, arrivalProb G σ τ T i ≤ arrivalProb G σ τ (T + 1) i := by
  intro T
  induction T with
  | zero =>
    intro i
    have m := (arrivalProb_mem G σ τ 1 i).1
    by_cases h : G.nodeType i = .terminal1
    · have a : arrivalProb G σ τ 0 i = 1 := by simp [arrivalProb, h]
      have b : arrivalProb G σ τ 1 i = 1 := by simp [arrivalProb, h]
      rw [a, b]
    · have a : arrivalProb G σ τ 0 i = 0 := by simp [arrivalProb, h]
      rw [a]; exact m
  | succ T ih =>
    intro i
    show arrivalProb G σ τ (T + 1) i ≤ arrivalProb G σ τ (T + 1 + 1) i
    conv_lhs => rw [arrivalProb]
    conv_rhs => rw [arrivalProb]
    cases h : G.nodeType i <;> simp only
    · exact ih _
    · exact ih _
    · have a := ih (G.childJ i); have b := ih (G.childK i); linarith
    · exact le_refl _
    · exact le_refl _

/-- audit lemma: `arrivalProb` is nondecreasing in `T`. -/
theorem arrivalProb_mono (G : Game n) (σ : MaxStrategy n) (τ : MinStrategy n) (i : Fin n) {T T' : Nat}
    (h : T ≤ T') : arrivalProb G σ τ T i ≤ arrivalProb G σ τ T' i := by
  induction T' with
  | zero => have : T = 0 := by omega
            subst this; exact le_refl _
  | succ T' ih =>
    rcases Nat.lt_or_ge T (T' + 1) with hl | hl
    · exact le_trans (ih (by omega)) (arrivalProb_succ G σ τ T' i)
    · have : T = T' + 1 := by omega
      subst this; exact le_refl _

/-- audit lemma: "greater than `c`" means "at least some `c' > c`". -/
theorem arrivesWithProbGreater_iff (G : Game n) (σ : MaxStrategy n) (τ : MinStrategy n) (i : Fin n) (c : ℚ) :
    ArrivesWithProbGreater G σ τ i c ↔ ∃ c' > c, ArrivesWithProbAtLeast G σ τ i c' := by
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨arrivalProb G σ τ T i, hT, fun ε hε => ⟨T, by linarith⟩⟩
  · rintro ⟨c', hc', h⟩
    obtain ⟨T, hT⟩ := h ((c' - c) / 2) (by linarith)
    exact ⟨T, by linarith⟩

/-- audit lemma: "at least `c`" means "greater than every `c' < c`". -/
theorem arrivesWithProbAtLeast_iff_forall_lt (G : Game n) (σ : MaxStrategy n) (τ : MinStrategy n) (i : Fin n)
    (c : ℚ) : ArrivesWithProbAtLeast G σ τ i c ↔ ∀ c' < c, ArrivesWithProbGreater G σ τ i c' := by
  constructor
  · intro h c' hc'
    obtain ⟨T, hT⟩ := h ((c - c') / 2) (by linarith)
    exact ⟨T, by linarith⟩
  · intro h ε hε
    obtain ⟨T, hT⟩ := h (c - ε) (by linarith)
    exact ⟨T, le_of_lt hT⟩

/-! ## secondary: history-dependent strategies -/

/-- a history-dependent strategy (for either player): the chosen arc may depend on the list of visited nodes
(current node first). -/
abbrev HStrategy (n : Nat) := List (Fin n) → ArcChoice

/-- number of sequences of `T` fair random bits on which the play from `u` (history `h`) arrives at terminal-1 within
`T` steps, when the max player plays `σ` and the min player plays `τ`. -/
def win1 (G : Game n) (σ τ : HStrategy n) : Nat → List (Fin n) → Fin n → Int
  | 0, _, u => if G.nodeType u = .terminal1 then 1 else 0
  | T + 1, h, u => match G.nodeType u with
    | .terminal1 => 2 ^ (T + 1)
    | .terminal0 => 0
    | .max => 2 * win1 G σ τ T (u :: h) (G.chosen u (σ (u :: h)))
    | .min => 2 * win1 G σ τ T (u :: h) (G.chosen u (τ (u :: h)))
    | .average => win1 G σ τ T (u :: h) (G.childJ u) + win1 G σ τ T (u :: h) (G.childK u)

/-- number of sequences of `T` fair random bits on which the play reaches no terminal within `T` steps. -/
def unabs (G : Game n) (σ τ : HStrategy n) : Nat → List (Fin n) → Fin n → Int
  | 0, _, u => if G.nodeType u = .terminal0 ∨ G.nodeType u = .terminal1 then 0 else 1
  | T + 1, h, u => match G.nodeType u with
    | .terminal1 => 0
    | .terminal0 => 0
    | .max => 2 * unabs G σ τ T (u :: h) (G.chosen u (σ (u :: h)))
    | .min => 2 * unabs G σ τ T (u :: h) (G.chosen u (τ (u :: h)))
    | .average => unabs G σ τ T (u :: h) (G.childJ u) + unabs G σ τ T (u :: h) (G.childK u)

/-- stopping by play: for all history-dependent strategies and every start node, the probability of reaching no
terminal within `T` steps tends to `0`. -/
def StoppingByPlay (G : Game n) : Prop :=
  ∀ (σ τ : HStrategy n) (u : Fin n) (k : Nat), ∃ T, 2 ^ k * unabs G σ τ T [] u < 2 ^ T

/-- the decision problem with history-dependent strategies. -/
def ValueAtLeastHalfByPlay (G : Game n) : Prop :=
  ∃ σ : HStrategy n, ∀ τ : HStrategy n, ∀ k : Nat, ∃ T : Nat,
    (1 / 2 - 1 / 2 ^ k) * 2 ^ T ≤ (win1 G σ τ T [] G.startNode : ℚ)

/-- the strict variant with history-dependent strategies (horizon uniform in the min player's strategy). -/
def ValueGreaterHalfByPlay (G : Game n) : Prop :=
  ∃ σ : HStrategy n, ∃ T : Nat, ∀ τ : HStrategy n, (2 : Int) ^ T < 2 * win1 G σ τ T [] G.startNode

/-! ## invariance under renaming of the nodes -/

/-- an isomorphism of games: a renaming of the nodes preserving node types, children and the start node. -/
structure GameIso (G : Game n) (H : Game m) where
  e : Fin n ≃ Fin m
  nodeType : ∀ i, H.nodeType (e i) = G.nodeType i
  childJ : ∀ i, H.childJ (e i) = e (G.childJ i)
  childK : ∀ i, H.childK (e i) = e (G.childK i)
  startNode : H.startNode = e G.startNode

def GameIso.symm {G : Game n} {H : Game m} (f : GameIso G H) : GameIso H G where
  e := f.e.symm
  nodeType := fun j => by
    have := f.nodeType (f.e.symm j); rw [Equiv.apply_symm_apply] at this; exact this.symm
  childJ := fun j => by
    have := f.childJ (f.e.symm j); rw [Equiv.apply_symm_apply] at this
    rw [this, Equiv.symm_apply_apply]
  childK := fun j => by
    have := f.childK (f.e.symm j); rw [Equiv.apply_symm_apply] at this
    rw [this, Equiv.symm_apply_apply]
  startNode := by rw [f.startNode, Equiv.symm_apply_apply]

theorem GameIso.chosen {G : Game n} {H : Game m} (f : GameIso G H) (i : Fin n) (c : ArcChoice) :
    H.chosen (f.e i) c = f.e (G.chosen i c) := by
  cases c
  · exact f.childJ i
  · exact f.childK i

theorem isTerminal_iso {G : Game n} {H : Game m} (f : GameIso G H) (i : Fin n) :
    isTerminal H (f.e i) = isTerminal G i := by simp [isTerminal, f.nodeType]

theorem wellFormed_of_iso {G : Game n} {H : Game m} (f : GameIso G H) (hG : WellFormed G) : WellFormed H := by
  have key : ∀ t : NodeType, (Finset.univ.filter (fun j => H.nodeType j = t)) =
      (Finset.univ.filter (fun i => G.nodeType i = t)).map f.e.toEmbedding := by
    intro t; ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · intro h; refine ⟨f.e.symm j, ?_, by simp⟩
      rw [← f.nodeType, Equiv.apply_symm_apply]; exact h
    · rintro ⟨i, hi, rfl⟩; rw [f.nodeType]; exact hi
  unfold WellFormed at *
  rw [key, key, Finset.card_map, Finset.card_map]
  refine ⟨hG.1, hG.2.1, fun j hj => ?_⟩
  have hj' : isTerminal G (f.e.symm j) = true := by rw [← isTerminal_iso f, Equiv.apply_symm_apply]; exact hj
  obtain ⟨a, b⟩ := hG.2.2 _ hj'
  have ea := f.childJ (f.e.symm j); have eb := f.childK (f.e.symm j)
  rw [Equiv.apply_symm_apply, a, Equiv.apply_symm_apply] at ea
  rw [Equiv.apply_symm_apply, b, Equiv.apply_symm_apply] at eb
  exact ⟨ea, eb⟩

/-- transport of a strategy (one chosen arc per node) along a renaming. -/
def trP (e : Fin n ≃ Fin m) (σ : Fin n → ArcChoice) : Fin m → ArcChoice := fun j => σ (e.symm j)

theorem trP_back (e : Fin n ≃ Fin m) (τ : Fin m → ArcChoice) : trP e (trP e.symm τ) = τ := by
  funext j; simp [trP]

theorem arc_iso {G : Game n} {H : Game m} (f : GameIso G H) (σ : MaxStrategy n) (τ : MinStrategy n) (i j : Fin n) :
    Arc H (trP f.e σ) (trP f.e τ) (f.e i) (f.e j) ↔ Arc G σ τ i j := by
  unfold Arc; rw [f.nodeType]
  cases G.nodeType i <;> simp [trP, f.chosen, f.childJ, f.childK]

theorem reaches_iso {G : Game n} {H : Game m} (f : GameIso G H) (σ : MaxStrategy n) (τ : MinStrategy n) (i : Fin n)
    (h : ReachesTerminal G σ τ i) : ReachesTerminal H (trP f.e σ) (trP f.e τ) (f.e i) := by
  induction h with
  | terminal i hi => exact .terminal _ (by rw [isTerminal_iso]; exact hi)
  | step i j hij _ ih => exact .step _ _ ((arc_iso f σ τ i j).mpr hij) ih

theorem stoppingGame_of_iso {G : Game n} {H : Game m} (f : GameIso G H) (hG : StoppingGame G) : StoppingGame H := by
  intro σ τ j
  have := reaches_iso f (trP f.e.symm σ) (trP f.e.symm τ) (f.e.symm j) (hG _ _ _)
  rwa [trP_back, trP_back, Equiv.apply_symm_apply] at this

theorem arrivalProb_iso {G : Game n} {H : Game m} (f : GameIso G H) (σ : MaxStrategy n) (τ : MinStrategy n) :
    ∀ T i, arrivalProb H (trP f.e σ) (trP f.e τ) T (f.e i) = arrivalProb G σ τ T i := by
  intro T
  induction T with
  | zero => intro i; simp [arrivalProb, f.nodeType]
  | succ T ih =>
    intro i
    simp only [arrivalProb, f.nodeType]
    cases G.nodeType i <;> simp [trP, f.chosen, f.childJ, f.childK, ih]

theorem valueAtLeastHalf_of_iso {G : Game n} {H : Game m} (f : GameIso G H) (hG : ValueAtLeastHalf G) :
    ValueAtLeastHalf H := by
  obtain ⟨σ, h⟩ := hG
  refine ⟨trP f.e σ, fun τ ε hε => ?_⟩
  obtain ⟨T, hT⟩ := h (trP f.e.symm τ) ε hε
  refine ⟨T, ?_⟩
  have e := arrivalProb_iso f σ (trP f.e.symm τ) T G.startNode
  rw [trP_back] at e
  rw [f.startNode, e]; exact hT

theorem valueGreaterHalf_of_iso {G : Game n} {H : Game m} (f : GameIso G H) (hG : ValueGreaterHalf G) :
    ValueGreaterHalf H := by
  obtain ⟨σ, h⟩ := hG
  refine ⟨trP f.e σ, fun τ => ?_⟩
  obtain ⟨T, hT⟩ := h (trP f.e.symm τ)
  refine ⟨T, ?_⟩
  have e := arrivalProb_iso f σ (trP f.e.symm τ) T G.startNode
  rw [trP_back] at e
  rw [f.startNode, e]; exact hT

theorem wellFormed_iso {G : Game n} {H : Game m} (f : GameIso G H) : WellFormed G ↔ WellFormed H :=
  ⟨wellFormed_of_iso f, wellFormed_of_iso f.symm⟩

theorem stoppingGame_iso {G : Game n} {H : Game m} (f : GameIso G H) : StoppingGame G ↔ StoppingGame H :=
  ⟨stoppingGame_of_iso f, stoppingGame_of_iso f.symm⟩

theorem valueAtLeastHalf_iso {G : Game n} {H : Game m} (f : GameIso G H) : ValueAtLeastHalf G ↔ ValueAtLeastHalf H :=
  ⟨valueAtLeastHalf_of_iso f, valueAtLeastHalf_of_iso f.symm⟩

theorem valueGreaterHalf_iso {G : Game n} {H : Game m} (f : GameIso G H) :
    ValueGreaterHalf G ↔ ValueGreaterHalf H :=
  ⟨valueGreaterHalf_of_iso f, valueGreaterHalf_of_iso f.symm⟩

/-- **isomorphism invariance of the decision problem.** -/
theorem ssgDecision_iso {G : Game n} {H : Game m} (f : GameIso G H) : SSGDecision G ↔ SSGDecision H := by
  unfold SSGDecision; rw [wellFormed_iso f, stoppingGame_iso f, valueAtLeastHalf_iso f]

theorem ssgDecisionStrict_iso {G : Game n} {H : Game m} (f : GameIso G H) :
    SSGDecisionStrict G ↔ SSGDecisionStrict H := by
  unfold SSGDecisionStrict; rw [wellFormed_iso f, stoppingGame_iso f, valueGreaterHalf_iso f]

/-! ### invariance of the by-play variants -/

/-- transport of a history-dependent strategy. -/
def trS (e : Fin n ≃ Fin m) (σ : HStrategy n) : HStrategy m := fun h => σ (h.map e.symm)

theorem trS_back (e : Fin n ≃ Fin m) (τ : HStrategy m) : trS e (trS e.symm τ) = τ := by
  funext h; simp [trS, List.map_map]

theorem win1_iso {G : Game n} {H : Game m} (f : GameIso G H) (σ τ : HStrategy n) :
    ∀ T h u, win1 H (trS f.e σ) (trS f.e τ) T (h.map f.e) (f.e u) = win1 G σ τ T h u := by
  intro T
  induction T with
  | zero => intro h u; simp [win1, f.nodeType]
  | succ T ih =>
    intro h u
    have hh : ∀ c : HStrategy n, trS f.e c ((u :: h).map f.e) = c (u :: h) := by
      intro c; simp [trS, List.map_map]
    have hm : f.e u :: h.map f.e = (u :: h).map f.e := rfl
    simp only [win1, f.nodeType]
    cases G.nodeType u <;> simp only [hh, f.chosen, f.childJ, f.childK, hm, ih]

theorem unabs_iso {G : Game n} {H : Game m} (f : GameIso G H) (σ τ : HStrategy n) :
    ∀ T h u, unabs H (trS f.e σ) (trS f.e τ) T (h.map f.e) (f.e u) = unabs G σ τ T h u := by
  intro T
  induction T with
  | zero => intro h u; simp [unabs, f.nodeType]
  | succ T ih =>
    intro h u
    have hh : ∀ c : HStrategy n, trS f.e c ((u :: h).map f.e) = c (u :: h) := by
      intro c; simp [trS, List.map_map]
    have hm : f.e u :: h.map f.e = (u :: h).map f.e := rfl
    simp only [unabs, f.nodeType]
    cases G.nodeType u <;> simp only [hh, f.chosen, f.childJ, f.childK, hm, ih]

theorem valueGreaterHalfByPlay_of_iso {G : Game n} {H : Game m} (f : GameIso G H) (hG : ValueGreaterHalfByPlay G) :
    ValueGreaterHalfByPlay H := by
  obtain ⟨σ, T, h⟩ := hG
  refine ⟨trS f.e σ, T, fun τ => ?_⟩
  have := h (trS f.e.symm τ)
  have e := win1_iso f σ (trS f.e.symm τ) T [] G.startNode
  rw [trS_back] at e
  simp only [List.map_nil] at e
  rw [f.startNode, e]; exact this

theorem valueAtLeastHalfByPlay_of_iso {G : Game n} {H : Game m} (f : GameIso G H) (hG : ValueAtLeastHalfByPlay G) :
    ValueAtLeastHalfByPlay H := by
  obtain ⟨σ, h⟩ := hG
  refine ⟨trS f.e σ, fun τ k => ?_⟩
  obtain ⟨T, hT⟩ := h (trS f.e.symm τ) k
  refine ⟨T, ?_⟩
  have e := win1_iso f σ (trS f.e.symm τ) T [] G.startNode
  rw [trS_back] at e
  simp only [List.map_nil] at e
  rw [f.startNode, e]; exact hT

theorem stoppingByPlay_of_iso {G : Game n} {H : Game m} (f : GameIso G H) (hG : StoppingByPlay G) :
    StoppingByPlay H := by
  intro σ τ u k
  obtain ⟨T, hT⟩ := hG (trS f.e.symm σ) (trS f.e.symm τ) (f.e.symm u) k
  refine ⟨T, ?_⟩
  have e := unabs_iso f (trS f.e.symm σ) (trS f.e.symm τ) T [] (f.e.symm u)
  rw [trS_back, trS_back, Equiv.apply_symm_apply] at e
  simp only [List.map_nil] at e
  rw [e]; exact hT

theorem valueGreaterHalfByPlay_iso {G : Game n} {H : Game m} (f : GameIso G H) :
    ValueGreaterHalfByPlay G ↔ ValueGreaterHalfByPlay H :=
  ⟨valueGreaterHalfByPlay_of_iso f, valueGreaterHalfByPlay_of_iso f.symm⟩

theorem valueAtLeastHalfByPlay_iso {G : Game n} {H : Game m} (f : GameIso G H) :
    ValueAtLeastHalfByPlay G ↔ ValueAtLeastHalfByPlay H :=
  ⟨valueAtLeastHalfByPlay_of_iso f, valueAtLeastHalfByPlay_of_iso f.symm⟩

theorem stoppingByPlay_iso {G : Game n} {H : Game m} (f : GameIso G H) : StoppingByPlay G ↔ StoppingByPlay H :=
  ⟨stoppingByPlay_of_iso f, stoppingByPlay_of_iso f.symm⟩

end SSG
