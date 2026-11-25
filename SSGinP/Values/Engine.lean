module

public import SSGinP.Values.Basic
public import SSGinP.Search.Decision

@[expose] public section

/-!
# SSGinP.Values.Engine: values of all nodes and optimal strategies of a Stopping Game,
# by `n (2n+1)` runs of the ported price search (unconditional)

* `engineCall G k θ` : ONE run of the ported reference strategy tree (`SSG.searchTree n`, openai_math) against
                       the reply `SSG28Reply.replyGood` of the game `G` with its start node moved to `k`
                       (`SSG.runSearch (withStart G k) θ`); each query is answered by one evaluation of the value
                       operator `F G` at one node.
* `engineCall_fuzzy` : on a Stopping Game with stable assignment `v`, `engineCall G k θ = true` if
                       `θ + 1/(4·9^n) ≤ v k` and `= false` if `v k ≤ θ - 1/(4·9^n)`.
* `solve G`          : `SSGValues.solveWith (engineCall G) G`.
* MAIN `solve_correct`, `solve_eq_none_iff`, `solve_sound`.
* COSTS `solve_cost`, `engineCall_eq`, `searchTree_height`, `searchTree_prices`.
-/

namespace SSGValues

open SSG SSG28Search SSG28Reply OAI.Optimization.LinearProgramming OracleSpec PriceGame

variable {n : ℕ}

/-- the same game with the start node moved to `k`. -/
def withStart (G : Game n) (k : Fin n) : Game n :=
  { nodeType := G.nodeType, childJ := G.childJ, childK := G.childK, startNode := k }

theorem F_withStart (G : Game n) (k : Fin n) : F (withStart G k) = F G := rfl

theorem peel_withStart (G : Game n) (k : Fin n) : ∀ m, peel (withStart G k) m = peel G m
  | 0 => rfl
  | m + 1 => by
    funext i
    show peelStep (withStart G k) (peel (withStart G k) m) i = peelStep G (peel G m) i
    rw [peel_withStart G k m]; rfl

theorem stopping_withStart (G : Game n) (k : Fin n) (hs : StoppingGame G) : StoppingGame (withStart G k) := by
  rw [stoppingGame_iff_peelAll, peelAll_iff] at hs ⊢
  intro i; rw [peel_withStart]; exact hs i

/-- **one engine call**: one run of the ported price-search strategy tree on `2n+1` goods, asking "is the value
of node `k` greater than `θ`?". -/
noncomputable def engineCall (G : Game n) (k : Fin n) (θ : ℚ) : Bool := runSearch (withStart G k) θ

/-- the engine call decides `θ < v k` whenever `|v k - θ| ≥ 1/(4·9^n)`. -/
theorem engineCall_gap (G : Game n) (hs : StoppingGame G) (v : Fin n → ℚ) (hv : F G v = v) (k : Fin n) (θ : ℚ)
    (gap : θ + Delta n ≤ v k ∨ v k ≤ θ - Delta n) : engineCall G k θ = decide (θ < v k) := by
  have hs' := stopping_withStart G k hs
  have hr := prank_ranked G (peelAll_of_stoppingGame G hs)
  have ev : val (withStart G k) hs' = v :=
    fix_unique G (prank G) hr _ v (by have := val_fix (withStart G k) hs'; rwa [F_withStart] at this) hv
  have P := params (withStart G k) hs'
  have gap' : θ + Delta n ≤ (ssgCone (withStart G k) hs').v k ∨ (ssgCone (withStart G k) hs').v k ≤ θ - Delta n := by
    show θ + Delta n ≤ val (withStart G k) hs' k ∨ val (withStart G k) hs' k ≤ θ - Delta n
    rw [ev]; exact gap
  have h := decide_by_strategy (k := k) (θ := θ) P (le_rfl : 2 * rK n ≤ rR n) (rR_pos n) gap'
  have e : (ssgCone (withStart G k) hs').v k = v k := congrFun ev k
  rw [e] at h
  rw [← h]
  unfold engineCall runSearch searchTree
  rw [reply_eq (withStart G k) hs']
  rfl

theorem engineCall_fuzzy (G : Game n) (hs : StoppingGame G) (v : Fin n → ℚ) (hv : F G v = v) (k : Fin n) :
    Fuzzy (engineCall G k) (v k) (Delta n) := by
  have hΔ : 0 < Delta n := by unfold Delta; positivity
  constructor
  · intro θ h
    rw [engineCall_gap G hs v hv k θ (Or.inl h), decide_eq_true_iff]; linarith
  · intro θ h
    rw [engineCall_gap G hs v hv k θ (Or.inr h), decide_eq_false_iff_not]; linarith

/-- **the algorithm** (no hypothesis, no parameter): stopping test by peeling; for every node `2n+1` bisection
steps, each one run of the ported price search; greedy arc choice; Gauss–Jordan; check `F y = y`; output the
values of all nodes, a max strategy and a min strategy.  `none` exactly on games that are not Stopping Games. -/
noncomputable def solve (G : Game n) : Option (Solution n) := solveWith (engineCall G) G

/-- **MAIN THEOREM (values and optimal strategies, unconditional).** For every Stopping Game `G`, `solve G`
returns `s` such that `s.value` is the stable assignment of `G` and, from every node `i`: the max strategy
`s.maxStrategy` guarantees arrival at terminal-1 with probability at least `s.value i` against every min
strategy, and the min strategy `s.minStrategy` keeps the probability of arrival at terminal-1 at most
`s.value i` against every max strategy. -/
theorem solve_correct (G : Game n) (hs : StoppingGame G) :
    ∃ s : Solution n, solve G = some s ∧ Stable G s.value ∧
      ∀ i : Fin n,
        (∀ τ' : MinStrategy n, ArrivesWithProbAtLeast G s.maxStrategy τ' i (s.value i)) ∧
        (∀ (σ' : MaxStrategy n) (T : ℕ), arrivalProb G σ' s.minStrategy T i ≤ s.value i) := by
  obtain ⟨v, hv⟩ := stable_point_exists G hs
  have h := solveWith_complete (engineCall G) G hs v hv (engineCall_fuzzy G hs v hv)
  exact ⟨_, h, (stable_iff G v).mpr hv, greedy_isSolution G hs v hv⟩

/-- the answer is `none` exactly when `G` is not a Stopping Game (well-formedness plays no role). -/
theorem solve_eq_none_iff (G : Game n) : solve G = none ↔ ¬ StoppingGame G := by
  constructor
  · intro h hs
    obtain ⟨s, hsol, -⟩ := solve_correct G hs
    rw [h] at hsol; cases hsol
  · exact solveWith_not_stopping _ G

/-- every answer `some s` is correct (same conclusion as `solve_correct`). -/
theorem solve_sound (G : Game n) (s : Solution n) (h : solve G = some s) :
    StoppingGame G ∧ Stable G s.value ∧ IsSolution G s.value s.maxStrategy s.minStrategy :=
  solveWith_sound _ G s h

/-- the variant that also rejects games that are not well formed. -/
noncomputable def solveProblem (G : Game n) : Option (Solution n) :=
  if WellFormed G then solve G else none

theorem solveProblem_correct (G : Game n) :
    (WellFormed G ∧ StoppingGame G → ∃ s, solveProblem G = some s ∧ Stable G s.value ∧
      IsSolution G s.value s.maxStrategy s.minStrategy) ∧
    (¬ (WellFormed G ∧ StoppingGame G) → solveProblem G = none) := by
  unfold solveProblem
  constructor
  · rintro ⟨hw, hs⟩
    rw [if_pos hw]
    exact solve_correct G hs
  · intro h
    by_cases hw : WellFormed G
    · rw [if_pos hw]; exact (solve_eq_none_iff G).mpr (fun hs => h ⟨hw, hs⟩)
    · rw [if_neg hw]

/-! ## COSTS -/

theorem log_rR (n : ℕ) : (rR n + 1).log2 ≤ 5 * n + 8 := by
  have h1 := rR_size n
  have h2 : rR n < 2 ^ (5 * n + 8) := lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by norm_num) h1)
  have h3 : rR n + 1 < 2 ^ (5 * n + 8 + 1) := by rw [pow_succ]; omega
  have := (Nat.log2_lt (by omega)).mpr h3
  omega

/-- an engine call is, by definition, one run of the strategy tree `searchTree n` against the reply of the game
with start node `k`. -/
theorem engineCall_eq (G : Game n) (k : Fin n) (θ : ℚ) :
    engineCall G k θ =
      PriceGame.Tree.run (fun _ q => replyGood (withStart G k) θ (rDelta n) q.index q.prices) (searchTree n) [] := by
  unfold engineCall runSearch
  exact rfl

set_option exponentiation.threshold 2000 in
/-- the number of queries of one engine call. -/
theorem searchTree_height (n : ℕ) : (searchTree n).height ≤ 2 ^ 1510 * (7 * n + 10) ^ 1510 := by
  have hh : (searchTree n).height ≤ 2 ^ 1510 * (2*n+1 + (rR n + 1).log2 + 1) ^ 1510 :=
    decide_by_strategy_queries (n := n) (rR n)
  refine le_trans hh (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
  have := log_rR n
  omega

set_option exponentiation.threshold 400 in
/-- the bit size of every price queried in an engine call (the ported bound, as in `SSG.decision_by_search`). -/
theorem searchTree_prices (n : ℕ) :
    (Computation.ofTree (searchTree n)).AllQueries
      (PricesBounded (N := 2*n+1) (Control.Wire.pricePolynomial.eval (2*n+1 + (rR n).size + 1))) := by
  unfold searchTree
  have hT0 : Campaign.rounds (2*n+1) (rR n) ≤ (2*n+1 + (rR n).size + 1) ^ 300 :=
    (Campaign.rounds_eq _ _).le
  generalize hTT : Campaign.rounds (2*n+1) (rR n) = T at hT0 ⊢
  have h := price_key (2*n+1) (rR n) (dummy n) (fun _ _ => T)
  have hb := Control.Wire.campaignPriceBits_polynomial (2*n+1) (rR n) T hT0
  exact Computation.allQueries_mono _ _ (fun q hq i => (hq i).trans hb) _ h

/-- **COSTS.** For every game `G` on `n` nodes:
1. for every node exactly `2n+1` thresholds are asked, i.e. `n (2n+1)` engine calls in all, and `solve G`
   depends on the engine only through the answers of these calls;
2. every threshold is `a / 2^j` with `j ≤ 2n+1`, `a ≤ 2^j`;
3. the linear system solved has `n` unknowns and entries in `{0, ±1/2, ±1}`.
Together with: every engine call is a run of the same strategy tree `searchTree n` (`engineCall_eq`), which asks
at most `2^1510 (7n+10)^1510` queries (`searchTree_height`), each answered by evaluating `F G` at one node, and
every price in every query has bit size at most `pricePolynomial.eval (2n+1 + size(R) + 1)`, `R = 128·27^n`,
`size(R) ≤ 5n+8` (`searchTree_prices`, `SSG.rR_size`). -/
theorem solve_cost (G : Game n) :
    ((∀ k, (asked (engineCall G) k).length = 2 * n + 1) ∧
      ∀ call' : Fin n → ℚ → Bool, (∀ k, ∀ θ ∈ asked (engineCall G) k, engineCall G k θ = call' k θ) →
        solve G = solveWith call' G) ∧
    (∀ k, ∀ θ ∈ asked (engineCall G) k, ∃ j a : ℕ, j ≤ 2 * n + 1 ∧ a ≤ 2 ^ j ∧ θ = (a : ℚ) / 2 ^ j) ∧
    (∀ π : Fin n → Bool, (∀ i j, 2 * chainA G π i j = twoA G π i j ∧ -2 ≤ twoA G π i j ∧ twoA G π i j ≤ 2) ∧
      (∀ i, 2 * chainB G π i = twoB G π i ∧ 0 ≤ twoB G π i ∧ twoB G π i ≤ 2)) :=
  ⟨⟨(solveWith_congr (engineCall G) (engineCall G) G).1,
      fun call' h => (solveWith_congr (engineCall G) call' G).2 h⟩,
    fun k θ h => asked_dyadic _ k θ h, fun π => chain_entries G π⟩


end SSGValues
