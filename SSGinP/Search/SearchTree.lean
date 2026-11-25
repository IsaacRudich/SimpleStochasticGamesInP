module

public import SSGinP.Search.Search
public import OAI.Optimization.LinearProgramming.PriceGame.RecursiveRecovery

@[expose] public section

/-!
# SSGinP.Search.SearchTree: the ported recursive price strategy decides `θ < v k` for a cone contraction

Combines `SSG28Search.pos_consistent` / `neg_consistent` (ours) with
`Campaign.recover_sign` and `Campaign.recursive_query_bound_machine` (ported from openai_math,
math layer, no machine model): running the reference strategy tree on `2n+1` goods with the
labels of `SSG28Search.label` returns `decide (θ < v k)` whenever `|v k - θ| ≥ Δ`, after at most
`2^1510 (2n+1 + log2 (R+1) + 1)^1510` queries. (Bit sizes of the queried prices are bounded only
in the machine layer, `OracleSpec.ExtremalSignRecovery`.)
-/

namespace SSG28Search

open OAI.Optimization.LinearProgramming.PriceGame

variable {n : ℕ} {C : Cone n} {δ θ Δ : ℚ} {k : Fin n} {K T R : ℕ}

/-- The hidden hypothesis of the ported theorem, for either sign. -/
noncomputable def hidden (P : Params C δ Δ K T) (hR : 2 * K ≤ R) (positive : Bool) :
    Hidden (2*n+1) R (dummy n) where
  positive := positive
  active := Finset.univ
  anchor_mem := Finset.mem_univ _
  cost g := if positive then ⟨costPos C δ K T g, by have := costPos_le P g; omega⟩
    else ⟨costNeg C δ K T g, by have := costNeg_le P g; omega⟩

/-- The label oracle, as a reply function for `Tree.run`. -/
noncomputable def reply (C : Cone n) (δ θ : ℚ) (k : Fin n) :
    List (Query (2*n+1) × Bool) → Query (2*n+1) → Bool :=
  fun _ q => label C δ θ k q.index q.prices

theorem forced_pos (P : Params C δ Δ K T) (hR : 2 * K ≤ R) (hk : θ + Δ ≤ C.v k)
    (history : List (Query (2*n+1) × Bool)) (q : Query (2*n+1))
    (hf : (hidden P hR true).Forced q) : reply C δ θ k history q = (hidden P hR true).positive := by
  obtain ⟨-, hmin⟩ := hf
  simp only [hidden, Hidden.signedPrice, if_true] at hmin
  exact pos_consistent P hk q.index q.prices (fun g => by
    simpa [OAI.Optimization.LinearProgramming.OracleSpec.adjustedCost] using hmin g (Finset.mem_univ g))

theorem forced_neg (P : Params C δ Δ K T) (hR : 2 * K ≤ R) (hk : C.v k ≤ θ - Δ)
    (history : List (Query (2*n+1) × Bool)) (q : Query (2*n+1))
    (hf : (hidden P hR false).Forced q) : reply C δ θ k history q = (hidden P hR false).positive := by
  obtain ⟨-, hmin⟩ := hf
  simp only [hidden, Hidden.signedPrice, Bool.false_eq_true, if_false] at hmin
  exact neg_consistent P hk q.index q.prices (fun g => by
    have := hmin g (Finset.mem_univ g)
    simp only [OAI.Optimization.LinearProgramming.OracleSpec.adjustedCost, Bool.false_eq_true,
      if_false]
    linarith)

/-- **Main math-level theorem.** One run of the ported reference strategy with our labels decides
`θ < v k` under the gap promise. -/
theorem decide_by_strategy (P : Params C δ Δ K T) (hR : 2 * K ≤ R) (hR0 : 0 < R)
    (gap : θ + Δ ≤ C.v k ∨ C.v k ≤ θ - Δ) :
    Tree.run (reply C δ θ k)
      (Campaign.referenceStrategy R (Campaign.rounds (2*n+1) R) (dummy n)) [] =
      decide (θ < C.v k) := by
  have hΔ : 0 < Δ := by
    have := P.hΔ; have := P.hδ
    have : (0:ℚ) < 2 * δ * ((T:ℚ) + 1) := by positivity
    linarith
  rcases gap with hk | hk
  · have hc := Campaign.recover_sign (hidden P hR true) hR0
    rw [Tree.run_eq_of_correct _ _ hc _ (forced_pos P hR hk)]
    simp only [hidden]; symm; simp only [decide_eq_true_eq]; linarith
  · have hc := Campaign.recover_sign (hidden P hR false) hR0
    rw [Tree.run_eq_of_correct _ _ hc _ (forced_neg P hR hk)]
    simp only [hidden]; symm; simp only [decide_eq_false_iff_not, not_lt]; linarith

/-- The query count of that run. -/
theorem decide_by_strategy_queries (R : ℕ) :
    (Campaign.referenceStrategy R (Campaign.rounds (2*n+1) R) (dummy n)).height ≤
      2 ^ 1510 * (2*n+1 + (R + 1).log2 + 1) ^ 1510 :=
  Campaign.recursive_query_bound_machine R (dummy n)

end SSG28Search
