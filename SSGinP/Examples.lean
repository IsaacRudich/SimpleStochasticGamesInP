module

public import SSGinP.Theory.Play

@[expose] public section

/-!
# SSGinP.Examples: sanity examples for the definitions of SSGinP.GameFacts

All checks are kernel-checked (`decide`, `simp`, `norm_num`); no `native_decide`.

* (a) `exA`: an average node `a` with children terminal-1 and `a` itself. Arrival probabilities from `a`
  within `T = 0, 1, 2, 3` steps are `0, 1/2, 3/4, 7/8`; it is well-formed, a Stopping Game, and both
  `ValueAtLeastHalf` and `ValueGreaterHalf` hold, so `SSGDecision exA`.
* (b) `exB`: an average node with children terminal-0 and a min node that can move to terminal-0. The value is 0,
  so `¬ SSGDecision exB`.
* (c) `exC`: an average node with children terminal-0 and terminal-1. The value is exactly 1/2, so `SSGDecision exC`
  holds but `SSGDecisionStrict exC` fails: the two problems differ.
* (d) `exD`: two max nodes pointing at each other. It is well-formed but not a Stopping Game.
* (e) `exE`: two terminal-1 nodes, so it is not well-formed.
-/

namespace SSG.Examples

open SSG

/-! ## (a) -/

/-- nodes: `0` = average node `a` (childJ = terminal-1, childK = `a`), `1` = terminal-0, `2` = terminal-1; start `a`. -/
def exA : Game 3 where
  nodeType := (fun i => if i.val = 0 then .average else if i.val = 1 then .terminal0 else .terminal1)
  childJ := (fun i => if i.val = 0 then 2 else if i.val = 1 then 1 else 2)
  childK := (fun i => if i.val = 0 then 0 else if i.val = 1 then 1 else 2)
  startNode := 0

theorem exA_prob (σ : MaxStrategy 3) (τ : MinStrategy 3) :
    arrivalProb exA σ τ 0 0 = 0 ∧ arrivalProb exA σ τ 1 0 = 1 / 2 ∧
    arrivalProb exA σ τ 2 0 = 3 / 4 ∧ arrivalProb exA σ τ 3 0 = 7 / 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [arrivalProb, exA] <;> norm_num

theorem exA_wellFormed : WellFormed exA := by decide

theorem exA_stopping : StoppingGame exA := by
  rw [stoppingGame_iff_peelAll]; decide

theorem exA_valueGreaterHalf : ValueGreaterHalf exA :=
  ⟨fun _ => .j, fun τ => ⟨2, by
    change (1 : ℚ) / 2 < arrivalProb exA _ τ 2 0
    rw [(exA_prob _ τ).2.2.1]; norm_num⟩⟩

theorem exA_valueAtLeastHalf : ValueAtLeastHalf exA :=
  ⟨fun _ => .j, fun τ ε hε => ⟨2, by
    change (1 : ℚ) / 2 - ε ≤ arrivalProb exA _ τ 2 0
    rw [(exA_prob _ τ).2.2.1]
    linarith⟩⟩

theorem exA_decision : SSGDecision exA := ⟨exA_wellFormed, exA_stopping, exA_valueAtLeastHalf⟩

theorem exA_decisionStrict : SSGDecisionStrict exA := ⟨exA_wellFormed, exA_stopping, exA_valueGreaterHalf⟩

/-! ## (b) -/

/-- nodes: `0` = average (childJ = terminal-0, childK = min node `2`), `1` = terminal-0, `2` = min node
(childJ = terminal-0, childK = terminal-1), `3` = terminal-1; start `0`.  Value 0. -/
def exB : Game 4 where
  nodeType := (fun i => if i.val = 0 then .average else if i.val = 1 then .terminal0 else if i.val = 2 then .min else .terminal1)
  childJ := (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else if i.val = 2 then 1 else 3)
  childK := (fun i => if i.val = 0 then 2 else if i.val = 1 then 1 else if i.val = 2 then 3 else 3)
  startNode := 0

theorem exB_stopping : StoppingGame exB := by
  rw [stoppingGame_iff_peelAll]; decide

/-- the stable assignment of `exB`: values `0, 0, 0, 1` at nodes `0, 1, 2, 3`. -/
theorem exB_stable : F exB (fun i => if i.val = 3 then 1 else 0) = (fun i => if i.val = 3 then 1 else 0) := by
  funext i
  match i with
  | ⟨0, _⟩ => simp [F, ev, exB, Game.child]
  | ⟨1, _⟩ => simp [F, ev, exB, Game.child]
  | ⟨2, _⟩ => simp [F, ev, exB, Game.child]
  | ⟨3, _⟩ => simp [F, ev, exB, Game.child]
  | ⟨k + 4, h⟩ => exact absurd h (by omega)

theorem exB_not_decision : ¬ SSGDecision exB := by
  rintro ⟨_, hs, hv⟩
  have := (valueAtLeastHalf_iff exB hs _ exB_stable).mp hv
  norm_num [exB] at this

/-! ## (c) -/

/-- nodes: `0` = average (childJ = terminal-0, childK = terminal-1), `1` = terminal-0, `2` = terminal-1; start `0`.
Value exactly 1/2. -/
def exC : Game 3 where
  nodeType := (fun i => if i.val = 0 then .average else if i.val = 1 then .terminal0 else .terminal1)
  childJ := (fun i => if i.val = 0 then 1 else if i.val = 1 then 1 else 2)
  childK := (fun i => if i.val = 0 then 2 else if i.val = 1 then 1 else 2)
  startNode := 0

theorem exC_prob (σ : MaxStrategy 3) (τ : MinStrategy 3) :
    ∀ T, arrivalProb exC σ τ T 0 ≤ 1 / 2 ∧ (1 ≤ T → arrivalProb exC σ τ T 0 = 1 / 2) := by
  have t0 : ∀ T, arrivalProb exC σ τ T 1 = 0 := by intro T; cases T <;> simp [arrivalProb, exC]
  have t1 : ∀ T, arrivalProb exC σ τ T 2 = 1 := by intro T; cases T <;> simp [arrivalProb, exC]
  intro T
  cases T with
  | zero => simp [arrivalProb, exC]
  | succ T =>
    have e : arrivalProb exC σ τ (T + 1) 0 = (arrivalProb exC σ τ T 1 + arrivalProb exC σ τ T 2) / 2 := by
      simp [arrivalProb, exC]
    rw [e, t0, t1]; norm_num

theorem exC_wellFormed : WellFormed exC := by decide

theorem exC_stopping : StoppingGame exC := by
  rw [stoppingGame_iff_peelAll]; decide

theorem exC_decision : SSGDecision exC :=
  ⟨exC_wellFormed, exC_stopping, ⟨fun _ => .j, fun τ ε hε => ⟨1, by
    change (1 : ℚ) / 2 - ε ≤ arrivalProb exC _ τ 1 0
    rw [(exC_prob _ τ 1).2 le_rfl]
    linarith⟩⟩⟩

theorem exC_not_decisionStrict : ¬ SSGDecisionStrict exC := by
  rintro ⟨_, _, σ, h⟩
  obtain ⟨T, hT⟩ := h (fun _ => .j)
  have := (exC_prob σ (fun _ => .j) T).1
  change (1 : ℚ) / 2 < arrivalProb exC σ (fun _ => .j) T 0 at hT
  linarith

/-! ## (d) -/

/-- nodes: `0`, `1` = max nodes pointing at each other, `2` = terminal-0, `3` = terminal-1; start `0`. -/
def exD : Game 4 where
  nodeType := (fun i => if i.val = 0 then .max else if i.val = 1 then .max else if i.val = 2 then .terminal0 else .terminal1)
  childJ := (fun i => if i.val = 0 then 1 else if i.val = 1 then 0 else if i.val = 2 then 2 else 3)
  childK := (fun i => if i.val = 0 then 1 else if i.val = 1 then 0 else if i.val = 2 then 2 else 3)
  startNode := 0

theorem exD_wellFormed : WellFormed exD := by decide

theorem exD_not_stopping : ¬ StoppingGame exD := by
  rw [stoppingGame_iff_peelAll]; decide

/-! ## (e) -/

/-- nodes: `0`, `1` = terminal-1, `2` = terminal-0; start `0`: two terminal-1 nodes. -/
def exE : Game 3 where
  nodeType := (fun i => if i.val = 0 then .terminal1 else if i.val = 1 then .terminal1 else .terminal0)
  childJ := (fun i => if i.val = 0 then 0 else if i.val = 1 then 1 else 2)
  childK := (fun i => if i.val = 0 then 0 else if i.val = 1 then 1 else 2)
  startNode := 0

theorem exE_not_wellFormed : ¬ WellFormed exE := by decide

end SSG.Examples
