module

public import SSGinP.Machine.Reply
public import SSGinP.Search.SearchTree
public import SSGinP.Search.SingleCall

@[expose] public section

/-!
# SSGinP.Search.Decision: stopping simple stochastic games are decided by polynomially many
evaluations of the value operator, through the ported price search

* `SSG.decision_by_search` (math level, no machine): for every Stopping Game `G`, running the ported
  reference strategy tree of openai_math on `2n+1` goods against `SSG28Reply.replyGood G θ δ`
  returns `true` iff `ValueAtLeastHalf G` (θ = thetaGe n), resp. iff `ValueGreaterHalf G`
  (θ = thetaGt n). The tree has height `≤ 2^1510 (2n+1 + log2 (R+1) + 1)^1510` (`R = 128·27^n`) and
  every price it ever queries has bit size `≤ pricePolynomial.eval (2n+1 + R.size + 1)`.
* `SSG.decision_by_machine` (machine level): the fixed ported BitProgram `p` with oracle
  `ssgReply G θ δ` on input `priceInput R (dummy n)` halts within
  `coefficient · (2n+1 + log2 (R+1) + 1)^degree` bit steps with output
  `[decide (StoppingGame G ∧ ValueAtLeastHalf G)]` (resp. `>`), for EVERY game `G` (non-stopping
  games get all replies `false`, hence output `[false]`).
-/

namespace SSG

open SSG28Search SSG28Reply OAI.Optimization.LinearProgramming OracleSpec PriceGame

variable {n : ℕ}

/-! ### Monotonicity and the cone bounds -/

theorem ev_mono (G : Game n) {x y : Fin n → ℚ} (h : ∀ j, x j ≤ y j) (j : Fin n) :
    ev G x j ≤ ev G y j := by
  unfold ev; cases G.nodeType j <;> simp [h j]

theorem F_mono (G : Game n) {x y : Fin n → ℚ} (h : ∀ j, x j ≤ y j) (i : Fin n) :
    F G x i ≤ F G y i := by
  have e := ev_mono G h
  unfold F
  split
  · exact le_refl _
  · exact le_refl _
  · exact max_le_max (e _) (e _)
  · exact min_le_min (e _) (e _)
  · exact div_le_div_of_nonneg_right (add_le_add (e _) (e _)) (by norm_num)

theorem stable_point_exists (G : Game n) (hs : StoppingGame G) : ∃ v, F G v = v := by
  obtain ⟨v, hv, -⟩ := stable_exists_unique G hs
  exact ⟨v, (stable_iff G v).mp hv⟩

/-- The value vector (the unique stable assignment) of a Stopping Game. -/
noncomputable def val (G : Game n) (hs : StoppingGame G) : Fin n → ℚ :=
  (stable_point_exists G hs).choose

theorem val_fix (G : Game n) (hs : StoppingGame G) : F G (val G hs) = val G hs :=
  (stable_point_exists G hs).choose_spec

theorem gam_pos_D2 (n : ℕ) : 0 < gam n := by unfold gam; positivity
theorem gam_le_one (n : ℕ) : gam n ≤ 1 := by
  unfold gam; rw [div_le_one (by positivity)]
  have : (1 : ℚ) ≤ 3 ^ n := one_le_pow₀ (by norm_num); linarith

/-- **The cone of a Stopping Game**: `F`, its value vector, the weights `wt` and `γ = gam n`. -/
noncomputable def ssgCone (G : Game n) (hs : StoppingGame G) : Cone n where
  F := F G
  v := val G hs
  w := wt G
  γ := gam n
  hw := wt_bounds G
  hv := fix_bounds G (prank G) (prank_ranked G (peelAll_of_stoppingGame G hs)) _ (val_fix G hs)
  hγ := ⟨gam_pos_D2 n, gam_le_one n⟩
  lower := by
    intro x M hM hx i
    have hall := peelAll_of_stoppingGame G hs
    let z : Fin n → ℚ := fun j => min (x j) (val G hs j)
    have hz : ∀ j, |z j - val G hs j| ≤ M * wt G j := by
      intro j
      have h1 := hx j
      have : z j ≤ val G hs j := min_le_right _ _
      have : val G hs j - M * wt G j ≤ z j := le_min h1 (by nlinarith [(wt_bounds G j).1])
      rw [abs_le]; constructor <;> linarith
    have hc := contraction G hall z (val G hs) M hM hz i
    rw [val_fix G hs] at hc
    have hmono := F_mono G (fun j => (min_le_left (x j) (val G hs j) : z j ≤ x j)) i
    have := (abs_le.mp hc).1
    linarith
  upper := by
    intro x M hM hx i
    have hall := peelAll_of_stoppingGame G hs
    let z : Fin n → ℚ := fun j => max (x j) (val G hs j)
    have hz : ∀ j, |z j - val G hs j| ≤ M * wt G j := by
      intro j
      have h1 := hx j
      have : val G hs j ≤ z j := le_max_right _ _
      have : z j ≤ val G hs j + M * wt G j := max_le h1 (by nlinarith [(wt_bounds G j).1])
      rw [abs_le]; constructor <;> linarith
    have hc := contraction G hall z (val G hs) M hM hz i
    rw [val_fix G hs] at hc
    have hmono := F_mono G (fun j => (le_max_left (x j) (val G hs j) : x j ≤ z j)) i
    have := (abs_le.mp hc).2
    linarith

/-! ### The reply is the abstract label -/

theorem replyGood_eq_label (G : Game n) (hs : StoppingGame G) (θ δ : ℚ) (g : Fin (2*n+1))
    (q : Fin (2*n+1) → ℚ) :
    replyGood G θ δ g q = label (ssgCone G hs) δ θ G.startNode g q := by
  rcases goods_cases g with rfl | ⟨l, rfl⟩ | ⟨l, rfl⟩
  · rw [label_dummy, replyGood_dummy]; rfl
  · rw [label_up, replyGood_up]; rfl
  · rw [label_down, replyGood_down]; rfl

/-! ### Constants satisfy `Params` -/

theorem pow9 (n : ℕ) : (9 : ℚ) ^ n = (3 ^ n) ^ 2 := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num
theorem pow27 (n : ℕ) : (27 : ℚ) ^ n = (3 ^ n) ^ 3 := by
  rw [← pow_mul, mul_comm, pow_mul]; norm_num

theorem params (G : Game n) (hs : StoppingGame G) :
    Params (ssgCone G hs) (rDelta n) (Delta n) (rK n) (rT n) where
  hδ := by unfold rDelta; positivity
  hT := by
    show 1 ≤ ((4 * 3 ^ n : ℕ) : ℚ) * gam n
    unfold gam; push_cast; rw [mul_one_div, div_self (by positivity)]
  hΔ := by
    unfold rDelta Delta rT
    push_cast
    rw [pow9, pow27]
    have ha : (1 : ℚ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
    set a : ℚ := 3 ^ n
    have : 2 * (1 / (64 * a ^ 3)) * (4 * a + 1) = (8 * a + 2) / (64 * a ^ 3) := by
      field_simp; ring
    rw [this, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos (show (0:ℚ) < a by linarith) 2, pow_pos (show (0:ℚ) < a by linarith) 3]
  hTK := by
    unfold rT rK
    have : 3 ^ n ≤ 27 ^ n := Nat.pow_le_pow_left (by norm_num) n
    omega
  hK := by unfold rDelta rK; push_cast; simp

/-! ### The threshold gap -/

theorem half_gap (G : Game n) (hs : StoppingGame G) :
    2 * val G hs G.startNode = 1 ∨ 1 / (3 ^ n : ℚ) ≤ |2 * val G hs G.startNode - 1| := by
  obtain ⟨D, hD0, hD3, hz⟩ := denom_bound G (prank G)
    (prank_ranked G (peelAll_of_stoppingGame G hs)) _ (val_fix G hs)
  obtain ⟨z, hz⟩ := hz G.startNode
  set v := val G hs G.startNode
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD0
  by_cases h : 2 * z = (D : ℤ)
  · left
    have : (2 : ℚ) * z = D := by exact_mod_cast h
    have : (D : ℚ) * (2 * v) = D * 1 := by
      calc (D : ℚ) * (2 * v) = 2 * (D * v) := by ring
        _ = 2 * z := by rw [hz]
        _ = D * 1 := by rw [mul_one]; exact this
    exact mul_left_cancel₀ hDq.ne' this
  · right
    have h1 : (1 : ℤ) ≤ |2 * z - (D : ℤ)| := Int.one_le_abs (sub_ne_zero.mpr h)
    have h1q : (1 : ℚ) ≤ |2 * (z : ℚ) - D| := by exact_mod_cast h1
    have heq : 2 * v - 1 = (2 * (z : ℚ) - D) / D := by
      rw [← hz]; field_simp
    rw [heq, abs_div, abs_of_pos hDq]
    have hD3q : (D : ℚ) ≤ 3 ^ n := by exact_mod_cast hD3
    calc 1 / (3 ^ n : ℚ) ≤ 1 / D := one_div_le_one_div_of_le hDq hD3q
      _ ≤ |2 * (z : ℚ) - D| / D := div_le_div_of_nonneg_right h1q hDq.le

theorem two_delta_le (n : ℕ) : 2 * Delta n ≤ 1 / (2 * 3 ^ n) := by
  unfold Delta; rw [pow9]
  have ha : (1 : ℚ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  set a : ℚ := 3 ^ n
  rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem gapGe (G : Game n) (hs : StoppingGame G) :
    (thetaGe n + Delta n ≤ (ssgCone G hs).v G.startNode ∨
      (ssgCone G hs).v G.startNode ≤ thetaGe n - Delta n) ∧
    (thetaGe n < (ssgCone G hs).v G.startNode ↔ 1 ≤ 2 * val G hs G.startNode) := by
  show (thetaGe n + Delta n ≤ val G hs G.startNode ∨ val G hs G.startNode ≤ thetaGe n - Delta n) ∧
    (thetaGe n < val G hs G.startNode ↔ 1 ≤ 2 * val G hs G.startNode)
  have h2 := two_delta_le n
  have hΔ : 0 < Delta n := by unfold Delta; positivity
  have ha : (0 : ℚ) < 3 ^ n := by positivity
  unfold thetaGe
  rcases half_gap G hs with h | h
  · constructor
    · left; linarith
    · constructor <;> intro _ <;> linarith
  · by_cases hv : 1 ≤ 2 * val G hs G.startNode
    · exact ⟨Or.inl (by linarith), ⟨fun _ => hv, fun _ => by linarith⟩⟩
    · push Not at hv
      rw [abs_of_neg (by linarith)] at h
      have : 1 / (2 * 3 ^ n : ℚ) = (1 / 3 ^ n) / 2 := by field_simp
      refine ⟨Or.inr (by linarith), ⟨fun h' => by linarith, fun h' => by linarith⟩⟩

theorem gapGt (G : Game n) (hs : StoppingGame G) :
    (thetaGt n + Delta n ≤ (ssgCone G hs).v G.startNode ∨
      (ssgCone G hs).v G.startNode ≤ thetaGt n - Delta n) ∧
    (thetaGt n < (ssgCone G hs).v G.startNode ↔ 1 < 2 * val G hs G.startNode) := by
  show (thetaGt n + Delta n ≤ val G hs G.startNode ∨ val G hs G.startNode ≤ thetaGt n - Delta n) ∧
    (thetaGt n < val G hs G.startNode ↔ 1 < 2 * val G hs G.startNode)
  have h2 := two_delta_le n
  have hΔ : 0 < Delta n := by unfold Delta; positivity
  unfold thetaGt
  rcases half_gap G hs with h | h
  · exact ⟨Or.inr (by linarith), ⟨fun h' => by linarith, fun h' => by linarith⟩⟩
  · by_cases hv : 1 < 2 * val G hs G.startNode
    · rw [abs_of_pos (by linarith)] at h
      have : 1 / (2 * 3 ^ n : ℚ) = (1 / 3 ^ n) / 2 := by field_simp
      exact ⟨Or.inl (by linarith), ⟨fun _ => hv, fun _ => by linarith⟩⟩
    · push Not at hv
      exact ⟨Or.inr (by linarith), ⟨fun h' => by linarith, fun h' => absurd h' (by linarith)⟩⟩

/-! ### The math-level decision theorem -/

theorem rR_pos (n : ℕ) : 0 < rR n := by unfold rR rK; positivity

theorem reply_eq (G : Game n) (hs : StoppingGame G) (θ δ : ℚ) :
    (fun (_ : List (Query (2*n+1) × Bool)) (q : Query (2*n+1)) => replyGood G θ δ q.index q.prices) =
      SSG28Search.reply (ssgCone G hs) δ θ G.startNode := by
  funext h q; exact replyGood_eq_label G hs θ δ q.index q.prices

/-- The ported price-bit cap of the campaign, for a generic round count (stated generically: Lean's
elaborator would otherwise try to evaluate `Campaign.rounds`). -/
theorem price_key (N R : ℕ) (a : Fin N) (t : ℕ → ℕ → ℕ) :
    (Computation.ofTree (Campaign.referenceStrategy R (t N R) a)).AllQueries
      (PricesBounded (Control.Wire.campaignPriceBits N R (t N R))) := by
  have := Control.Wire.campaignSolver_all_prices t ⟨N, R, a⟩
  exact this

/-- The reference strategy tree of the ported price search, on `2n+1` goods with range `rR n`. -/
noncomputable def searchTree (n : ℕ) : PriceGame.Tree (2*n+1) :=
  Campaign.referenceStrategy (rR n) (Campaign.rounds (2*n+1) (rR n)) (dummy n)

/-- Running the search tree against the SSG reply with threshold `θ`. -/
noncomputable def runSearch (G : Game n) (θ : ℚ) : Bool :=
  PriceGame.Tree.run (fun _ q => replyGood G θ (rDelta n) q.index q.prices) (searchTree n) []

theorem rR_size (n : ℕ) : (rR n).size ≤ 5 * n + 8 := by
  rw [Nat.size_le]
  unfold rR rK
  have : 27 ^ n ≤ 32 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have h32 : (32 : ℕ) ^ n = 2 ^ (5 * n) := by rw [pow_mul]; norm_num
  rw [show 5 * n + 8 = 8 + 5 * n by ring, pow_add, ← h32]
  have : 0 < 27 ^ n := by positivity
  omega

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 400 in
/-- **`SSG.decision_by_search`** (math level, no machine model). For every Stopping Game `G` on `n`
nodes, one run of the ported price-search strategy tree, whose oracle evaluates `F G` once per query,
decides the paper's problem (`θ = thetaGe n`) and Condon's strict variant (`θ = thetaGt n`); the tree
asks at most `2^1510 (2n+1 + log2 (rR n + 1) + 1)^1510` queries, `rR n = 128·27^n`, and every queried
price has bit size at most `pricePolynomial.eval (2n+1 + (rR n).size + 1)`, `(rR n).size ≤ 5n+8`. -/
theorem decision_by_search (G : Game n) (hs : StoppingGame G) :
    (runSearch G (thetaGe n) = true ↔ ValueAtLeastHalf G) ∧
    (runSearch G (thetaGt n) = true ↔ ValueGreaterHalf G) ∧
    (searchTree n).height ≤ 2 ^ 1510 * (2*n+1 + (rR n + 1).log2 + 1) ^ 1510 ∧
    (Computation.ofTree (searchTree n)).AllQueries
      (PricesBounded (N := 2*n+1) (Control.Wire.pricePolynomial.eval (2*n+1 + (rR n).size + 1))) := by
  have P := params G hs
  have hR : 2 * rK n ≤ rR n := le_rfl
  refine ⟨?_, ?_, decide_by_strategy_queries (n := n) (rR n), ?_⟩
  · unfold runSearch searchTree
    rw [reply_eq G hs, decide_by_strategy P hR (rR_pos n) (gapGe G hs).1, decide_eq_true_iff,
      (gapGe G hs).2, valueAtLeastHalf_iff G hs (val G hs) (val_fix G hs)]
  · unfold runSearch searchTree
    rw [reply_eq G hs, decide_by_strategy P hR (rR_pos n) (gapGt G hs).1, decide_eq_true_iff,
      (gapGt G hs).2, valueGreaterHalf_iff G hs (val G hs) (val_fix G hs)]
  · unfold searchTree
    have hT0 : Campaign.rounds (2*n+1) (rR n) ≤ (2*n+1 + (rR n).size + 1) ^ 300 :=
      (Campaign.rounds_eq _ _).le
    generalize hTT : Campaign.rounds (2*n+1) (rR n) = T at hT0 ⊢
    have h := price_key (2*n+1) (rR n) (dummy n) (fun _ _ => T)
    have hb := Control.Wire.campaignPriceBits_polynomial (2*n+1) (rR n) T hT0
    exact Computation.allQueries_mono _ _ (fun q hq i => (hq i).trans hb) _ h

/-! ### The machine-level instance -/

theorem ssgReply_eq_wordReply (G : Game n) (hs : StoppingGame G) (hok : okGame G = true)
    (θ δ : ℚ) (w : Word) :
    ssgReply G θ δ w = wordReply (ssgCone G hs) δ θ G.startNode w := by
  by_cases h : ∃ iq : Fin (2*n+1) × (Fin (2*n+1) → ℚ), priceQuery iq.1 iq.2 = w
  · obtain ⟨⟨i, q⟩, rfl⟩ := h
    rw [ssgReply_priceQuery, wordReply_priceQuery, hok, Bool.true_and, replyGood_eq_label G hs]
  · have h' : ¬ ∃ x : Fin (2*n+1) × (Fin (2*n+1) → ℚ), w = priceQuery x.1 x.2 :=
      fun ⟨x, hx⟩ => h ⟨x, hx.symm⟩
    simp only [ssgReply, h', dif_neg, not_false_eq_true, wordReply, h]

theorem okGame_iff (G : Game n) : okGame G = true ↔ WellFormed G ∧ StoppingGame G := by
  unfold okGame; rw [Bool.and_eq_true, decide_eq_true_iff, ← stoppingGame_iff_peelAll]

/-- one generic step: the run's answers are ssgReply's, its transcript satisfies `pricePost`. -/
theorem machine_output (G : Game n) (θ : ℚ) (Pr : Prop)
    (hθ : ∀ hs : StoppingGame G, (θ + Delta n ≤ (ssgCone G hs).v G.startNode ∨
      (ssgCone G hs).v G.startNode ≤ θ - Delta n) ∧ (θ < (ssgCone G hs).v G.startNode ↔ Pr))
    (history : Transcript) (output : Word)
    (hpost : pricePost (rR n) (dummy n) history output)
    (hans : ∀ e ∈ history, e.2 = [ssgReply G θ (rDelta n) e.1]) :
    ∃ b, output = [b] ∧ (b = true ↔ WellFormed G ∧ StoppingGame G ∧ Pr) := by
  by_cases hok : okGame G = true
  · obtain ⟨hwf, hs⟩ := (okGame_iff G).mp hok
    have hans' : ∀ e ∈ history, e.2 = [wordReply (ssgCone G hs) (rDelta n) θ G.startNode e.1] := by
      intro e he; rw [hans e he, ssgReply_eq_wordReply G hs hok]
    have := single_call_correct (params G hs) (le_rfl : 2 * rK n ≤ rR n) (hθ hs).1 history output
      hpost hans'
    refine ⟨_, this, ?_⟩
    rw [decide_eq_true_iff, (hθ hs).2]
    exact ⟨fun h => ⟨hwf, hs, h⟩, fun h => h.2.2⟩
  · have hf : okGame G = false := by simpa using hok
    have hout : output = [false] := by
      refine hpost.2.2 false Set.univ (fun _ => 0) (Set.mem_univ _) (fun _ _ => Nat.zero_le _) ?_
      intro i prices answer hmem _ _
      have ha : answer = [ssgReply G θ (rDelta n) (priceQuery i prices)] := hans _ hmem
      rw [ha, ssgReply_priceQuery, hf, Bool.false_and]
    refine ⟨false, hout, ?_⟩
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨hwf, hs, -⟩
    exact hok ((okGame_iff G).mpr ⟨hwf, hs⟩)

/-- **`SSG.decision_by_machine`**: one fixed bit machine (the ported `extremalSignRecovery` program),
on input `priceInput (rR n) (dummy n)` and with oracle `ssgReply G θ (rDelta n)`, halts within
`coefficient · (2n+1 + log2 (rR n + 1) + 1)^degree` bit steps (all query and answer bits included)
and outputs one bit that is `true` iff `SSGDecision G` (θ = thetaGe n), resp. `SSGDecisionStrict G`
(θ = thetaGt n), for every game `G`. -/
theorem decision_by_machine :
    ∃ (p : BitProgram) (coefficient degree : ℕ), ∀ (n : ℕ) (G : Game n),
      p.ComputesWithin (fun _ w => [ssgReply G (thetaGe n) (rDelta n) w]) (priceInput (rR n) (dummy n))
        (coefficient * (2*n+1 + (rR n + 1).log2 + 1) ^ degree)
        (fun h out => (∃ b, out = [b] ∧ (b = true ↔ SSGDecision G)) ∧
          ∀ e ∈ h, ∃ (i : Fin (2*n+1)) (q : Fin (2*n+1) → ℚ), e.1 = priceQuery i q) ∧
      p.ComputesWithin (fun _ w => [ssgReply G (thetaGt n) (rDelta n) w]) (priceInput (rR n) (dummy n))
        (coefficient * (2*n+1 + (rR n + 1).log2 + 1) ^ degree)
        (fun h out => (∃ b, out = [b] ∧ (b = true ↔ SSGDecisionStrict G)) ∧
          ∀ e ∈ h, ∃ (i : Fin (2*n+1)) (q : Fin (2*n+1) → ℚ), e.1 = priceQuery i q) := by
  obtain ⟨p, coefficient, degree, hp⟩ := PriceGame.extremalSignRecovery
  refine ⟨p, coefficient, degree, fun n G => ⟨?_, ?_⟩⟩
  · obtain ⟨el, c, hrun, hle, hhalt, hpost⟩ :=
      hp (2*n+1) (rR n) (by omega) (rR_pos n) (dummy n) (fun _ w => ssgReply G (thetaGe n) (rDelta n) w)
    refine ⟨el, c, hrun, hle, hhalt, ?_⟩
    have hans := run_transcript_answers p (ssgReply G (thetaGe n) (rDelta n)) hrun (by
      intro e he; simp [BitProgram.initial] at he)
    have := machine_output G (thetaGe n) (ValueAtLeastHalf G)
      (fun hs => ⟨(gapGe G hs).1, by rw [(gapGe G hs).2, valueAtLeastHalf_iff G hs (val G hs) (val_fix G hs)]⟩)
      _ _ hpost hans
    exact ⟨by simpa [SSGDecision] using this, hpost.1⟩
  · obtain ⟨el, c, hrun, hle, hhalt, hpost⟩ :=
      hp (2*n+1) (rR n) (by omega) (rR_pos n) (dummy n) (fun _ w => ssgReply G (thetaGt n) (rDelta n) w)
    refine ⟨el, c, hrun, hle, hhalt, ?_⟩
    have hans := run_transcript_answers p (ssgReply G (thetaGt n) (rDelta n)) hrun (by
      intro e he; simp [BitProgram.initial] at he)
    have := machine_output G (thetaGt n) (ValueGreaterHalf G)
      (fun hs => ⟨(gapGt G hs).1, by rw [(gapGt G hs).2, valueGreaterHalf_iff G hs (val G hs) (val_fix G hs)]⟩)
      _ _ hpost hans
    exact ⟨by simpa [SSGDecisionStrict] using this, hpost.1⟩

end SSG
