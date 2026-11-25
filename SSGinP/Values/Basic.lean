module

public import SSGinP.Machine.Reply

@[expose] public section

/-!
# SSGinP.Values.Basic: values of all nodes and optimal strategies, from threshold tests

Engine-independent part.  A *threshold test* for node `k` is any function `c : ℚ → Bool`; it is `Fuzzy c v Δ`
when `c θ = true` whenever `θ + Δ ≤ v` and `c θ = false` whenever `v ≤ θ - Δ` (nothing is asked when
`|v - θ| < Δ`).

* `bisect`, `approx`      : `m` bisection steps on `[0,1]`, one test per step; `approx_close`:
                            `|approx c m - v| < 1/2^(m+1) + Δ`.
* `solveWith call G`      : stopping test by peeling; `2n+1` bisection steps per node; greedy arc choice read off
                            the approximations; Gauss–Jordan on its linear system; check `F y = y`; output `y`
                            with the greedy strategies of `y`.
* `IsSolution G y σ τ`    : from every node `i`, `σ` guarantees arrival at terminal-1 with probability at least
                            `y i` against every min strategy, and `τ` keeps it at most `y i` against every max
                            strategy.  `isSolution_unique`: such a `y` is unique.
* `solveWith_sound`       : ANY answer `some s` (whatever the tests say) has `StoppingGame G`, `Stable G s.value`
                            and `IsSolution`.
* `solveWith_complete`    : on a Stopping Game with tests that are fuzzy for the stable assignment `v` with
                            `Δ = 1/(4·9^n)`, the answer is `some ⟨v, greedyMax G v, greedyMin G v⟩`.
* `solveWith_not_stopping`: on a game that is not a Stopping Game the answer is `none`.
* `thresholds`, `solveWith_congr`, `thresholds_dyadic` : the answer depends on the tests only at the
                            `n (2n+1)` thresholds actually asked; each is `a / 2^j` with `j ≤ 2n+1`, `a ≤ 2^j`.
-/

namespace SSGValues

open SSG SSG28Reply

variable {n : ℕ}

/-! ## bisection with a threshold test -/

/-- `m` bisection steps: the test at the midpoint decides which half is kept. -/
def bisect (c : ℚ → Bool) : ℕ → ℚ × ℚ → ℚ × ℚ
  | 0, I => I
  | m + 1, I =>
    if c ((I.1 + I.2) / 2) then bisect c m ((I.1 + I.2) / 2, I.2) else bisect c m (I.1, (I.1 + I.2) / 2)

/-- the thresholds at which `bisect` asks the test, in order. -/
def thresholds (c : ℚ → Bool) : ℕ → ℚ × ℚ → List ℚ
  | 0, _ => []
  | m + 1, I =>
    ((I.1 + I.2) / 2) ::
      (if c ((I.1 + I.2) / 2) then thresholds c m ((I.1 + I.2) / 2, I.2) else thresholds c m (I.1, (I.1 + I.2) / 2))

theorem thresholds_length (c : ℚ → Bool) : ∀ (m : ℕ) (I : ℚ × ℚ), (thresholds c m I).length = m
  | 0, _ => rfl
  | m + 1, I => by
    simp only [thresholds, List.length_cons]
    split <;> rw [thresholds_length c m]

/-- `bisect` uses the test only at its thresholds. -/
theorem bisect_congr (c c' : ℚ → Bool) : ∀ (m : ℕ) (I : ℚ × ℚ), (∀ θ ∈ thresholds c m I, c θ = c' θ) →
    bisect c m I = bisect c' m I
  | 0, _, _ => rfl
  | m + 1, I, h => by
    have h0 : c ((I.1 + I.2) / 2) = c' ((I.1 + I.2) / 2) := h _ (by simp [thresholds])
    simp only [bisect, ← h0]
    cases hc : c ((I.1 + I.2) / 2)
    · simp only [Bool.false_eq_true, if_false]
      exact bisect_congr c c' m _ (fun θ hθ => h θ (by simp [thresholds, hc, hθ]))
    · simp only [if_true]
      exact bisect_congr c c' m _ (fun θ hθ => h θ (by simp [thresholds, hc, hθ]))

/-- a threshold test for the number `v` that is right whenever the threshold is at distance `≥ Δ` from `v`. -/
def Fuzzy (c : ℚ → Bool) (v Δ : ℚ) : Prop :=
  (∀ θ, θ + Δ ≤ v → c θ = true) ∧ (∀ θ, v ≤ θ - Δ → c θ = false)

theorem bisect_inv {c : ℚ → Bool} {v Δ : ℚ} (hc : Fuzzy c v Δ) : ∀ (m : ℕ) (I : ℚ × ℚ),
    I.1 - Δ < v → v < I.2 + Δ →
    (bisect c m I).1 - Δ < v ∧ v < (bisect c m I).2 + Δ ∧ (bisect c m I).2 - (bisect c m I).1 = (I.2 - I.1) / 2 ^ m
  | 0, I, h1, h2 => ⟨h1, h2, by simp [bisect]⟩
  | m + 1, I, h1, h2 => by
    simp only [bisect]
    cases hm : c ((I.1 + I.2) / 2)
    · simp only [Bool.false_eq_true, if_false]
      have hv : v < (I.1 + I.2) / 2 + Δ := by
        by_contra hlt; push Not at hlt
        have := hc.1 _ hlt; rw [hm] at this; cases this
      obtain ⟨a, b, e⟩ := bisect_inv hc m (I.1, (I.1 + I.2) / 2) h1 hv
      refine ⟨a, b, ?_⟩
      rw [e, pow_succ]; field_simp; ring
    · simp only [if_true]
      have hv : (I.1 + I.2) / 2 - Δ < v := by
        by_contra hlt; push Not at hlt
        have := hc.2 _ hlt; rw [hm] at this; cases this
      obtain ⟨a, b, e⟩ := bisect_inv hc m ((I.1 + I.2) / 2, I.2) hv h2
      refine ⟨a, b, ?_⟩
      rw [e, pow_succ]; field_simp; ring

/-- the approximation after `m` bisection steps on `[0,1]`: the midpoint of the last interval. -/
def approx (c : ℚ → Bool) (m : ℕ) : ℚ := ((bisect c m (0, 1)).1 + (bisect c m (0, 1)).2) / 2

theorem approx_close {c : ℚ → Bool} {v Δ : ℚ} (hc : Fuzzy c v Δ) (hΔ : 0 < Δ) (hv : 0 ≤ v ∧ v ≤ 1) (m : ℕ) :
    |approx c m - v| < 1 / 2 ^ (m + 1) + Δ := by
  obtain ⟨a, b, e⟩ := bisect_inv hc m (0, 1) (by simp; linarith [hv.1]) (by simp; linarith [hv.2])
  simp only [sub_zero] at e
  have e2 : (1 : ℚ) / 2 ^ (m + 1) = (1 / 2 ^ m) / 2 := by rw [pow_succ]; field_simp
  unfold approx
  rw [e2, ← e, abs_lt]
  constructor <;> linarith

/-- every threshold asked from a dyadic interval `[a/2^j, (a+1)/2^j] ⊆ [0,1]` is `a'/2^j'` with `j' ≤ j + m`. -/
theorem thresholds_dyadic_aux (c : ℚ → Bool) : ∀ (m j a : ℕ), a + 1 ≤ 2 ^ j →
    ∀ θ ∈ thresholds c m ((a : ℚ) / 2 ^ j, ((a : ℚ) + 1) / 2 ^ j),
      ∃ j' a' : ℕ, j' ≤ j + m ∧ a' ≤ 2 ^ j' ∧ θ = (a' : ℚ) / 2 ^ j'
  | 0, _, _, _, θ, h => by simp [thresholds] at h
  | m + 1, j, a, ha, θ, h => by
    have emid : ((a : ℚ) / 2 ^ j + ((a : ℚ) + 1) / 2 ^ j) / 2 = ((2 * a + 1 : ℕ) : ℚ) / 2 ^ (j + 1) := by
      push_cast; rw [pow_succ]; field_simp; ring
    have eL : ((a : ℚ) / 2 ^ j) = ((2 * a : ℕ) : ℚ) / 2 ^ (j + 1) := by
      push_cast; rw [pow_succ]; field_simp
    have eR : (((a : ℚ) + 1) / 2 ^ j) = (((2 * a + 1 : ℕ) : ℚ) + 1) / 2 ^ (j + 1) := by
      push_cast; rw [pow_succ]; field_simp; ring
    have emid' : ((2 * a + 1 : ℕ) : ℚ) / 2 ^ (j + 1) = (((2 * a : ℕ) : ℚ) + 1) / 2 ^ (j + 1) := by push_cast; ring
    have hp : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
    simp only [thresholds, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨j + 1, 2 * a + 1, by omega, by omega, by rw [h, emid]⟩
    · rw [emid] at h
      split at h
      · rw [eR] at h
        obtain ⟨j', a', h1, h2, h3⟩ := thresholds_dyadic_aux c m (j + 1) (2 * a + 1) (by omega) θ h
        exact ⟨j', a', by omega, h2, h3⟩
      · rw [eL, emid'] at h
        obtain ⟨j', a', h1, h2, h3⟩ := thresholds_dyadic_aux c m (j + 1) (2 * a) (by omega) θ h
        exact ⟨j', a', by omega, h2, h3⟩

/-- every threshold asked in `m` bisection steps on `[0,1]` is `a / 2^j` with `j ≤ m` and `a ≤ 2^j`. -/
theorem thresholds_dyadic (c : ℚ → Bool) (m : ℕ) (θ : ℚ) (h : θ ∈ thresholds c m (0, 1)) :
    ∃ j a : ℕ, j ≤ m ∧ a ≤ 2 ^ j ∧ θ = (a : ℚ) / 2 ^ j := by
  have := thresholds_dyadic_aux c m 0 0 (by norm_num) θ (by simpa using h)
  simpa using this

/-! ## values and optimal strategies -/

/-- **`y` is the vector of values and `σ`, `τ` are optimal strategies**: from every node `i`, the max strategy
`σ` guarantees, against every min strategy `τ'`, arrival at terminal-1 with probability at least `y i`; and the
min strategy `τ` guarantees, against every max strategy `σ'`, that the probability of arrival at terminal-1
(within any number `T` of steps) is at most `y i`. -/
def IsSolution (G : Game n) (y : Fin n → ℚ) (σ : MaxStrategy n) (τ : MinStrategy n) : Prop :=
  ∀ i : Fin n, (∀ τ' : MinStrategy n, ArrivesWithProbAtLeast G σ τ' i (y i)) ∧
    (∀ (σ' : MaxStrategy n) (T : ℕ), arrivalProb G σ' τ T i ≤ y i)

/-- audit lemma: the min player's half says exactly "arrival with probability greater than `y i` never
happens". -/
theorem isSolution_min_iff (G : Game n) (σ' : MaxStrategy n) (τ : MinStrategy n) (i : Fin n) (c : ℚ) :
    (∀ T : ℕ, arrivalProb G σ' τ T i ≤ c) ↔ ¬ ArrivesWithProbGreater G σ' τ i c := by
  unfold ArrivesWithProbGreater; push Not; rfl

/-- audit lemma: the vector of values is unique (so `IsSolution` pins `y` down, on any game). -/
theorem isSolution_unique (G : Game n) (y y' : Fin n → ℚ) (σ σ' : MaxStrategy n) (τ τ' : MinStrategy n)
    (h : IsSolution G y σ τ) (h' : IsSolution G y' σ' τ') : y = y' := by
  have one : ∀ (a b : Fin n → ℚ) (s s' : MaxStrategy n) (t t' : MinStrategy n),
      IsSolution G a s t → IsSolution G b s' t' → ∀ i, a i ≤ b i := by
    intro a b s s' t t' ha hb i
    by_contra hlt; push Not at hlt
    obtain ⟨T, hT⟩ := (ha i).1 t' ((a i - b i) / 2) (by linarith)
    have := (hb i).2 s T
    linarith
  funext i
  exact le_antisymm (one y y' σ σ' τ τ' h h' i) (one y' y σ' σ τ' τ h' h i)

/-- **the stable assignment of a Stopping Game is the vector of values, and its greedy strategies are
optimal.** -/
theorem greedy_isSolution (G : Game n) (hs : StoppingGame G) (v : Fin n → ℚ) (hv : F G v = v) :
    IsSolution G v (greedyMax G v) (greedyMin G v) := by
  have hall := peelAll_of_stoppingGame G hs
  have hr := prank_ranked G hall
  intro i
  constructor
  · intro τ'
    refine (atLeast_iff_arrive1 _ _ _ _ _).mpr fun k => ⟨2 ^ (k + 1) * 3 ^ n, ?_⟩
    have g := optMax_guarantee G hall v hv i k _ le_rfl (posS τ')
    rw [optMax_eq, ← arrive1_eq_win1] at g
    exact g
  · intro σ' T
    have up := win_upper G (prank G) hr v hv (posS σ') T [] i
    rw [optMin_eq, ← arrive1_eq_win1, arrive1_eq] at up
    have pp : (0 : ℚ) < 2 ^ T := by positivity
    rw [mul_comm] at up
    exact le_of_mul_le_mul_right up pp

/-! ## the procedure -/

/-- the output: a value for every node, a max strategy and a min strategy. -/
structure Solution (n : ℕ) where
  value : Fin n → ℚ
  maxStrategy : MaxStrategy n
  minStrategy : MinStrategy n

/-- number of bisection steps per node. -/
def steps (n : ℕ) : ℕ := 2 * n + 1

/-- the approximate values: `steps n` bisection steps for every node `k`, with the test `call k`. -/
def approxVec (call : Fin n → ℚ → Bool) : Fin n → ℚ := fun k => approx (call k) (steps n)

/-- **the procedure**, for any family of threshold tests `call k θ` ("is the value of node `k` greater than
`θ`?"): reject unless peeling succeeds (Stopping Game); approximate every value by bisection; read the greedy
arc choice off the approximations; solve its linear system by Gauss–Jordan; check `F y = y`; return `y` and
its greedy strategies. -/
def solveWith (call : Fin n → ℚ → Bool) (G : Game n) : Option (Solution n) :=
  if peelAll G = true then
    match gj (chainA G (choice G (approxVec call))) (chainB G (choice G (approxVec call))) with
    | none => none
    | some y => if F G y = y then some ⟨y, greedyMax G y, greedyMin G y⟩ else none
  else none

/-- **soundness, whatever the tests answer**: an answer `some s` is only given on a Stopping Game, `s.value`
is its stable assignment, and it is the vector of values with `s.maxStrategy`, `s.minStrategy` optimal. -/
theorem solveWith_sound (call : Fin n → ℚ → Bool) (G : Game n) (s : Solution n) (h : solveWith call G = some s) :
    StoppingGame G ∧ Stable G s.value ∧ IsSolution G s.value s.maxStrategy s.minStrategy := by
  unfold solveWith at h
  split at h
  · rename_i hp
    have hs := (stoppingGame_iff_peelAll G).mpr hp
    split at h
    · cases h
    · split at h
      · rename_i y _ hy
        cases h
        exact ⟨hs, (stable_iff G y).mpr hy, greedy_isSolution G hs y hy⟩
      · cases h
  · cases h

/-- on a game that is not a Stopping Game the answer is `none`. -/
theorem solveWith_not_stopping (call : Fin n → ℚ → Bool) (G : Game n) (hs : ¬ StoppingGame G) :
    solveWith call G = none := by
  unfold solveWith
  rw [if_neg]
  rw [← stoppingGame_iff_peelAll]; exact hs

theorem steps_err (n : ℕ) : 1 / 2 ^ (steps n + 1) + Delta n ≤ 1 / (2 * 3 ^ n : ℚ) := by
  have h4 : (3 : ℚ) ^ n ≤ 4 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h9 : (3 : ℚ) ^ n ≤ 9 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h3 : (0 : ℚ) < 3 ^ n := by positivity
  have e : (2 : ℚ) ^ (steps n + 1) = 4 * 4 ^ n := by
    unfold steps
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul]; norm_num; rw [pow_succ]; ring
  have a : (1 : ℚ) / 2 ^ (steps n + 1) ≤ 1 / (4 * 3 ^ n) := by
    rw [e]; exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have b : Delta n ≤ 1 / (4 * 3 ^ n) := by
    unfold Delta; exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have c : (1 : ℚ) / (4 * 3 ^ n) + 1 / (4 * 3 ^ n) = 1 / (2 * 3 ^ n) := by field_simp; ring
  linarith

/-- **completeness**: on a Stopping Game with stable assignment `v`, if every test `call k` is right at
distance `≥ 1/(4·9^n)` from `v k`, the procedure returns `v` with its greedy strategies. -/
theorem solveWith_complete (call : Fin n → ℚ → Bool) (G : Game n) (hs : StoppingGame G) (v : Fin n → ℚ)
    (hv : F G v = v) (hc : ∀ k, Fuzzy (call k) (v k) (Delta n)) :
    solveWith call G = some ⟨v, greedyMax G v, greedyMin G v⟩ := by
  have hall := peelAll_of_stoppingGame G hs
  have hr := prank_ranked G hall
  have hb := fix_bounds G (prank G) hr v hv
  have hΔ : 0 < Delta n := by unfold Delta; positivity
  have hx : ∀ i, |approxVec call i - v i| < 1 / (2 * 3 ^ n) := fun i =>
    lt_of_lt_of_le (approx_close (hc i) hΔ (hb i) (steps n)) (steps_err n)
  obtain ⟨_, hgj⟩ := greedy_exact G hall v hv (approxVec call) hx
  unfold solveWith
  rw [if_pos ((stoppingGame_iff_peelAll G).mp hs), hgj]
  simp [hv]

/-- the thresholds asked for node `k`. -/
def asked (call : Fin n → ℚ → Bool) (k : Fin n) : List ℚ := thresholds (call k) (steps n) (0, 1)

/-- **cost: number of tests.** For every node, exactly `2n+1` thresholds are asked (so `n (2n+1)` tests in
all), and the answer of the procedure depends on the tests only through the answers at these thresholds. -/
theorem solveWith_congr (call call' : Fin n → ℚ → Bool) (G : Game n) :
    (∀ k, (asked call k).length = 2 * n + 1) ∧
    ((∀ k, ∀ θ ∈ asked call k, call k θ = call' k θ) → solveWith call G = solveWith call' G) := by
  refine ⟨fun k => thresholds_length _ _ _, fun h => ?_⟩
  have e : approxVec call = approxVec call' := by
    funext k; unfold approxVec approx
    rw [bisect_congr (call k) (call' k) (steps n) (0, 1) (h k)]
  unfold solveWith; rw [e]

/-- **cost: the thresholds.** Every threshold asked is `a / 2^j` with `j ≤ 2n+1` and `a ≤ 2^j`. -/
theorem asked_dyadic (call : Fin n → ℚ → Bool) (k : Fin n) (θ : ℚ) (h : θ ∈ asked call k) :
    ∃ j a : ℕ, j ≤ 2 * n + 1 ∧ a ≤ 2 ^ j ∧ θ = (a : ℚ) / 2 ^ j :=
  thresholds_dyadic (call k) (steps n) θ h

end SSGValues
