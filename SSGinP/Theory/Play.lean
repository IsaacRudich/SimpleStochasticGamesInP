module

public import SSGinP.Theory.Theory

@[expose] public section

/-!
# SSGinP.Theory.Play: the fixed point of `F` is the value of the game as defined by play

* `optMax`, `optMin`        : the greedy max / min strategies of a vector (computable).
* `win_upper`, `win_lower`  : against the greedy strategies, `P(reach 1 within T)` is `≤ v_u`, resp. `≥ v_u - P(no terminal)`.
* `unabs_decay`             : on a ranked game, `P(no terminal within T steps) ≤ 2·3^R/(T+1)` for ALL strategies.
* `stoppingByPlay_iff_peelAll`    : `StoppingByPlay G ↔ peelAll G = true` (the peeling test decides Condon's condition).
* `IsValueAt`, `fix_isValue`, `isValueAt_unique`: the value at `u` defined by play; the fixed point is it.
* `valueGreaterHalfByPlay_iff`         : for a stopping game, `ValueGreaterHalfByPlay G ↔ 1 < 2 v(start)`.
-/

namespace SSG

variable {n : ℕ}

/-- greedy max strategy (as a history-dependent strategy reading only the current node) for the vector `v`. -/
def optMax (G : Game n) (v : Fin n → ℚ) : HStrategy n
  | [] => .j
  | u :: _ => ArcChoice.ofBool (decide (ev G v (G.child u false) < ev G v (G.child u true)))

/-- greedy min strategy (as a history-dependent strategy reading only the current node) for the vector `v`. -/
def optMin (G : Game n) (v : Fin n → ℚ) : HStrategy n
  | [] => .j
  | u :: _ => ArcChoice.ofBool (decide (ev G v (G.child u true) < ev G v (G.child u false)))

theorem optMax_keep (G : Game n) (v : Fin n → ℚ) (hv : F G v = v) (h : List (Fin n)) (u : Fin n)
    (hk : G.nodeType u = .max) : ev G v (G.child u (optMax G v (u :: h)).toBool) = v u := by
  have e := congrFun hv u; unfold F at e; rw [hk] at e; simp only at e
  simp only [optMax]
  by_cases c : ev G v (G.child u false) < ev G v (G.child u true)
  · simp only [c, decide_true, toBool_ofBool]; rw [← e, max_eq_right (le_of_lt c)]
  · simp only [c, decide_false, toBool_ofBool]; rw [← e, max_eq_left (le_of_not_gt c)]

theorem optMin_keep (G : Game n) (v : Fin n → ℚ) (hv : F G v = v) (h : List (Fin n)) (u : Fin n)
    (hk : G.nodeType u = .min) : ev G v (G.child u (optMin G v (u :: h)).toBool) = v u := by
  have e := congrFun hv u; unfold F at e; rw [hk] at e; simp only at e
  simp only [optMin]
  by_cases c : ev G v (G.child u true) < ev G v (G.child u false)
  · simp only [c, decide_true, toBool_ofBool]; rw [← e, min_eq_right (le_of_lt c)]
  · simp only [c, decide_false, toBool_ofBool]; rw [← e, min_eq_left (le_of_not_gt c)]

section fixpoint
variable (G : Game n) (r : Fin n → ℕ) (hr : Ranked G r) (v : Fin n → ℚ) (hv : F G v = v)
include hr hv

theorem ev_fix (j : Fin n) : ev G v j = v j :=
  ev_of_fix G v (fun i _ => congrFun hv i) j

/-- **upper bound**: if the min player plays greedily, `P(arrival at terminal-1 within T) ≤ v_u` against every strategy of the max player. -/
theorem win_upper (σ : HStrategy n) : ∀ T h u, ((win1 G σ (optMin G v) T h u : ℤ) : ℚ) ≤ v u * 2 ^ T := by
  have hb := fix_bounds G r hr v hv
  have hyp := fun i => fix_cmp_hyp G v hv i
  have evf := ev_fix G r hr v hv
  intro T
  induction T with
  | zero =>
    intro h u
    simp only [win1, pow_zero, mul_one]
    split
    · rename_i hk; rw [(hyp u).2.2.2.2 hk]; simp
    · simp; exact (hb u).1
  | succ T ih =>
    intro h u
    have pp : (0 : ℚ) < 2 ^ T := by positivity
    simp only [win1, chosen_eq_child, ← child_false, ← child_true]
    cases hk : G.nodeType u with
    | terminal1 => rw [(hyp u).2.2.2.2 hk]; simp
    | terminal0 => rw [(hyp u).2.2.2.1 hk]; simp
    | max =>
      obtain ⟨_, _, hle⟩ := (hyp u).1 hk
      have i := ih (u :: h) (G.child u (σ (u :: h)).toBool)
      have m := hle (σ (u :: h)).toBool; rw [evf] at m
      have : v (G.child u (σ (u :: h)).toBool) * 2 ^ T ≤ v u * 2 ^ T := mul_le_mul_of_nonneg_right m (le_of_lt pp)
      push_cast; rw [pow_succ]; linarith
    | min =>
      have i := ih (u :: h) (G.child u (optMin G v (u :: h)).toBool)
      have m := optMin_keep G v hv h u hk; rw [evf] at m
      rw [m] at i
      push_cast; rw [pow_succ]; linarith
    | average =>
      have e := (hyp u).2.2.1 hk; rw [evf, evf] at e
      have ia := ih (u :: h) (G.child u false); have ib := ih (u :: h) (G.child u true)
      push_cast; rw [pow_succ]; nlinarith

/-- **lower bound**: if the max player plays greedily, `v_u ≤ P(arrival at terminal-1 within T) + P(no terminal within T)`. -/
theorem win_lower (τ : HStrategy n) : ∀ T h u,
    v u * 2 ^ T ≤ ((win1 G (optMax G v) τ T h u : ℤ) : ℚ) + ((unabs G (optMax G v) τ T h u : ℤ) : ℚ) := by
  have hb := fix_bounds G r hr v hv
  have hyp := fun i => fix_cmp_hyp G v hv i
  have evf := ev_fix G r hr v hv
  intro T
  induction T with
  | zero =>
    intro h u
    simp only [win1, unabs, pow_zero, mul_one]
    cases hk : G.nodeType u with
    | terminal1 => rw [(hyp u).2.2.2.2 hk]; simp
    | terminal0 => rw [(hyp u).2.2.2.1 hk]; simp
    | _ => simp; exact (hb u).2
  | succ T ih =>
    intro h u
    have pp : (0 : ℚ) < 2 ^ T := by positivity
    simp only [win1, unabs, chosen_eq_child, ← child_false, ← child_true]
    cases hk : G.nodeType u with
    | terminal1 => rw [(hyp u).2.2.2.2 hk]; simp
    | terminal0 => rw [(hyp u).2.2.2.1 hk]; simp
    | max =>
      have i := ih (u :: h) (G.child u (optMax G v (u :: h)).toBool)
      have m := optMax_keep G v hv h u hk; rw [evf] at m
      rw [m] at i
      push_cast; rw [pow_succ]; linarith
    | min =>
      obtain ⟨_, _, hle⟩ := (hyp u).2.1 hk
      have i := ih (u :: h) (G.child u (τ (u :: h)).toBool)
      have m := hle (τ (u :: h)).toBool; rw [evf] at m
      have : v u * 2 ^ T ≤ v (G.child u (τ (u :: h)).toBool) * 2 ^ T := mul_le_mul_of_nonneg_right m (le_of_lt pp)
      push_cast; rw [pow_succ]; linarith
    | average =>
      have e := (hyp u).2.2.1 hk; rw [evf, evf] at e
      have ia := ih (u :: h) (G.child u false); have ib := ih (u :: h) (G.child u true)
      push_cast; rw [pow_succ]; nlinarith
end fixpoint

theorem unabs_range (G : Game n) (σ τ : HStrategy n) :
    ∀ T h u, 0 ≤ unabs G σ τ T h u ∧ unabs G σ τ T h u ≤ 2 ^ T := by
  intro T
  induction T with
  | zero => intro h u; simp only [unabs, chosen_eq_child, ← child_false, ← child_true]; split <;> simp
  | succ T ih =>
    intro h u
    have e : (2 : ℤ) ^ (T + 1) = 2 * 2 ^ T := by rw [pow_succ]; ring
    simp only [unabs, chosen_eq_child, ← child_false, ← child_true]
    cases G.nodeType u with
    | terminal1 => simp <;> positivity
    | terminal0 => simp <;> positivity
    | max => have := ih (u :: h) (G.child u (σ (u :: h)).toBool); simp only; omega
    | min => have := ih (u :: h) (G.child u (τ (u :: h)).toBool); simp only; omega
    | average => have := ih (u :: h) (G.child u false); have := ih (u :: h) (G.child u true); simp only; omega

theorem win1_range (G : Game n) (σ τ : HStrategy n) :
    ∀ T h u, 0 ≤ win1 G σ τ T h u ∧ win1 G σ τ T h u ≤ 2 ^ T := by
  intro T
  induction T with
  | zero => intro h u; simp only [win1, chosen_eq_child, ← child_false, ← child_true]; split <;> simp
  | succ T ih =>
    intro h u
    have e : (2 : ℤ) ^ (T + 1) = 2 * 2 ^ T := by rw [pow_succ]; ring
    simp only [win1, chosen_eq_child, ← child_false, ← child_true]
    cases G.nodeType u with
    | terminal1 => simp <;> positivity
    | terminal0 => simp <;> positivity
    | max => have := ih (u :: h) (G.child u (σ (u :: h)).toBool); simp only; omega
    | min => have := ih (u :: h) (G.child u (τ (u :: h)).toBool); simp only; omega
    | average => have := ih (u :: h) (G.child u false); have := ih (u :: h) (G.child u true); simp only; omega

/-- potential `3^R (1 - 3^-r)`. -/
def pot (R r : ℕ) : ℚ := 3 ^ R * (1 - (1 / 3 : ℚ) ^ r)

theorem pot_facts (R r : ℕ) (hr : r ≤ R) : 0 ≤ pot R r ∧ pot R r ≤ 3 ^ R - 1 ∧ 1 ≤ 3 ^ R * (1 / 3 : ℚ) ^ r := by
  have hX : 1 ≤ (3 : ℚ) ^ R * (1 / 3 : ℚ) ^ r := by
    rw [show (3 : ℚ) ^ R = 3 ^ (R - r) * 3 ^ r by rw [← pow_add]; congr 1; omega, mul_assoc, ← mul_pow]
    norm_num; exact one_le_pow₀ (by norm_num)
  have h1 : (1 / 3 : ℚ) ^ r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h3 : (0 : ℚ) ≤ 3 ^ R := by positivity
  unfold pot
  refine ⟨mul_nonneg h3 (by linarith), by nlinarith, hX⟩

theorem pot_step (R r r' : ℕ) (hr : r ≤ R) (h : r' < r) :
    pot R r' ≤ pot R r - 2 * (3 ^ R * (1 / 3 : ℚ) ^ r) := by
  have : 3 * (1 / 3 : ℚ) ^ r ≤ (1 / 3 : ℚ) ^ r' := by
    have e : (1 / 3 : ℚ) ^ r = (1 / 3) ^ (r - r' - 1) * (1 / 3) ^ r' * (1 / 3) := by
      rw [← pow_add, ← pow_succ]; congr 1; omega
    rw [e]
    have : (1 / 3 : ℚ) ^ (r - r' - 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have : (0 : ℚ) ≤ (1 / 3) ^ r' := by positivity
    nlinarith
  unfold pot
  have h3 : (0 : ℚ) ≤ 3 ^ R := by positivity
  nlinarith

/-- **absorption**: on a ranked game with ranks `≤ R`, for ALL strategies,
`P(no terminal within T steps) · (T+1) ≤ 2 · pot(rank u)`. -/
theorem unabs_decay (G : Game n) (r : Fin n → ℕ) (hr : Ranked G r) (R : ℕ) (hR : ∀ i, r i ≤ R) (σ τ : HStrategy n) :
    ∀ T h u, ((unabs G σ τ T h u : ℤ) : ℚ) * ((T : ℚ) + 1) ≤ 2 * pot R (r u) * 2 ^ T := by
  intro T
  induction T with
  | zero =>
    intro h u
    obtain ⟨p0, _, _⟩ := pot_facts R (r u) (hR u)
    simp only [unabs, pow_zero, mul_one, Nat.cast_zero, zero_add]
    split
    · simp; linarith
    · rename_i hs
      -- a non-terminal node has rank ≥ 1
      have hpos : 1 ≤ r u := by
        cases hk : G.nodeType u with
        | average => rcases (hr u).1 hk with h | h <;> omega
        | max => have := (hr u).2 (Or.inl hk); omega
        | min => have := (hr u).2 (Or.inr hk); omega
        | terminal0 => simp [hk] at hs
        | terminal1 => simp [hk] at hs
      have : (1 / 3 : ℚ) ^ r u ≤ 1 / 3 := by
        have := pow_le_pow_of_le_one (show (0:ℚ) ≤ 1/3 by norm_num) (by norm_num) hpos; simpa using this
      have h3 : (1 : ℚ) ≤ 3 ^ R := one_le_pow₀ (by norm_num)
      have hp : 3 ^ R * (2 / 3 : ℚ) ≤ pot R (r u) := by unfold pot; nlinarith
      norm_num; linarith
  | succ T ih =>
    intro h u
    have pp : (0 : ℚ) < 2 ^ T := by positivity
    obtain ⟨p0, p1, pX⟩ := pot_facts R (r u) (hR u)
    have fin : ∀ (Q C : ℚ), Q * ((T : ℚ) + 1) ≤ (2 * C - 1) * (2 * 2 ^ T) → Q ≤ 2 * 2 ^ T →
        Q * (((T + 1 : ℕ) : ℚ) + 1) ≤ 2 * C * 2 ^ (T + 1) := by
      intro Q C h1 h2
      push_cast; rw [pow_succ]; nlinarith
    simp only [unabs, chosen_eq_child, ← child_false, ← child_true]
    cases hk : G.nodeType u with
    | terminal1 => simp; positivity
    | terminal0 => simp; positivity
    | max =>
      have hl := (hr u).2 (Or.inl hk)
      set c := G.child u (σ (u :: h)).toBool
      have hc : r c < r u := by simp only [c]; cases σ (u :: h); exact hl.1; exact hl.2
      have i := ih (u :: h) c
      have rg := unabs_range G σ τ T (u :: h) c
      have st := pot_step R (r u) (r c) (hR u) hc
      have : 2 * pot R (r c) * 2 ^ T ≤ 2 * (pot R (r u) - 2) * 2 ^ T := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt pp); linarith
      apply fin
      · push_cast; nlinarith
      · have : ((unabs G σ τ T (u :: h) c : ℤ) : ℚ) ≤ 2 ^ T := by exact_mod_cast rg.2
        push_cast; linarith
    | min =>
      have hl := (hr u).2 (Or.inr hk)
      set c := G.child u (τ (u :: h)).toBool
      have hc : r c < r u := by simp only [c]; cases τ (u :: h); exact hl.1; exact hl.2
      have i := ih (u :: h) c
      have rg := unabs_range G σ τ T (u :: h) c
      have st := pot_step R (r u) (r c) (hR u) hc
      have : 2 * pot R (r c) * 2 ^ T ≤ 2 * (pot R (r u) - 2) * 2 ^ T := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt pp); linarith
      apply fin
      · push_cast; nlinarith
      · have : ((unabs G σ τ T (u :: h) c : ℤ) : ℚ) ≤ 2 ^ T := by exact_mod_cast rg.2
        push_cast; linarith
    | average =>
      have ia := ih (u :: h) (G.child u false); have ib := ih (u :: h) (G.child u true)
      have ra := unabs_range G σ τ T (u :: h) (G.child u false)
      have rb := unabs_range G σ τ T (u :: h) (G.child u true)
      have ra' : ((unabs G σ τ T (u :: h) (G.child u false) : ℤ) : ℚ) ≤ 2 ^ T := by exact_mod_cast ra.2
      have rb' : ((unabs G σ τ T (u :: h) (G.child u true) : ℤ) : ℚ) ≤ 2 ^ T := by exact_mod_cast rb.2
      obtain ⟨_, qa, _⟩ := pot_facts R (r (G.child u false)) (hR _)
      obtain ⟨_, qb, _⟩ := pot_facts R (r (G.child u true)) (hR _)
      have hsum : pot R (r (G.child u false)) + pot R (r (G.child u true)) ≤ 2 * pot R (r u) - 1 := by
        unfold pot at *
        rcases (hr u).1 hk with hc | hc
        · have := pot_step R (r u) _ (hR u) hc; unfold pot at this; nlinarith
        · have := pot_step R (r u) _ (hR u) hc; unfold pot at this; nlinarith
      have : (2 * pot R (r (G.child u false)) + 2 * pot R (r (G.child u true))) * 2 ^ T ≤
          (2 * (2 * pot R (r u) - 1)) * 2 ^ T := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt pp); linarith
      apply fin
      · push_cast; nlinarith
      · push_cast; linarith

/-! ## Stopping ↔ peeling -/

theorem peel_stable (G : Game n) : ∀ k, (∃ j < k, peel G j = peel G (j + 1)) ∨
    k ≤ (Finset.univ.filter (fun i => peel G k i = true)).card := by
  intro k
  induction k with
  | zero => right; simp
  | succ k ih =>
    rcases ih with ⟨j, hj, e⟩ | ih
    · left; exact ⟨j, by omega, e⟩
    · by_cases e : peel G k = peel G (k + 1)
      · left; exact ⟨k, by omega, e⟩
      · right
        have : (Finset.univ.filter (fun i => peel G k i = true)).card <
            (Finset.univ.filter (fun i => peel G (k + 1) i = true)).card := by
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff_of_subset]
          · obtain ⟨i, hi⟩ : ∃ i, peel G k i ≠ peel G (k + 1) i := by
              by_contra c; push Not at c; exact e (funext c)
            refine ⟨i, ?_, ?_⟩
            · have : peel G (k + 1) i = true := by
                cases h1 : peel G (k + 1) i
                · cases h0 : peel G k i
                  · rw [h0, h1] at hi; exact absurd rfl hi
                  · have := peel_succ_of G k i h0; rw [h1] at this; cases this
                · rfl
              simp [this]
            · have : peel G k i = false := by
                cases h0 : peel G k i
                · rfl
                · have := peel_succ_of G k i h0; rw [h0, this] at hi; exact absurd rfl hi
              simp [this]
          · intro i hi; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
            exact peel_succ_of G k i hi
        omega

theorem peel_stab_n (G : Game n) : peel G (n + 1) = peel G n := by
  obtain ⟨j, hj, e⟩ : ∃ j < n + 1, peel G j = peel G (j + 1) := by
    rcases peel_stable G (n + 1) with h | h
    · exact h
    · have := Finset.card_le_univ (Finset.univ.filter (fun i => peel G (n + 1) i = true))
      simp at this; omega
  have : ∀ m, j ≤ m → peel G m = peel G j := by
    intro m hm
    induction m with
    | zero => have : j = 0 := by omega
              subst this; rfl
    | succ m ih =>
      rcases Nat.lt_or_ge j (m + 1) with h | h
      · show peelStep G (peel G m) = peel G j
        rw [ih (by omega)]
        exact e.symm
      · have : j = m + 1 := by omega
        subst this; rfl
  rw [this (n + 1) (by omega), this n (by omega)]

/-- the trap strategy: stay among the nodes peeling never removes. -/
def trapS (G : Game n) : HStrategy n
  | [] => .j
  | u :: _ => ArcChoice.ofBool (decide (peel G n (G.child u true) = false))

theorem trap_closed (G : Game n) : ∀ u, peel G n u = false →
    (G.nodeType u ≠ .terminal0 ∧ G.nodeType u ≠ .terminal1) ∧
    (G.nodeType u = .average → peel G n (G.child u false) = false ∧ peel G n (G.child u true) = false) ∧
    (G.nodeType u = .max ∨ G.nodeType u = .min → peel G n (G.child u (trapS G (u :: [])).toBool) = false) := by
  have stab := congrFun (peel_stab_n G)
  intro u hu
  have h1 := stab u
  rw [hu] at h1
  change peelStep G (peel G n) u = false at h1
  simp only [peelStep, hu, Bool.false_or] at h1
  refine ⟨⟨fun hk => ?_, fun hk => ?_⟩, fun hk => ?_, fun hk => ?_⟩
  · rw [hk] at h1; cases h1
  · rw [hk] at h1; cases h1
  · rw [hk] at h1; simp only [Bool.or_eq_false_iff] at h1; exact h1
  · simp only [trapS]
    rcases hk with hk | hk <;> rw [hk] at h1 <;> simp only [Bool.and_eq_false_iff] at h1 <;>
      by_cases c : peel G n (G.child u true) = false <;> simp [c] <;> rcases h1 with h1 | h1 <;>
      first | exact h1 | exact absurd h1 c

theorem trap_unabs (G : Game n) : ∀ T h u, peel G n u = false → unabs G (trapS G) (trapS G) T h u = 2 ^ T := by
  have closed := trap_closed G
  have tr : ∀ u h, trapS G (u :: h) = trapS G (u :: []) := fun _ _ => rfl
  intro T
  induction T with
  | zero => intro h u hu; obtain ⟨⟨a, b⟩, _⟩ := closed u hu; simp [unabs, a, b]
  | succ T ih =>
    intro h u hu
    obtain ⟨_, hc, hp⟩ := closed u hu
    simp only [unabs, chosen_eq_child, ← child_false, ← child_true]
    cases hk : G.nodeType u with
    | terminal0 => exact absurd hk (closed u hu).1.1
    | terminal1 => exact absurd hk (closed u hu).1.2
    | average => rw [ih _ _ (hc hk).1, ih _ _ (hc hk).2, pow_succ]; ring
    | max => rw [tr, ih _ _ (hp (Or.inl hk)), pow_succ]; ring
    | min => rw [tr, ih _ _ (hp (Or.inr hk)), pow_succ]; ring

theorem stoppingByPlay_peelAll (G : Game n) (hs : StoppingByPlay G) : ∀ i, peel G n i = true := by
  intro i
  by_contra hc
  have hu : peel G n i = false := by simpa using hc
  obtain ⟨T, hT⟩ := hs (trapS G) (trapS G) i 0
  rw [trap_unabs G T [] i hu] at hT
  simp at hT

theorem peelAll_stoppingByPlay (G : Game n) (hall : ∀ i, peel G n i = true) : StoppingByPlay G := by
  have hr := prank_ranked G hall
  have hR : ∀ i, prank G i ≤ n := fun i => le_of_lt (prank_facts G hall i).1
  intro σ τ u k
  refine ⟨2 ^ (k + 1) * 3 ^ n, ?_⟩
  set T := 2 ^ (k + 1) * 3 ^ n with hT
  have d := unabs_decay G (prank G) hr n hR σ τ T [] u
  obtain ⟨_, p1, _⟩ := pot_facts n (prank G u) (hR u)
  have rg := unabs_range G σ τ T [] u
  have pp : (0 : ℚ) < 2 ^ T := by positivity
  have U0 : (0 : ℚ) ≤ ((unabs G σ τ T [] u : ℤ) : ℚ) := by exact_mod_cast rg.1
  have hTq : (T : ℚ) = 2 ^ (k + 1) * 3 ^ n := by rw [hT]; push_cast; ring
  have pk : (0 : ℚ) < 2 ^ k := by positivity
  -- 2^k U (T+1) ≤ 2^k · 2 · 3^n · 2^T = T 2^T < (T+1) 2^T
  have : (2 : ℚ) ^ k * ((unabs G σ τ T [] u : ℤ) : ℚ) * ((T : ℚ) + 1) < 2 ^ T * ((T : ℚ) + 1) := by
    have h1 : (2 : ℚ) ^ k * (((unabs G σ τ T [] u : ℤ) : ℚ) * ((T : ℚ) + 1)) ≤ 2 ^ k * (2 * pot n (prank G u) * 2 ^ T) :=
      mul_le_mul_of_nonneg_left d (le_of_lt pk)
    have h2 : (2 : ℚ) ^ k * (2 * pot n (prank G u) * 2 ^ T) ≤ 2 ^ k * (2 * (3 ^ n - 1) * 2 ^ T) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt pk)
      apply mul_le_mul_of_nonneg_right _ (le_of_lt pp); linarith
    have h3 : (2 : ℚ) ^ k * (2 * (3 ^ n - 1) * 2 ^ T) < 2 ^ T * ((T : ℚ) + 1) := by
      rw [hTq, pow_succ]; nlinarith
    calc (2 : ℚ) ^ k * ((unabs G σ τ T [] u : ℤ) : ℚ) * ((T : ℚ) + 1)
        = (2 : ℚ) ^ k * (((unabs G σ τ T [] u : ℤ) : ℚ) * ((T : ℚ) + 1)) := by ring
      _ < _ := lt_of_le_of_lt (le_trans h1 h2) h3
  have hlt : (2 : ℚ) ^ k * ((unabs G σ τ T [] u : ℤ) : ℚ) < 2 ^ T :=
    lt_of_mul_lt_mul_right this (by positivity)
  exact_mod_cast hlt

/-- **the peeling test decides Condon's stopping condition.** -/
theorem stoppingByPlay_iff_peelAll (G : Game n) : StoppingByPlay G ↔ peelAll G = true := by
  rw [peelAll_iff]; exact ⟨stoppingByPlay_peelAll G, peelAll_stoppingByPlay G⟩

/-! ## the value defined by play -/

theorem exists_pow_lt (ε : ℚ) (hε : 0 < ε) : ∃ k : ℕ, 1 / (2 : ℚ) ^ k < ε := by
  refine ⟨⌈1 / ε⌉₊, ?_⟩
  have h1 : 1 / ε ≤ (⌈1 / ε⌉₊ : ℚ) := Nat.le_ceil _
  have h2 : ((⌈1 / ε⌉₊ : ℕ) : ℚ) < 2 ^ ⌈1 / ε⌉₊ := by exact_mod_cast Nat.lt_two_pow_self
  rw [div_lt_iff₀ (by positivity)]
  rw [div_le_iff₀ hε] at h1
  nlinarith

/-- **`c` is the value of the game at node `u`, by play**: the max player has a strategy that, for every `k`, from
some horizon on guarantees arrival at terminal-1 with probability `≥ c - 2^-k` against all (history-dependent)
strategies of the min player; the min player has a strategy keeping the probability of arrival within `T` steps at
most `c` for every `T` against all strategies of the max player. -/
def IsValueAt (G : Game n) (u : Fin n) (c : ℚ) : Prop :=
  (∃ σ : HStrategy n, ∀ k : ℕ, ∃ T0 : ℕ, ∀ T, T0 ≤ T → ∀ τ : HStrategy n,
      (c - 1 / 2 ^ k) * 2 ^ T ≤ ((win1 G σ τ T [] u : ℤ) : ℚ)) ∧
  (∃ τ : HStrategy n, ∀ (σ : HStrategy n) (T : ℕ), ((win1 G σ τ T [] u : ℤ) : ℚ) ≤ c * 2 ^ T)

/-- the value by play is unique. -/
theorem isValueAt_unique (G : Game n) (u : Fin n) (c c' : ℚ) (h : IsValueAt G u c) (h' : IsValueAt G u c') :
    c = c' := by
  have one : ∀ a b : ℚ, IsValueAt G u a → IsValueAt G u b → a ≤ b := by
    intro a b ha hb
    by_contra hlt; push Not at hlt
    obtain ⟨σ, hσ⟩ := ha.1
    obtain ⟨τ, hτ⟩ := hb.2
    obtain ⟨k, hk⟩ := exists_pow_lt (a - b) (by linarith)
    obtain ⟨T0, hT0⟩ := hσ k
    have l := hT0 T0 le_rfl τ
    have r := hτ σ T0
    have pp : (0 : ℚ) < 2 ^ T0 := by positivity
    have : (a - 1 / 2 ^ k) * 2 ^ T0 ≤ b * 2 ^ T0 := le_trans l r
    have := le_of_mul_le_mul_right this pp
    linarith
  exact le_antisymm (one c c' h h') (one c' c h' h)

/-- the greedy max strategy guarantees `v_u - 2^-k` from the horizon `2^(k+1)·3^n` on, uniformly against all
history-dependent min strategies. -/
theorem optMax_guarantee (G : Game n) (hall : ∀ i, peel G n i = true) (v : Fin n → ℚ) (hv : F G v = v) (u : Fin n)
    (k : ℕ) (T : ℕ) (hT : 2 ^ (k + 1) * 3 ^ n ≤ T) (τ : HStrategy n) :
    (v u - 1 / 2 ^ k) * 2 ^ T ≤ ((win1 G (optMax G v) τ T [] u : ℤ) : ℚ) := by
  have hr := prank_ranked G hall
  have hR : ∀ i, prank G i ≤ n := fun i => le_of_lt (prank_facts G hall i).1
  have lo := win_lower G (prank G) hr v hv τ T [] u
  have d := unabs_decay G (prank G) hr n hR (optMax G v) τ T [] u
  obtain ⟨_, p1, _⟩ := pot_facts n (prank G u) (hR u)
  have pp : (0 : ℚ) < 2 ^ T := by positivity
  have pk : (0 : ℚ) < 2 ^ k := by positivity
  have hTq : (2 : ℚ) ^ (k + 1) * 3 ^ n ≤ T := by exact_mod_cast hT
  set U := ((unabs G (optMax G v) τ T [] u : ℤ) : ℚ)
  have rg := unabs_range G (optMax G v) τ T [] u
  have U0 : 0 ≤ U := by simp only [U]; exact_mod_cast rg.1
  -- U ≤ 2^T / 2^k
  have hU : U * 2 ^ k ≤ 2 ^ T := by
    have h1 : U * ((T : ℚ) + 1) ≤ 2 * (3 ^ n - 1) * 2 ^ T := by
      have : 2 * pot n (prank G u) * 2 ^ T ≤ 2 * (3 ^ n - 1) * 2 ^ T :=
        mul_le_mul_of_nonneg_right (by linarith) (le_of_lt pp)
      linarith
    have h2 : U * (2 ^ (k + 1) * 3 ^ n) ≤ U * ((T : ℚ) + 1) := mul_le_mul_of_nonneg_left (by linarith) U0
    rw [pow_succ] at h2
    have h3 : (0 : ℚ) < 3 ^ n := by positivity
    nlinarith
  have : (1 / 2 ^ k) * 2 ^ T ≥ U := by
    rw [ge_iff_le, div_mul_eq_mul_div, one_mul, le_div_iff₀ pk]; exact hU
  nlinarith


/-- **the fixed point of `F` is the value of the game by play, at every node**; the greedy
strategies `optMax v`, `optMin v` are optimal (they are the witnesses). -/
theorem fix_isValue (G : Game n) (hs : StoppingByPlay G) (v : Fin n → ℚ) (hv : F G v = v) (u : Fin n) :
    IsValueAt G u (v u) := by
  have hall := (stoppingByPlay_iff_peelAll G).mp hs
  rw [peelAll_iff] at hall
  have hr := prank_ranked G hall
  refine ⟨⟨optMax G v, fun k => ⟨2 ^ (k + 1) * 3 ^ n, fun T hT τ => optMax_guarantee G hall v hv u k T hT τ⟩⟩,
    ⟨optMin G v, fun σ T => ?_⟩⟩
  · exact win_upper G (prank G) hr v hv σ T [] u

/-- **decision form**: for a stopping game, the start value is `> 1/2` (by play) iff `1 < 2 v(start)`. -/
theorem valueGreaterHalfByPlay_iff (G : Game n) (hs : StoppingByPlay G) (v : Fin n → ℚ) (hv : F G v = v) :
    ValueGreaterHalfByPlay G ↔ 1 < 2 * v G.startNode := by
  have hall := (stoppingByPlay_iff_peelAll G).mp hs
  rw [peelAll_iff] at hall
  have hr := prank_ranked G hall
  constructor
  · rintro ⟨σ, T, h⟩
    by_contra hle; push Not at hle
    have up := win_upper G (prank G) hr v hv σ T [] G.startNode
    have := h (optMin G v)
    have pp : (0 : ℚ) < 2 ^ T := by positivity
    have : ((2 : ℤ) ^ T : ℚ) < 2 * ((win1 G σ (optMin G v) T [] G.startNode : ℤ) : ℚ) := by exact_mod_cast this
    push_cast at this
    nlinarith
  · intro hgt
    obtain ⟨⟨σ, hσ⟩, _⟩ := fix_isValue G hs v hv G.startNode
    -- choose k with 2^-k < (2 v - 1)/2
    obtain ⟨k, hk⟩ := exists_pow_lt (v G.startNode - 1 / 2) (by linarith)
    obtain ⟨T0, hT0⟩ := hσ k
    refine ⟨σ, T0, fun τ => ?_⟩
    have l := hT0 T0 le_rfl τ
    have pp : (0 : ℚ) < 2 ^ T0 := by positivity
    have : (2 : ℚ) ^ T0 < 2 * ((win1 G σ τ T0 [] G.startNode : ℤ) : ℚ) := by nlinarith
    exact_mod_cast this

/-! ## the paper's definitions agree with the by-play definitions -/

/-- a strategy given by one chosen arc per node, read as a history-dependent strategy. -/
def posS (σ : Fin n → ArcChoice) : HStrategy n
  | [] => .j
  | u :: _ => σ u

/-! ### INTERNAL helper: integer counts of random-bit sequences (not part of the primary definitions) -/

/-- INTERNAL: number of sequences of `T` fair random bits on which the random walk in `G_{σ,τ}` from `i` arrives at
terminal-1 within `T` steps; `arrive1 = 2^T · arrivalProb` (`arrive1_eq`). -/
def arrive1 (G : Game n) (σ : MaxStrategy n) (τ : MinStrategy n) : Nat → Fin n → Int
  | 0, i => if G.nodeType i = .terminal1 then 1 else 0
  | T + 1, i => match G.nodeType i with
    | .terminal1 => 2 ^ (T + 1)
    | .terminal0 => 0
    | .max => 2 * arrive1 G σ τ T (G.chosen i (σ i))
    | .min => 2 * arrive1 G σ τ T (G.chosen i (τ i))
    | .average => arrive1 G σ τ T (G.childJ i) + arrive1 G σ τ T (G.childK i)

/-- bridge: the integer count is `2^T` times the arrival probability. -/
theorem arrive1_eq (G : Game n) (σ : MaxStrategy n) (τ : MinStrategy n) :
    ∀ T i, (arrive1 G σ τ T i : ℚ) = 2 ^ T * arrivalProb G σ τ T i := by
  intro T
  induction T with
  | zero => intro i; simp only [arrive1, arrivalProb]; split <;> simp
  | succ T ih =>
    intro i
    simp only [arrive1, arrivalProb]
    cases G.nodeType i <;> simp only [Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_ofNat, Int.cast_zero, ih] <;>
      ring

theorem atLeast_iff_arrive1 (G : Game n) (σ : MaxStrategy n) (τ : MinStrategy n) (i : Fin n) (c : ℚ) :
    ArrivesWithProbAtLeast G σ τ i c ↔ ∀ k : ℕ, ∃ T : ℕ, (c - 1 / 2 ^ k) * 2 ^ T ≤ (arrive1 G σ τ T i : ℚ) := by
  have pw : ArrivesWithProbAtLeast G σ τ i c ↔ ∀ k : ℕ, ∃ T : ℕ, c - 1 / 2 ^ k ≤ arrivalProb G σ τ T i := by
    constructor
    · intro h k; exact h _ (by positivity)
    · intro h ε hε
      obtain ⟨k, hk⟩ := exists_pow_lt ε hε
      obtain ⟨T, hT⟩ := h k
      exact ⟨T, by linarith⟩
  rw [pw]
  have h : ∀ (a : ℚ) T, a * 2 ^ T ≤ (arrive1 G σ τ T i : ℚ) ↔ a ≤ arrivalProb G σ τ T i := by
    intro a T; rw [arrive1_eq, mul_comm (2 ^ T : ℚ)]
    exact mul_le_mul_iff_of_pos_right (by positivity)
  simp only [h]

theorem greater_iff_arrive1 (G : Game n) (σ : MaxStrategy n) (τ : MinStrategy n) (i : Fin n) (c : ℚ) :
    ArrivesWithProbGreater G σ τ i c ↔ ∃ T : ℕ, c * 2 ^ T < (arrive1 G σ τ T i : ℚ) := by
  unfold ArrivesWithProbGreater
  have h : ∀ (a : ℚ) T, a * 2 ^ T < (arrive1 G σ τ T i : ℚ) ↔ a < arrivalProb G σ τ T i := by
    intro a T; rw [arrive1_eq, mul_comm (2 ^ T : ℚ)]
    exact mul_lt_mul_iff_of_pos_right (by positivity)
  simp only [h]

theorem arrive1_eq_win1 (G : Game n) (σ : MaxStrategy n) (τ : MinStrategy n) :
    ∀ T h i, arrive1 G σ τ T i = win1 G (posS σ) (posS τ) T h i := by
  intro T
  induction T with
  | zero => intro h i; simp [arrive1, win1]
  | succ T ih =>
    intro h i
    simp only [arrive1, win1, chosen_eq_child, ← child_false, ← child_true]
    cases G.nodeType i <;> simp only [posS, ih (i :: h)]

/-- the greedy max strategy of `v` (one chosen arc per max node). -/
def greedyMax (G : Game n) (v : Fin n → ℚ) : MaxStrategy n :=
  fun i => ArcChoice.ofBool (decide (ev G v (G.child i false) < ev G v (G.child i true)))

/-- the greedy min strategy of `v`. -/
def greedyMin (G : Game n) (v : Fin n → ℚ) : MinStrategy n :=
  fun i => ArcChoice.ofBool (decide (ev G v (G.child i true) < ev G v (G.child i false)))

theorem optMax_eq (G : Game n) (v : Fin n → ℚ) : optMax G v = posS (greedyMax G v) := by
  funext h; cases h <;> rfl

theorem optMin_eq (G : Game n) (v : Fin n → ℚ) : optMin G v = posS (greedyMin G v) := by
  funext h; cases h <;> rfl

theorem reaches_of_ranked (G : Game n) (r : Fin n → ℕ) (hr : Ranked G r) (σ : MaxStrategy n) (τ : MinStrategy n) :
    ∀ i, ReachesTerminal G σ τ i := by
  have key : ∀ k i, r i < k → ReachesTerminal G σ τ i := by
    intro k
    induction k with
    | zero => intro i h; omega
    | succ k ih =>
      intro i hi
      cases hk : G.nodeType i with
      | terminal0 => exact .terminal i (by simp [isTerminal, hk])
      | terminal1 => exact .terminal i (by simp [isTerminal, hk])
      | average =>
        rcases (hr i).1 hk with h | h
        · exact .step i (G.child i false) (by simp only [Arc, hk]; exact Or.inl rfl) (ih _ (by omega))
        · exact .step i (G.child i true) (by simp only [Arc, hk]; exact Or.inr rfl) (ih _ (by omega))
      | max =>
        have h := (hr i).2 (Or.inl hk)
        have : r (G.child i (σ i).toBool) < r i := by cases σ i; exact h.1; exact h.2
        exact .step i (G.child i (σ i).toBool) (by simp only [Arc, hk, chosen_eq_child]) (ih _ (by omega))
      | min =>
        have h := (hr i).2 (Or.inr hk)
        have : r (G.child i (τ i).toBool) < r i := by cases τ i; exact h.1; exact h.2
        exact .step i (G.child i (τ i).toBool) (by simp only [Arc, hk, chosen_eq_child]) (ih _ (by omega))
  exact fun i => key (r i + 1) i (by omega)

theorem stoppingGame_of_peelAll (G : Game n) (hall : ∀ i, peel G n i = true) : StoppingGame G :=
  fun σ τ => reaches_of_ranked G (prank G) (prank_ranked G hall) σ τ

/-- the trap choice as a pair of strategies. -/
def trapP (G : Game n) : Fin n → ArcChoice := fun u => ArcChoice.ofBool (decide (peel G n (G.child u true) = false))

theorem peelAll_of_stoppingGame (G : Game n) (hs : StoppingGame G) : ∀ i, peel G n i = true := by
  intro i0
  by_contra hc
  have hu : peel G n i0 = false := by simpa using hc
  have closed := trap_closed G
  have tr : ∀ u, trapS G (u :: []) = trapP G u := fun _ => rfl
  have key : ∀ i, ReachesTerminal G (trapP G) (trapP G) i → peel G n i = true := by
    intro i h
    induction h with
    | terminal i hi =>
      by_contra c
      have := (closed i (by simpa using c)).1
      unfold isTerminal at hi
      cases hk : G.nodeType i <;> rw [hk] at hi <;> simp at hi
      · exact this.1 hk
      · exact this.2 hk
    | step i j hij _ ih =>
      by_contra c
      have hci : peel G n i = false := by simpa using c
      obtain ⟨_, hav, hpl⟩ := closed i hci
      unfold Arc at hij
      cases hk : G.nodeType i <;> rw [hk] at hij <;> simp only at hij
      · rw [hij, chosen_eq_child] at ih; have := hpl (Or.inl hk); rw [tr] at this; rw [this] at ih; cases ih
      · rw [hij, chosen_eq_child] at ih; have := hpl (Or.inr hk); rw [tr] at this; rw [this] at ih; cases ih
      · rcases hij with e | e <;> rw [e] at ih <;> simp only [← child_false, ← child_true] at ih
        · rw [(hav hk).1] at ih; cases ih
        · rw [(hav hk).2] at ih; cases ih
  rw [key i0 (hs _ _ i0)] at hu; cases hu

/-- **Stopping Game ⇔ peeling succeeds** (computable test). -/
theorem stoppingGame_iff_peelAll (G : Game n) : StoppingGame G ↔ peelAll G = true := by
  rw [peelAll_iff]; exact ⟨peelAll_of_stoppingGame G, stoppingGame_of_peelAll G⟩

/-- **the paper's Stopping Game ⇔ stopping by play** (all history-dependent strategies). -/
theorem stoppingGame_iff_byPlay (G : Game n) : StoppingGame G ↔ StoppingByPlay G := by
  rw [stoppingGame_iff_peelAll, stoppingByPlay_iff_peelAll]

/-- on a Stopping Game there is exactly one stable assignment. -/
theorem stable_exists_unique (G : Game n) (hs : StoppingGame G) :
    ∃ v, Stable G v ∧ ∀ w, Stable G w → w = v := by
  have hall := peelAll_of_stoppingGame G hs
  have hr := prank_ranked G hall
  obtain ⟨v, hv⟩ := fix_exists (nfree G) G (prank G) hr le_rfl
  refine ⟨v, (stable_iff G v).mpr hv, fun w hw => fix_unique G (prank G) hr w v ((stable_iff G w).mp hw) hv⟩

section decision
variable (G : Game n) (hs : StoppingGame G) (v : Fin n → ℚ) (hv : F G v = v)
include hs hv

/-- **the paper's decision problem, by the stable assignment**: `ValueAtLeastHalf G ↔ 1 ≤ 2 v(startNode)`. -/
theorem valueAtLeastHalf_iff : ValueAtLeastHalf G ↔ 1 ≤ 2 * v G.startNode := by
  have hall := peelAll_of_stoppingGame G hs
  have hr := prank_ranked G hall
  constructor
  · rintro ⟨σ, h⟩
    by_contra hlt; push Not at hlt
    obtain ⟨k, hk⟩ := exists_pow_lt (1 / 2 - v G.startNode) (by linarith)
    obtain ⟨T, hT⟩ := (atLeast_iff_arrive1 _ _ _ _ _).mp (h (greedyMin G v)) k
    have up := win_upper G (prank G) hr v hv (posS σ) T [] G.startNode
    rw [optMin_eq, ← arrive1_eq_win1] at up
    have pp : (0 : ℚ) < 2 ^ T := by positivity
    have : (1 / 2 - 1 / 2 ^ k) * 2 ^ T ≤ v G.startNode * 2 ^ T := le_trans hT up
    have := le_of_mul_le_mul_right this pp
    linarith
  · intro h
    refine ⟨greedyMax G v, fun τ => (atLeast_iff_arrive1 _ _ _ _ _).mpr fun k => ⟨2 ^ (k + 1) * 3 ^ n, ?_⟩⟩
    have g := optMax_guarantee G hall v hv G.startNode k _ le_rfl (posS τ)
    rw [optMax_eq, ← arrive1_eq_win1] at g
    have pp : (0 : ℚ) < 2 ^ (2 ^ (k + 1) * 3 ^ n) := by positivity
    have : (1 / 2 - 1 / 2 ^ k) * 2 ^ (2 ^ (k + 1) * 3 ^ n) ≤ (v G.startNode - 1 / 2 ^ k) * 2 ^ (2 ^ (k + 1) * 3 ^ n) :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt pp)
    exact le_trans this g

/-- the strict variant: `ValueGreaterHalf G ↔ 1 < 2 v(startNode)`. -/
theorem valueGreaterHalf_iff : ValueGreaterHalf G ↔ 1 < 2 * v G.startNode := by
  have hall := peelAll_of_stoppingGame G hs
  have hr := prank_ranked G hall
  constructor
  · rintro ⟨σ, h⟩
    by_contra hle; push Not at hle
    obtain ⟨T, hT⟩ := (greater_iff_arrive1 _ _ _ _ _).mp (h (greedyMin G v))
    have up := win_upper G (prank G) hr v hv (posS σ) T [] G.startNode
    rw [optMin_eq, ← arrive1_eq_win1] at up
    have pp : (0 : ℚ) < 2 ^ T := by positivity
    nlinarith
  · intro h
    obtain ⟨k, hk⟩ := exists_pow_lt (v G.startNode - 1 / 2) (by linarith)
    refine ⟨greedyMax G v, fun τ => (greater_iff_arrive1 _ _ _ _ _).mpr ⟨2 ^ (k + 1) * 3 ^ n, ?_⟩⟩
    have g := optMax_guarantee G hall v hv G.startNode k _ le_rfl (posS τ)
    rw [optMax_eq, ← arrive1_eq_win1] at g
    have pp : (0 : ℚ) < 2 ^ (2 ^ (k + 1) * 3 ^ n) := by positivity
    have : 1 / 2 * 2 ^ (2 ^ (k + 1) * 3 ^ n) < (v G.startNode - 1 / 2 ^ k) * 2 ^ (2 ^ (k + 1) * 3 ^ n) :=
      mul_lt_mul_of_pos_right (by linarith) pp
    exact lt_of_lt_of_le this g

/-- the by-play decision problem: `ValueAtLeastHalfByPlay G ↔ 1 ≤ 2 v(startNode)`. -/
theorem valueAtLeastHalfByPlay_iff : ValueAtLeastHalfByPlay G ↔ 1 ≤ 2 * v G.startNode := by
  have hall := peelAll_of_stoppingGame G hs
  have hr := prank_ranked G hall
  constructor
  · rintro ⟨σ, h⟩
    by_contra hlt; push Not at hlt
    obtain ⟨k, hk⟩ := exists_pow_lt (1 / 2 - v G.startNode) (by linarith)
    obtain ⟨T, hT⟩ := h (optMin G v) k
    have up := win_upper G (prank G) hr v hv σ T [] G.startNode
    have pp : (0 : ℚ) < 2 ^ T := by positivity
    have : (1 / 2 - 1 / 2 ^ k) * 2 ^ T ≤ v G.startNode * 2 ^ T := le_trans hT up
    have := le_of_mul_le_mul_right this pp
    linarith
  · intro h
    refine ⟨optMax G v, fun τ k => ⟨2 ^ (k + 1) * 3 ^ n, ?_⟩⟩
    have g := optMax_guarantee G hall v hv G.startNode k _ le_rfl τ
    have pp : (0 : ℚ) < 2 ^ (2 ^ (k + 1) * 3 ^ n) := by positivity
    have : (1 / 2 - 1 / 2 ^ k) * 2 ^ (2 ^ (k + 1) * 3 ^ n) ≤ (v G.startNode - 1 / 2 ^ k) * 2 ^ (2 ^ (k + 1) * 3 ^ n) :=
      mul_le_mul_of_nonneg_right (by linarith) (le_of_lt pp)
    exact le_trans this g
end decision

/-- **the paper's decision problem equals its history-dependent version** on Stopping Games. -/
theorem valueAtLeastHalf_iff_byPlay (G : Game n) (hs : StoppingGame G) :
    ValueAtLeastHalf G ↔ ValueAtLeastHalfByPlay G := by
  obtain ⟨v, hv, _⟩ := stable_exists_unique G hs
  rw [stable_iff] at hv
  rw [valueAtLeastHalf_iff G hs v hv, valueAtLeastHalfByPlay_iff G hs v hv]

/-- the strict variant equals its history-dependent version on Stopping Games. -/
theorem valueGreaterHalf_iff_byPlay (G : Game n) (hs : StoppingGame G) :
    ValueGreaterHalf G ↔ ValueGreaterHalfByPlay G := by
  obtain ⟨v, hv, _⟩ := stable_exists_unique G hs
  rw [stable_iff] at hv
  rw [valueGreaterHalf_iff G hs v hv, valueGreaterHalfByPlay_iff G ((stoppingGame_iff_byPlay G).mp hs) v hv]

end SSG
