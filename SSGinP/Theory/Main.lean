module

public import SSGinP.Theory.Play
public import SSGinP.Theory.Interface

@[expose] public section

/-!
# SSGinP.Theory.Main: simple stochastic games from any price search (paper's Theorem 2)

Parameters for a game on `n` nodes: `γ = 1/(4·3^n)` (`gam`), `ε = 1/(4·3^n)` (`eps`), `δ = γε/16 = 1/(256·9^n)`
(`dlt`), demand bound `R = 1024·9^n` (`Rb`), weights `w_i = 2 - 3^-(prank i)` (`wt`, from peeling).

* `point`, `oracle`     : a price vector `p` is answered at the point `x_i = δ w_i p_i` with the labels
                          `z_i = [x_i ≤ F(x)_i]` (one exact evaluation of `F`).
* THEOREM L `label_consistent` : the hypothesis `hypV` (all `2n` slots, demands `a_{i,h} = ⌊(h v_i/w_i - ε/2)/δ⌋`)
                          is consistent with every answer of this oracle; `search_close`: hence the output `x` of ANY
                          `PriceSearch n (Rb n)` run against the oracle has `|δ w_i x_i - v_i| < w_i (ε/2 + δ)`.
* THEOREM E `greedy_exact` : from any `x̂` with `|x̂_i - v_i| < 1/(2·3^n)`, the greedy choice is
                          value-greedy, `v` is the unique solution of its chain system, and Gauss–Jordan returns `v`.
* MAIN `solveSSG_correct` : `solveSSG P G = some v` with `F v = v` and `v_u` the value of the game by play at every
                          `u` (`IsValueAt`); `decideSSG_correct` : `decideSSG P G = true ↔ StoppingGame G ∧ ValueAtLeastHalf G`
                          (the paper's problem), `decideSSGStrict_correct` (> 1/2), `decideProblem_correct`
                          (`↔ SSGDecision G`, including well-formedness).
* COSTS `cost_queries`, `cost_bits`, `chain_entries` : at most `P.Q` evaluations of `F` during the search (plus one
                          for the final check), every point passed to `F` during the search has numerators and
                          denominators `≤ 2^(B + 5n + 8)`, and the linear system has entries in `{0, ±1/2, ±1}`.
-/

namespace SSG

open SSG28

variable {n : ℕ}

/-! ## parameters -/

def eps (n : ℕ) : ℚ := 1 / (4 * 3 ^ n)
def dlt (n : ℕ) : ℚ := 1 / (256 * 9 ^ n)
def Rb (n : ℕ) : ℕ := 1024 * 9 ^ n

theorem nine_pow (n : ℕ) : (9 : ℚ) ^ n = 3 ^ n * 3 ^ n := by
  rw [← mul_pow]; norm_num

theorem dlt_eq (n : ℕ) : 16 * dlt n = gam n * eps n := by
  unfold dlt gam eps; rw [nine_pow]; field_simp; ring

theorem dlt_pos (n : ℕ) : 0 < dlt n := by unfold dlt; positivity
theorem eps_pos (n : ℕ) : 0 < eps n := by unfold eps; positivity
theorem gam_pos (n : ℕ) : 0 < gam n := by unfold gam; positivity

theorem gam_le (n : ℕ) : gam n ≤ 1 / 4 := by
  unfold gam; rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have : (1 : ℚ) ≤ 3 ^ n := one_le_pow₀ (by norm_num); linarith

/-! ## the oracle -/

/-- the point queried for the price vector `p`. -/
def point (G : Game n) (p : Fin n → ℚ) : Fin n → ℚ := fun i => dlt n * wt G i * p i

/-- the label oracle: `z_i = [x_i ≤ F(x)_i]` at `x = point p`. -/
def oracle (G : Game n) (p : Fin n → ℚ) : Fin n → Bool := fun i => decide (point G p i ≤ F G (point G p) i)

/-- demands of the value hypothesis. -/
def dem (G : Game n) (v : Fin n → ℚ) (s : Slot n) : ℤ := ⌊(sideVal s.2 * v s.1 / wt G s.1 - eps n / 2) / dlt n⌋

theorem sideVal_sq (h : Bool) : sideVal h * sideVal h = 1 := by cases h <;> simp [sideVal]
theorem sideVal_abs (h : Bool) : sideVal h = 1 ∨ sideVal h = -1 := by cases h <;> simp [sideVal]

theorem dem_bound (G : Game n) (v : Fin n → ℚ) (hb : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (s : Slot n) :
    -(Rb n : ℤ) ≤ dem G v s ∧ dem G v s ≤ Rb n := by
  have hw := wt_bounds G s.1
  have hv := hb s.1
  have hd := dlt_pos n
  set q := (sideVal s.2 * v s.1 / wt G s.1 - eps n / 2) / dlt n with hq
  have habs : |sideVal s.2 * v s.1 / wt G s.1| ≤ 1 := by
    rw [abs_div, abs_mul]
    have : |sideVal s.2| = 1 := by rcases sideVal_abs s.2 with e | e <;> rw [e] <;> simp
    rw [this, one_mul, abs_of_nonneg hv.1, abs_of_pos (by linarith), div_le_one (by linarith)]; linarith
  have he : eps n / 2 ≤ 1 / 8 := by
    unfold eps; rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (1 : ℚ) ≤ 3 ^ n := one_le_pow₀ (by norm_num); linarith
  have he0 := eps_pos n
  have hR : (Rb n : ℚ) = 1024 * 9 ^ n := by unfold Rb; push_cast; ring
  have hdR : dlt n * (Rb n : ℚ) = 4 := by rw [hR]; unfold dlt; field_simp; ring
  rw [abs_le] at habs
  have hd1 : dlt n ≤ 1 := by
    unfold dlt; rw [div_le_one (by positivity)]
    have : (1 : ℚ) ≤ 9 ^ n := one_le_pow₀ (by norm_num); linarith
  have q_lo : -(Rb n : ℚ) + 1 ≤ q := by
    rw [hq, le_div_iff₀ hd]
    have ex : (-(Rb n : ℚ) + 1) * dlt n = -(dlt n * Rb n) + dlt n := by ring
    rw [ex, hdR]
    have : dlt n ≤ 1 / 256 := by
      unfold dlt; rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (1 : ℚ) ≤ 9 ^ n := one_le_pow₀ (by norm_num); linarith
    linarith
  have q_hi : q ≤ (Rb n : ℚ) := by
    rw [hq, div_le_iff₀ hd]
    have ex : (Rb n : ℚ) * dlt n = dlt n * Rb n := by ring
    rw [ex, hdR]; linarith
  have f1 := Int.floor_le q
  have f2 := Int.lt_floor_add_one q
  unfold dem; rw [← hq]
  constructor
  · have : (-(Rb n : ℤ) : ℚ) < (⌊q⌋ : ℚ) + 1 := by push_cast; linarith
    have := (Int.cast_lt (R := ℚ)).mp (by push_cast at this ⊢; linarith : ((-(Rb n : ℤ) - 1 : ℤ) : ℚ) < (⌊q⌋ : ℚ))
    omega
  · have : (⌊q⌋ : ℚ) ≤ ((Rb n : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this

/-- the value hypothesis (all `2n` slots). -/
def hypV (G : Game n) (hn : 0 < n) (v : Fin n → ℚ) (hb : ∀ i, 0 ≤ v i ∧ v i ≤ 1) : Hyp n (Rb n) where
  S := Finset.univ
  nonempty := ⟨(⟨0, hn⟩, true), Finset.mem_univ _⟩
  a := dem G v
  bound := fun s _ => dem_bound G v hb s

/-- the surplus of a slot in weighted error units. -/
theorem slot_bounds (G : Game n) (hn : 0 < n) (v : Fin n → ℚ) (hb : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (p : Fin n → ℚ)
    (s : Slot n) :
    dlt n * (hypV G hn v hb).surplus p s ≤ sideVal s.2 * (v s.1 - point G p s.1) / wt G s.1 - eps n / 2 ∧
    sideVal s.2 * (v s.1 - point G p s.1) / wt G s.1 - eps n / 2 - dlt n < dlt n * (hypV G hn v hb).surplus p s := by
  have hd := dlt_pos n
  have hw := wt_bounds G s.1
  set q := (sideVal s.2 * v s.1 / wt G s.1 - eps n / 2) / dlt n with hq
  have f1 := Int.floor_le q
  have f2 := Int.lt_floor_add_one q
  have e1 : dlt n * q = sideVal s.2 * v s.1 / wt G s.1 - eps n / 2 := by rw [hq]; field_simp
  have hw0 : wt G s.1 ≠ 0 := ne_of_gt (by linarith)
  have e2 : sideVal s.2 * (v s.1 - point G p s.1) / wt G s.1 =
      sideVal s.2 * v s.1 / wt G s.1 - dlt n * (sideVal s.2 * p s.1) := by
    unfold point; field_simp
  have hs : (hypV G hn v hb).surplus p s = (⌊q⌋ : ℚ) - sideVal s.2 * p s.1 := by
    simp [Hyp.surplus, hypV, dem, hq]
  rw [hs, e2]
  constructor
  · have : dlt n * (⌊q⌋ : ℚ) ≤ dlt n * q := mul_le_mul_of_nonneg_left f1 (le_of_lt hd)
    nlinarith
  · have : dlt n * q < dlt n * ((⌊q⌋ : ℚ) + 1) := mul_lt_mul_of_pos_left f2 hd
    nlinarith

/-- **THEOREM L (label consistency)**: on a stopping game (peeling succeeds) with fixed point `v`, the hypothesis
`hypV` is consistent with every answer of the oracle. -/
theorem label_consistent (G : Game n) (hall : ∀ i, peel G n i = true) (hn : 0 < n) (v : Fin n → ℚ)
    (hv : F G v = v) (hb : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (p : Fin n → ℚ) :
    (hypV G hn v hb).ConsistentAt p (oracle G p) := by
  intro s _ hmax h0
  have hd := dlt_pos n
  have heps := eps_pos n
  have hγ := gam_pos n
  have hγ4 := gam_le n
  have hde := dlt_eq n
  set y := point G p with hy
  set U := sideVal s.2 * (v s.1 - y s.1) / wt G s.1 with hU
  have bs := slot_bounds G hn v hb p s
  have hUe : eps n / 2 ≤ U := by
    have : 0 ≤ dlt n * (hypV G hn v hb).surplus p s := mul_nonneg (le_of_lt hd) h0
    rw [← hy] at bs; linarith [bs.1]
  -- every weighted error is at most `U + δ`
  have herr : ∀ j, |y j - v j| ≤ (U + dlt n) * wt G j := by
    intro j
    have hw := wt_bounds G j
    have one : ∀ h' : Bool, sideVal h' * (v j - y j) / wt G j ≤ U + dlt n := by
      intro h'
      have b := slot_bounds G hn v hb p (j, h')
      have m := hmax (j, h') (Finset.mem_univ _)
      have : dlt n * (hypV G hn v hb).surplus p (j, h') ≤ dlt n * (hypV G hn v hb).surplus p s :=
        mul_le_mul_of_nonneg_left m (le_of_lt hd)
      rw [← hy] at b bs; simp only at b
      linarith [bs.1]
    have a := one true; have b := one false
    simp only [sideVal, if_true, one_mul] at a
    simp only [sideVal, Bool.false_eq_true, if_false] at b
    rw [div_le_iff₀ (by linarith)] at a b
    rw [abs_le]; constructor <;> linarith
  have hM : 0 ≤ U + dlt n := by linarith
  have hc := contraction G hall y v (U + dlt n) hM herr s.1
  rw [hv] at hc
  have hw := wt_bounds G s.1
  -- `h (F(y)_i - y_i) ≥ w_i (γ U - (1-γ) δ) > 0`
  have hmove : 0 < sideVal s.2 * (F G y s.1 - y s.1) := by
    have hw0 : wt G s.1 ≠ 0 := ne_of_gt (by linarith)
    have hUw : sideVal s.2 * (v s.1 - y s.1) = U * wt G s.1 := by rw [hU]; field_simp
    have habs : sideVal s.2 * (F G y s.1 - v s.1) ≥ -((1 - gam n) * (U + dlt n) * wt G s.1) := by
      rw [abs_le] at hc
      rcases sideVal_abs s.2 with e | e <;> rw [e] <;> linarith [hc.1, hc.2]
    have e : sideVal s.2 * (F G y s.1 - y s.1) = sideVal s.2 * (F G y s.1 - v s.1) + sideVal s.2 * (v s.1 - y s.1) := by
      ring
    rw [e, hUw]
    have : 0 < (gam n * U - (1 - gam n) * dlt n) * wt G s.1 := by
      apply mul_pos _ (by linarith)
      nlinarith
    nlinarith
  show oracle G p s.1 = s.2
  unfold oracle; rw [← hy]
  cases hs2 : s.2
  · rw [hs2] at hmove; simp [sideVal] at hmove
    simp; linarith
  · rw [hs2] at hmove; simp [sideVal] at hmove
    simp; linarith

/-- **search output** (consequence of Theorem L): ANY price search for `N = n`, `R = Rb n`, run against the oracle,
returns prices `x` with `|δ w_i x_i - v_i| < w_i (ε/2 + δ)`. -/
theorem search_close (G : Game n) (hall : ∀ i, peel G n i = true) (hn : 0 < n) (v : Fin n → ℚ) (hv : F G v = v)
    (P : PriceSearch n (Rb n)) (x : Fin n → ℚ) (T : Transcript n) (hrun : run P.strat (oracle G) P.Q [] = some (x, T)) :
    ∀ i, |point G x i - v i| < wt G i * (eps n / 2 + dlt n) := by
  have hr := prank_ranked G hall
  have hb := fix_bounds G (prank G) hr v hv
  have hcons : (hypV G hn v hb).Consistent T := by
    intro q hq
    have := run_answers P.strat (oracle G) P.Q [] x T hrun (by simp) q hq
    rw [this]; exact label_consistent G hall hn v hv hb q.1
  have hmeet := P.correct (oracle G) x T hrun (hypV G hn v hb) hcons
  intro i
  have hd := dlt_pos n
  have hw := wt_bounds G i
  have one : ∀ h : Bool, sideVal h * (v i - point G x i) < wt G i * (eps n / 2 + dlt n) := by
    intro h
    have m := hmeet (i, h) (Finset.mem_univ _)
    simp only [hypV, dem] at m
    set q := (sideVal h * v i / wt G i - eps n / 2) / dlt n with hq
    have f2 := Int.lt_floor_add_one q
    have e1 : dlt n * q = sideVal h * v i / wt G i - eps n / 2 := by rw [hq]; field_simp
    have : dlt n * q < dlt n * (sideVal h * x i + 1) := mul_lt_mul_of_pos_left (by linarith) hd
    have hw0 : wt G i ≠ 0 := ne_of_gt (by linarith)
    have e2 : sideVal h * (v i - point G x i) = wt G i * (sideVal h * v i / wt G i - dlt n * (sideVal h * x i)) := by
      unfold point; field_simp
    rw [e2]
    apply mul_lt_mul_of_pos_left _ (by linarith)
    linarith
  have a := one true; have b := one false
  simp only [sideVal, if_true, one_mul, Bool.false_eq_true, if_false] at a b
  rw [abs_lt]; constructor <;> linarith

/-! ## THEOREM E: exact recovery -/

/-- the greedy choice read off from an approximation `x̂`. -/
def choice (G : Game n) (xh : Fin n → ℚ) (i : Fin n) : Bool :=
  match G.nodeType i with
  | .max => decide (xh (G.child i false) < xh (G.child i true))
  | .min => decide (xh (G.child i true) < xh (G.child i false))
  | _ => false

/-- **THEOREM E (exact recovery)**: on a stopping game with fixed point `v`, from ANY `x̂` with
`|x̂_i - v_i| < 1/(2·3^n)` the greedy choice is value-greedy (`Fp (choice x̂) v = v`) and Gauss–Jordan on its chain
system returns exactly `v`. -/
theorem greedy_exact (G : Game n) (hall : ∀ i, peel G n i = true) (v : Fin n → ℚ) (hv : F G v = v)
    (xh : Fin n → ℚ) (hx : ∀ i, |xh i - v i| < 1 / (2 * 3 ^ n)) :
    Fp G (choice G xh) v = v ∧ gj (chainA G (choice G xh)) (chainB G (choice G xh)) = some v := by
  have hr := prank_ranked G hall
  obtain ⟨D, hD0, hD, hz⟩ := denom_bound G (prank G) hr v hv
  have evf := ev_fix G (prank G) hr v hv
  -- separation of distinct values
  have cmpT : ∀ j j', xh j ≤ xh j' → v j ≤ v j' := by
    intro j j' hle
    by_contra hlt; push Not at hlt
    obtain ⟨z, ez⟩ := hz j; obtain ⟨z', ez'⟩ := hz j'
    have hDq : (0 : ℚ) < D := by exact_mod_cast hD0
    have hzz : z' < z := by
      have : (D : ℚ) * v j' < D * v j := mul_lt_mul_of_pos_left hlt hDq
      rw [ez, ez'] at this; exact_mod_cast this
    have hsep : (1 : ℚ) ≤ D * (v j - v j') := by
      have : (1 : ℚ) ≤ (z : ℚ) - z' := by
        have : z' + 1 ≤ z := hzz
        exact_mod_cast (by omega : (1 : ℤ) ≤ z - z')
      rw [mul_sub, ez, ez']; exact this
    have hD3 : (D : ℚ) ≤ 3 ^ n := by exact_mod_cast hD
    have h3 : (0 : ℚ) < 3 ^ n := by positivity
    have hgap : 1 / 3 ^ n ≤ v j - v j' := by
      rw [div_le_iff₀ h3]; nlinarith
    have a := hx j; have b := hx j'
    rw [abs_lt] at a b
    have : 1 / (2 * 3 ^ n) + 1 / (2 * 3 ^ n) = (1 : ℚ) / 3 ^ n := by field_simp; ring
    linarith
  have hfp : Fp G (choice G xh) v = v := by
    funext i
    have hyp := fix_cmp_hyp G v hv i
    have e := congrFun hv i
    unfold Fp; unfold F at e
    cases hk : G.nodeType i with
    | terminal0 => rw [hk] at e; exact e
    | terminal1 => rw [hk] at e; exact e
    | average => rw [hk] at e; exact e
    | max =>
      rw [hk] at e; simp only at e ⊢
      simp only [choice, hk]
      by_cases c : xh (G.child i false) < xh (G.child i true)
      · simp only [c, decide_true]
        have := cmpT _ _ (le_of_lt c); rw [← evf, ← evf] at this
        rw [← e, max_eq_right this]
      · simp only [c, decide_false]
        have := cmpT _ _ (le_of_not_gt c); rw [← evf, ← evf] at this
        rw [← e, max_eq_left this]
    | min =>
      rw [hk] at e; simp only at e ⊢
      simp only [choice, hk]
      by_cases c : xh (G.child i true) < xh (G.child i false)
      · simp only [c, decide_true]
        have := cmpT _ _ (le_of_lt c); rw [← evf, ← evf] at this
        rw [← e, min_eq_right this]
      · simp only [c, decide_false]
        have := cmpT _ _ (le_of_not_gt c); rw [← evf, ← evf] at this
        rw [← e, min_eq_left this]
  refine ⟨hfp, ?_⟩
  obtain ⟨y, hy⟩ := gj_complete (chainA G (choice G xh)) (chainB G (choice G xh)) (chain_inj G (prank G) hr _)
  have := (gj_sound _ _ y hy v).mp ((chain_sol G _ v).mpr hfp)
  rw [hy, this]

/-! ## MAIN: the algorithm -/

/-- **the algorithm**: run the search against the oracle, read the greedy choice off `δ w x`, solve the chain
system, and certify the result by checking `F y = y`. -/
def solveSSG (P : PriceSearch n (Rb n)) (G : Game n) : Option (Fin n → ℚ) :=
  match run P.strat (oracle G) P.Q [] with
  | none => none
  | some (x, _) =>
    match gj (chainA G (choice G (point G x))) (chainB G (choice G (point G x))) with
    | none => none
    | some y => if F G y = y then some y else none

/-- **the decision procedure** for the paper's problem (probability at least 1/2): stopping test by peeling, then
the sign of `2 v(startNode) - 1`. -/
def decideSSG (P : PriceSearch n (Rb n)) (G : Game n) : Bool :=
  peelAll G &&
    (match solveSSG P G with
     | some v => decide (1 ≤ 2 * v G.startNode)
     | none => false)

/-- the decision procedure for the strict variant (probability greater than 1/2). -/
def decideSSGStrict (P : PriceSearch n (Rb n)) (G : Game n) : Bool :=
  peelAll G &&
    (match solveSSG P G with
     | some v => decide (1 < 2 * v G.startNode)
     | none => false)

/-- the full decision procedure including well-formedness (exactly one terminal-0 and one terminal-1 node). -/
def decideProblem (P : PriceSearch n (Rb n)) (G : Game n) : Bool := decide (WellFormed G) && decideSSG P G

def decideProblemStrict (P : PriceSearch n (Rb n)) (G : Game n) : Bool := decide (WellFormed G) && decideSSGStrict P G

/-- soundness of the certificate: whatever the search does, an answer of `solveSSG` is the fixed point. -/
theorem solveSSG_sound (P : PriceSearch n (Rb n)) (G : Game n) (y : Fin n → ℚ) (h : solveSSG P G = some y) :
    F G y = y := by
  unfold solveSSG at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h; assumption
      · cases h

theorem err_small (n : ℕ) : 2 * (eps n / 2 + dlt n) < 1 / (2 * 3 ^ n) := by
  unfold eps dlt; rw [nine_pow]
  have h3 : (1 : ℚ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  generalize (3 : ℚ) ^ n = X at h3 ⊢
  have hX : 0 < X := by linarith
  rw [show 2 * (1 / (4 * X) / 2 + 1 / (256 * (X * X))) = (64 * X + 2) / (256 * (X * X)) by field_simp; ring]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **MAIN THEOREM (game side, conditional on a price search)**: for every Stopping Game `G` on `n` nodes and
every `PriceSearch n (1024·9^n)`, `solveSSG` returns the exact stable assignment `v`, and `v u` is the value of the
game at every node `u` (`IsValueAt`, witnessed by the greedy strategies `optMax v`, `optMin v`). -/
theorem solveSSG_correct (P : PriceSearch n (Rb n)) (G : Game n) (hs : StoppingGame G) :
    ∃ v, solveSSG P G = some v ∧ Stable G v ∧ ∀ u, IsValueAt G u (v u) := by
  have hall := peelAll_of_stoppingGame G hs
  have hn : 0 < n := Fin.pos G.startNode
  have hr := prank_ranked G hall
  obtain ⟨v, hv⟩ := fix_exists (nfree G) G (prank G) hr le_rfl
  refine ⟨v, ?_, (stable_iff G v).mpr hv, fun u => fix_isValue G ((stoppingGame_iff_byPlay G).mp hs) v hv u⟩
  obtain ⟨x, T, hrun⟩ := P.halts (oracle G)
  have hclose := search_close G hall hn v hv P x T hrun
  have hx : ∀ i, |point G x i - v i| < 1 / (2 * 3 ^ n) := by
    intro i
    have hw := wt_bounds G i
    have := hclose i
    have hp : 0 ≤ eps n / 2 + dlt n := by have := eps_pos n; have := dlt_pos n; linarith
    have : wt G i * (eps n / 2 + dlt n) ≤ 2 * (eps n / 2 + dlt n) := mul_le_mul_of_nonneg_right hw.2 hp
    have := err_small n
    linarith
  obtain ⟨_, hgj⟩ := greedy_exact G hall v hv (point G x) hx
  unfold solveSSG
  rw [hrun]; simp only
  rw [hgj]; simp [hv]

theorem peelAll_false (G : Game n) (hs : ¬ StoppingGame G) : peelAll G = false := by
  cases h : peelAll G
  · rfl
  · exact absurd ((stoppingGame_iff_peelAll G).mpr h) hs

/-- **MAIN THEOREM, decision form (the paper's problem)**: `decideSSG P G = true` iff `G` is a Stopping Game and
the max player can guarantee arrival at terminal-1 with probability at least 1/2 from the start node. -/
theorem decideSSG_correct (P : PriceSearch n (Rb n)) (G : Game n) :
    decideSSG P G = true ↔ StoppingGame G ∧ ValueAtLeastHalf G := by
  unfold decideSSG
  by_cases hs : StoppingGame G
  · obtain ⟨v, hsol, hv, _⟩ := solveSSG_correct P G hs
    rw [stable_iff] at hv
    rw [(stoppingGame_iff_peelAll G).mp hs, hsol, valueAtLeastHalf_iff G hs v hv]
    simp [hs]
  · simp [peelAll_false G hs, hs]

/-- **MAIN THEOREM, decision form (strict variant)**. -/
theorem decideSSGStrict_correct (P : PriceSearch n (Rb n)) (G : Game n) :
    decideSSGStrict P G = true ↔ StoppingGame G ∧ ValueGreaterHalf G := by
  unfold decideSSGStrict
  by_cases hs : StoppingGame G
  · obtain ⟨v, hsol, hv, _⟩ := solveSSG_correct P G hs
    rw [stable_iff] at hv
    rw [(stoppingGame_iff_peelAll G).mp hs, hsol, valueGreaterHalf_iff G hs v hv]
    simp [hs]
  · simp [peelAll_false G hs, hs]

/-- **the decision problem `SSGDecision` is decided by `decideProblem`.** -/
theorem decideProblem_correct (P : PriceSearch n (Rb n)) (G : Game n) :
    decideProblem P G = true ↔ SSGDecision G := by
  unfold decideProblem SSGDecision; rw [Bool.and_eq_true, decide_eq_true_iff, decideSSG_correct]

theorem decideProblemStrict_correct (P : PriceSearch n (Rb n)) (G : Game n) :
    decideProblemStrict P G = true ↔ SSGDecisionStrict G := by
  unfold decideProblemStrict SSGDecisionStrict; rw [Bool.and_eq_true, decide_eq_true_iff, decideSSGStrict_correct]

/-! ## COSTS -/

/-- **cost: evaluations of `F`.** Every oracle call evaluates `F` once; a halting run makes at most `P.Q` calls,
and the transcript records exactly the queried price vectors with the oracle's answers. `solveSSG` evaluates `F`
once more (the final check). -/
theorem cost_queries (P : PriceSearch n (Rb n)) (G : Game n) (x : Fin n → ℚ) (T : Transcript n)
    (h : run P.strat (oracle G) P.Q [] = some (x, T)) :
    T.length ≤ P.Q ∧ ∀ q ∈ T, q.2 = oracle G q.1 :=
  ⟨P.queries_le (oracle G) x T h, run_answers P.strat (oracle G) P.Q [] x T h (by simp)⟩

theorem natAbs_num_div_le (a : ℤ) (b : ℕ) (hb : 0 < b) : ((a : ℚ) / (b : ℚ)).num.natAbs ≤ a.natAbs := by
  by_cases ha : a = 0
  · subst ha; simp
  · rw [show ((b : ℚ)) = ((b : ℤ) : ℚ) by simp, ← Rat.divInt_eq_div]
    have := Rat.num_dvd a (show (b : ℤ) ≠ 0 by omega)
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr ha) (Int.natAbs_dvd_natAbs.mpr this)

theorem den_div_le (a : ℤ) (b : ℕ) (hb : 0 < b) : ((a : ℚ) / (b : ℚ)).den ≤ b := by
  rw [show ((b : ℚ)) = ((b : ℤ) : ℚ) by simp, ← Rat.divInt_eq_div]
  have := Rat.den_dvd a (b : ℤ)
  have : (Rat.divInt a b).den ∣ b := by exact_mod_cast this
  exact Nat.le_of_dvd hb this

/-- the point as an explicit fraction. -/
theorem point_frac (G : Game n) (p : Fin n → ℚ) (i : Fin n) :
    point G p i = (((2 * 3 ^ prank G i - 1 : ℤ) * (p i).num : ℤ) : ℚ) /
      (((256 * 9 ^ n * 3 ^ prank G i * (p i).den : ℕ)) : ℚ) := by
  unfold point dlt wt
  have hd : ((p i).den : ℚ) ≠ 0 := by have := (p i).den_pos; positivity
  conv_lhs => rw [← Rat.num_div_den (p i)]
  push_cast
  rw [div_pow, one_pow]
  field_simp

/-- **cost: bit sizes.** If a queried price has numerator and denominator `≤ 2^B`, the point passed to `F` has
numerator and denominator `≤ 2^(B + 5n + 8)`. -/
theorem cost_bits (G : Game n) (B : ℕ) (p : Fin n → ℚ) (i : Fin n) (hp : BitBdd B (p i)) :
    BitBdd (B + 5 * n + 8) (point G p i) := by
  have hall_r : prank G i ≤ n := by
    unfold prank; exact cnt_le _ (peel_mono' G i) n
  have h3r : 3 ^ prank G i ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hall_r
  have h3pos : 0 < 3 ^ prank G i := by positivity
  have hden : 0 < 256 * 9 ^ n * 3 ^ prank G i * (p i).den := by have := (p i).den_pos; positivity
  rw [point_frac]
  constructor
  · refine le_trans (natAbs_num_div_le _ _ hden) ?_
    rw [Int.natAbs_mul]
    have e1 : (2 * 3 ^ prank G i - 1 : ℤ).natAbs ≤ 2 * 3 ^ n := by
      have : (2 * 3 ^ prank G i - 1 : ℤ) = ((2 * 3 ^ prank G i - 1 : ℕ) : ℤ) := by push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * 3 ^ prank G i)]; ring
      rw [this, Int.natAbs_natCast]; omega
    have e2 : 2 * 3 ^ n ≤ 2 ^ (5 * n + 8) := by
      have : 3 ^ n ≤ 4 ^ n := Nat.pow_le_pow_left (by norm_num) n
      have : 4 ^ n = 2 ^ (2 * n) := by rw [pow_mul]; norm_num
      have : 2 ^ (2 * n) * 2 ≤ 2 ^ (5 * n + 8) := by
        rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc (2 * 3 ^ prank G i - 1 : ℤ).natAbs * (p i).num.natAbs ≤ (2 * 3 ^ n) * 2 ^ B :=
          Nat.mul_le_mul e1 hp.1
      _ ≤ 2 ^ (5 * n + 8) * 2 ^ B := Nat.mul_le_mul_right _ e2
      _ = 2 ^ (B + 5 * n + 8) := by rw [← pow_add]; congr 1; omega
  · refine le_trans (den_div_le _ _ hden) ?_
    have e : 256 * 9 ^ n * 3 ^ prank G i ≤ 2 ^ (5 * n + 8) := by
      have : 256 * 9 ^ n * 3 ^ prank G i ≤ 256 * 27 ^ n := by
        have : 27 ^ n = 9 ^ n * 3 ^ n := by rw [← mul_pow]; norm_num
        rw [this, mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h3r)
      have : 27 ^ n ≤ 32 ^ n := Nat.pow_le_pow_left (by norm_num) n
      have : 32 ^ n = 2 ^ (5 * n) := by rw [pow_mul]; norm_num
      have : 2 ^ (5 * n + 8) = 2 ^ (5 * n) * 256 := by rw [pow_add]; norm_num
      omega
    calc 256 * 9 ^ n * 3 ^ prank G i * (p i).den ≤ 2 ^ (5 * n + 8) * 2 ^ B := Nat.mul_le_mul e hp.2
      _ = 2 ^ (B + 5 * n + 8) := by rw [← pow_add]; congr 1; omega

/-- every point passed to `F` during a halting run is `(B + 5n + 8)`-bounded. -/
theorem cost_bits_run (P : PriceSearch n (Rb n)) (G : Game n) (x : Fin n → ℚ) (T : Transcript n)
    (h : run P.strat (oracle G) P.Q [] = some (x, T)) :
    ∀ q ∈ T, ∀ i, BitBdd (P.B + 5 * n + 8) (point G q.1 i) ∧ BitBdd (P.B + 5 * n + 8) (point G x i) :=
  fun q hq i => ⟨cost_bits G P.B q.1 i (P.priceBits (oracle G) x T h q hq i),
    cost_bits G P.B x i (P.outBits (oracle G) x T h i)⟩

def cfZ (G : Game n) (t j : Fin n) : ℤ := if j = t ∧ isTerminal G t = false then 1 else 0
def svZ (G : Game n) (t : Fin n) : ℤ :=
  match G.nodeType t with
  | .terminal1 => 1
  | _ => 0

/-- twice the chain matrix, as integers. -/
def twoA (G : Game n) (π : Fin n → Bool) (i j : Fin n) : ℤ :=
  2 * (if j = i then 1 else 0) -
    (match G.nodeType i with
     | .terminal0 => 0
     | .terminal1 => 0
     | .max => 2 * cfZ G (G.child i (π i)) j
     | .min => 2 * cfZ G (G.child i (π i)) j
     | .average => cfZ G (G.child i false) j + cfZ G (G.child i true) j)

/-- twice the right-hand side, as integers. -/
def twoB (G : Game n) (π : Fin n → Bool) (i : Fin n) : ℤ :=
  match G.nodeType i with
  | .terminal0 => 0
  | .terminal1 => 2
  | .max => 2 * svZ G (G.child i (π i))
  | .min => 2 * svZ G (G.child i (π i))
  | .average => svZ G (G.child i false) + svZ G (G.child i true)

/-- **cost: the linear system.** The chain matrix has entries in `{0, ±1/2, ±1}` (twice an integer in `[-2,2]`)
and the right-hand side entries in `{0, 1/2, 1}`. -/
theorem chain_entries (G : Game n) (π : Fin n → Bool) :
    (∀ i j, 2 * chainA G π i j = twoA G π i j ∧ -2 ≤ twoA G π i j ∧ twoA G π i j ≤ 2) ∧
    (∀ i, 2 * chainB G π i = twoB G π i ∧ 0 ≤ twoB G π i ∧ twoB G π i ≤ 2) := by
  have cfe : ∀ t j, cf G t j = (cfZ G t j : ℚ) := by intro t j; unfold cf cfZ; split <;> simp
  have sve : ∀ t, sv G t = (svZ G t : ℚ) := by intro t; unfold sv svZ; cases G.nodeType t <;> simp
  have cfb : ∀ t j, 0 ≤ cfZ G t j ∧ cfZ G t j ≤ 1 := by intro t j; unfold cfZ; split <;> simp
  have svb : ∀ t, 0 ≤ svZ G t ∧ svZ G t ≤ 1 := by intro t; unfold svZ; split <;> simp
  constructor
  · intro i j
    have dij : ∀ c : ℤ, (c = 0 ∨ c = 1) → True := fun _ _ => trivial
    have hd : (0 : ℤ) ≤ (if j = i then 1 else 0) ∧ (if j = i then (1 : ℤ) else 0) ≤ 1 := by split <;> simp
    have hdq : (if j = i then (1 : ℚ) else 0) = ((if j = i then (1 : ℤ) else 0 : ℤ) : ℚ) := by split <;> simp
    unfold chainA twoA
    rw [hdq]
    cases G.nodeType i <;> simp only [cfe] <;> push_cast <;> refine ⟨by ring, ?_, ?_⟩
    all_goals
      first
      | omega
      | (have := cfb (G.child i (π i)) j; omega)
      | (have := cfb (G.child i false) j; have := cfb (G.child i true) j; omega)
  · intro i
    unfold chainB twoB
    cases G.nodeType i
    all_goals (try simp only [sve]); (try push_cast)
    all_goals refine ⟨by ring, ?_, ?_⟩
    all_goals
      first
      | trivial
      | omega
      | (have := svb (G.child i (π i)); omega)
      | (have := svb (G.child i false); have := svb (G.child i true); omega)

/-- **the price-search instance used**: `N = n`, `R = 1024·9^n`, so `log₂ R ≤ 4n + 10`. -/
theorem log_Rb (n : ℕ) : Nat.log2 (Rb n) ≤ 4 * n + 10 := by
  have h : Rb n < 2 ^ (4 * n + 11) := by
    unfold Rb
    have : 9 ^ n ≤ 16 ^ n := Nat.pow_le_pow_left (by norm_num) n
    have : 16 ^ n = 2 ^ (4 * n) := by rw [pow_mul]; norm_num
    have : 2 ^ (4 * n + 11) = 2 ^ (4 * n) * 2048 := by rw [pow_add]; norm_num
    have : 0 < 2 ^ (4 * n) := by positivity
    omega
  have hne : Rb n ≠ 0 := by unfold Rb; positivity
  have := (Nat.log2_lt hne).mpr h
  omega

/-- **polynomial corollary**: from a polynomial family of price searches, the number of `F` evaluations and the
bit bound of every point passed to `F` are polynomial in `n`. -/
theorem poly_cost (Pf : ∀ N R : ℕ, PriceSearch N R) (hP : PolyFamily Pf) :
    ∃ c k : ℕ, ∀ n, (Pf n (Rb n)).Q ≤ c * (5 * n + 12) ^ k ∧ (Pf n (Rb n)).B + 5 * n + 8 ≤ c * (5 * n + 12) ^ k + 5 * n + 8 := by
  obtain ⟨c, k, h⟩ := hP
  refine ⟨c, k, fun n => ?_⟩
  have hl := log_Rb n
  have mono : (n + Nat.log2 (Rb n) + 2) ^ k ≤ (5 * n + 12) ^ k := Nat.pow_le_pow_left (by omega) k
  obtain ⟨h1, h2⟩ := h n (Rb n)
  exact ⟨le_trans h1 (Nat.mul_le_mul_left _ mono), by have := le_trans h2 (Nat.mul_le_mul_left c mono); omega⟩

end SSG
