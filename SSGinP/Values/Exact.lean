module

public import SSGinP.Values.Round
public import SSGinP.Values.Engine

@[expose] public section

/-!
# SSGinP.Values.Exact: exact values from threshold tests, WITHOUT a linear solve

Algorithm-level theorem.

* `thr a j = (2a+1)/2^(j+1)` : the midpoint of the dyadic interval `[a/2^j, (a+1)/2^j]`.
* `bStep c`                  : one bisection step on the state `(a, j)`: ask the test `c a j` (at the threshold
                               `thr a j`), keep the upper half (`2a+1`) or the lower half (`2a`).
* `exactOf n a`              : the reconstruction `recon` of the fraction with denominator `≤ 3^n` next to
                               `thr a (4n+1)`.
* `valueBy c n`              : `4n+1` bisection steps, then `exactOf`.
* `valueBy_exact`            : if the tests are right at distance `≥ 1/(4·9^n)` from `v`, `0 ≤ v ≤ 1` and
                               `v.den ≤ 3^n`, then `valueBy c n = v`.
* `solveExact call G`, MAIN `solveExact_correct` : on a Stopping Game with fuzzy tests, the values of all nodes
                               (the stable assignment) and optimal strategies.
-/

namespace SSGValues

open SSG SSG28Reply

variable {n : ℕ}

/-- the threshold asked in the state `(a, j)`. -/
def thr (a j : ℕ) : ℚ := (2 * (a : ℚ) + 1) / 2 ^ (j + 1)

/-- one bisection step. -/
def bStep (c : ℕ → ℕ → Bool) (s : ℕ × ℕ) : ℕ × ℕ := (if c s.1 s.2 then 2 * s.1 + 1 else 2 * s.1, s.2 + 1)

/-- the test `c` is right at distance `≥ Δ` from `v`, at every threshold. -/
def FuzzyN (c : ℕ → ℕ → Bool) (v Δ : ℚ) : Prop :=
  ∀ a j, (thr a j + Δ ≤ v → c a j = true) ∧ (v ≤ thr a j - Δ → c a j = false)

/-- the invariant of the bisection. -/
def BInv (v Δ : ℚ) (s : ℕ × ℕ) : Prop :=
  s.1 + 1 ≤ 2 ^ s.2 ∧ (s.1 : ℚ) / 2 ^ s.2 - Δ < v ∧ v < ((s.1 : ℚ) + 1) / 2 ^ s.2 + Δ

theorem bStep_inv {c : ℕ → ℕ → Bool} {v Δ : ℚ} (hc : FuzzyN c v Δ) (s : ℕ × ℕ) (h : BInv v Δ s) :
    BInv v Δ (bStep c s) := by
  obtain ⟨a, j⟩ := s
  obtain ⟨h0, h1, h2⟩ := h
  simp only at h0 h1 h2
  have hp : (0 : ℚ) < 2 ^ j := by positivity
  have eL : ((2 * a : ℕ) : ℚ) / 2 ^ (j + 1) = (a : ℚ) / 2 ^ j := by push_cast; rw [pow_succ]; field_simp
  have eR : (((2 * a + 1 : ℕ) : ℚ) + 1) / 2 ^ (j + 1) = ((a : ℚ) + 1) / 2 ^ j := by
    push_cast; rw [pow_succ]; field_simp; ring
  have eM : ((2 * a + 1 : ℕ) : ℚ) / 2 ^ (j + 1) = thr a j := by unfold thr; push_cast; rfl
  have eM' : (((2 * a : ℕ) : ℚ) + 1) / 2 ^ (j + 1) = thr a j := by unfold thr; push_cast; rfl
  have hpow : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
  unfold bStep BInv
  cases hm : c a j
  · simp only [Bool.false_eq_true, if_false]
    have hv : v < thr a j + Δ := by
      by_contra hlt; push Not at hlt
      have := (hc a j).1 hlt; rw [hm] at this; cases this
    exact ⟨by omega, by rw [eL]; exact h1, by rw [eM']; exact hv⟩
  · simp only [if_true]
    have hv : thr a j - Δ < v := by
      by_contra hlt; push Not at hlt
      have := (hc a j).2 hlt; rw [hm] at this; cases this
    exact ⟨by omega, by rw [eM]; exact hv, by rw [eR]; exact h2⟩

theorem bStep_iter_inv {c : ℕ → ℕ → Bool} {v Δ : ℚ} (hc : FuzzyN c v Δ) (s : ℕ × ℕ) (h : BInv v Δ s) :
    ∀ m, BInv v Δ ((bStep c)^[m] s)
  | 0 => h
  | m + 1 => by rw [Function.iterate_succ_apply']; exact bStep_inv hc _ (bStep_iter_inv hc s h m)

theorem bStep_iter_snd (c : ℕ → ℕ → Bool) (s : ℕ × ℕ) : ∀ m, ((bStep c)^[m] s).2 = s.2 + m
  | 0 => rfl
  | m + 1 => by rw [Function.iterate_succ_apply', bStep, bStep_iter_snd c s m]; rfl

theorem bInv_init {v Δ : ℚ} (hΔ : 0 < Δ) (hv : 0 ≤ v ∧ v ≤ 1) : BInv v Δ (0, 0) := by
  refine ⟨by simp, ?_, ?_⟩ <;> simp <;> linarith [hv.1, hv.2]

/-- number of bisection steps per node. -/
def stepsX (n : ℕ) : ℕ := 4 * n + 1

/-- the reconstruction from the numerator `a` reached after `stepsX n` steps. -/
def exactOf (n a : ℕ) : ℚ := recon (2 ^ (4 * n + 2)) (3 ^ n) (2 * a + 1) (3 * n + 2)

theorem fuel_ok (n : ℕ) : 2 ^ (3 * n + 2) * (2 * 3 ^ n) < 3 ^ (3 * n + 2) := by
  have h1 : (2 : ℕ) ^ (3 * n + 2) = 4 * 8 ^ n := by rw [pow_add, pow_mul]; norm_num; ring
  have h2 : (3 : ℕ) ^ (3 * n + 2) = 9 * 27 ^ n := by rw [pow_add, pow_mul]; norm_num; ring
  have h3 : (8 : ℕ) ^ n * 3 ^ n = 24 ^ n := by rw [← mul_pow]; norm_num
  have h4 : (24 : ℕ) ^ n ≤ 27 ^ n := Nat.pow_le_pow_left (by norm_num) n
  have h5 : 0 < 27 ^ n := by positivity
  rw [h1, h2]
  calc 4 * 8 ^ n * (2 * 3 ^ n) = 8 * (8 ^ n * 3 ^ n) := by ring
    _ = 8 * 24 ^ n := by rw [h3]
    _ < 9 * 27 ^ n := by omega

/-- **exact recovery from the last bisection interval.** -/
theorem exactOf_eq (n a : ℕ) (v : ℚ) (h : BInv v (Delta n) (a, stepsX n)) (hden : v.den ≤ 3 ^ n) :
    exactOf n a = v := by
  obtain ⟨h0, h1, h2⟩ := h
  simp only [stepsX] at h0 h1 h2
  have hpow : 2 ^ (4 * n + 2) = 2 * 2 ^ (4 * n + 1) := by rw [pow_succ]; ring
  refine recon_exact _ _ _ _ v (by positivity) (by omega) hden ?_ (fuel_ok n)
  -- |x - v| < 1/2^(4n+2) + Δ ≤ 1/(2·9^n)
  have hp : (0 : ℚ) < 2 ^ (4 * n + 1) := by positivity
  have ex : (((2 * a + 1 : ℕ) : ℚ)) / ((2 ^ (4 * n + 2) : ℕ) : ℚ) =
      ((a : ℚ) / 2 ^ (4 * n + 1) + ((a : ℚ) + 1) / 2 ^ (4 * n + 1)) / 2 := by
    push_cast; rw [pow_succ]; field_simp; ring
  have ew : ((a : ℚ) + 1) / 2 ^ (4 * n + 1) - (a : ℚ) / 2 ^ (4 * n + 1) = 1 / 2 ^ (4 * n + 1) := by
    field_simp; ring
  have h9 : (9 : ℚ) ^ n ≤ 16 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have e16 : (2 : ℚ) ^ (4 * n + 1) = 2 * 16 ^ n := by rw [pow_succ, pow_mul]; norm_num; ring
  have h9p : (0 : ℚ) < 9 ^ n := by positivity
  have hb : (1 : ℚ) / 2 ^ (4 * n + 1) / 2 ≤ 1 / (4 * 9 ^ n) := by
    rw [e16, div_div]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hQ : (1 : ℚ) / (2 * ((3 ^ n : ℕ) : ℚ) ^ 2) = 1 / (4 * 9 ^ n) + 1 / (4 * 9 ^ n) := by
    push_cast
    rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
    field_simp; ring
  rw [ex, hQ, abs_lt]
  unfold Delta at h1 h2
  constructor <;> linarith

/-- the value computed from a test: `stepsX n` bisection steps, then the reconstruction. -/
def valueBy (c : ℕ → ℕ → Bool) (n : ℕ) : ℚ := exactOf n ((bStep c)^[stepsX n] (0, 0)).1

theorem valueBy_exact (c : ℕ → ℕ → Bool) (n : ℕ) (v : ℚ) (hc : FuzzyN c v (Delta n)) (hv : 0 ≤ v ∧ v ≤ 1)
    (hden : v.den ≤ 3 ^ n) : valueBy c n = v := by
  have hΔ : 0 < Delta n := by unfold Delta; positivity
  have h := bStep_iter_inv hc (0, 0) (bInv_init hΔ hv) (stepsX n)
  have e2 := bStep_iter_snd c (0, 0) (stepsX n)
  simp only [zero_add] at e2
  unfold valueBy
  apply exactOf_eq n _ v _ hden
  have : ((bStep c)^[stepsX n] (0, 0)) = (((bStep c)^[stepsX n] (0, 0)).1, stepsX n) := Prod.ext rfl e2
  rw [← this]; exact h

/-- every value of a Stopping Game is a fraction with denominator at most `3^n`. -/
theorem value_den (G : Game n) (hs : StoppingGame G) (v : Fin n → ℚ) (hv : F G v = v) (i : Fin n) :
    (v i).den ≤ 3 ^ n := by
  have hr := prank_ranked G (peelAll_of_stoppingGame G hs)
  obtain ⟨D, hD0, hD, hz⟩ := denom_bound G (prank G) hr v hv
  obtain ⟨z, hz⟩ := hz i
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD0.ne'
  have e : v i = (z : ℚ) / ((D : ℤ) : ℚ) := by push_cast; rw [eq_div_iff hDq, mul_comm]; exact hz
  have hdvd : ((v i).den : ℤ) ∣ (D : ℤ) := by rw [e, ← Rat.divInt_eq_div]; exact Rat.den_dvd z D
  exact (Nat.le_of_dvd hD0 (by exact_mod_cast hdvd)).trans hD

/-- **the algorithm (exact values without a linear solve)**: for every node `4n+1` tests and one
reconstruction; then the greedy strategies of the values. -/
def solveExact (call : Fin n → ℕ → ℕ → Bool) (G : Game n) : Solution n :=
  ⟨fun k => valueBy (call k) n, greedyMax G (fun k => valueBy (call k) n),
    greedyMin G (fun k => valueBy (call k) n)⟩

/-- **MAIN (algorithm level).** On a Stopping Game with stable assignment `v`, if every test `call k` is right
at distance `≥ 1/(4·9^n)` from `v k`, then `solveExact` returns `v` with optimal strategies. -/
theorem solveExact_correct (call : Fin n → ℕ → ℕ → Bool) (G : Game n) (hs : StoppingGame G) (v : Fin n → ℚ)
    (hv : F G v = v) (hc : ∀ k, FuzzyN (call k) (v k) (Delta n)) :
    (solveExact call G).value = v ∧
      IsSolution G (solveExact call G).value (solveExact call G).maxStrategy (solveExact call G).minStrategy := by
  have hr := prank_ranked G (peelAll_of_stoppingGame G hs)
  have hb := fix_bounds G (prank G) hr v hv
  have e : (fun k => valueBy (call k) n) = v :=
    funext fun k => valueBy_exact (call k) n (v k) (hc k) (hb k) (value_den G hs v hv k)
  refine ⟨e, ?_⟩
  unfold solveExact
  simp only [e]
  exact greedy_isSolution G hs v hv


end SSGValues
