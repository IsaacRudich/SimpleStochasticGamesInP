module

public import SSGinP.Values.Basic
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# SSGinP.Values.Round: exact recovery of a fraction with bounded denominator

Pure arithmetic, used for the exact values (values of all nodes at machine level, without a linear solve).

`x = A / N` is an approximation of a rational `v` whose denominator is at most `Q`, with
`|x - v| < 1 / (2 Q²)`.  Then `v` is found by the Euclid / continued-fraction recurrence on `(N, A)`:

* state `((N, Q), (r0, r1), (s0, s1), (q0, q1))`, all natural numbers; `s1 / q1` is the current convergent of
  `A / N` and `r1 = |q1 A - s1 N|`;
* `cfPass`  : the current convergent has `q1 ≤ Q` and `2 Q² r1 < N q1`  (i.e. `|x - s1/q1| < 1/(2Q²)`);
* `cfStep`  : stay if `cfPass`, else one Euclid step;
* `recon N Q A T` : the convergent after `T` steps from `cfInit N Q A`.

MAIN `recon_exact`: if `A ≤ N`, `0 < N`, `v.den ≤ Q`, `|A/N - v| < 1/(2Q²)` and `2^T · 2Q < 3^T`,
then `recon N Q A T = v`.

Proof: Legendre's argument.  Two consecutive convergents form a basis of `ℤ²` (determinant `±1`), so a
fraction `p/q` with `q1 ≤ q < q2` and `2 q |qA - pN| < N` equals `s1/q1` (`legendre_core`); a convergent that
passes the test equals `v` (`pass_unique`); `q0 + q1` grows by the factor `3/2` in every step, which bounds the
number of steps.
-/

namespace SSGValues

/-- `((N, Q), (r0, r1), (s0, s1), (q0, q1))`. -/
abbrev CFState := (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)

/-- the current convergent is accepted: `q1 ≤ Q` and `2 Q² r1 < N q1`. -/
def cfPass (st : CFState) : Bool :=
  decide (st.2.2.2.2 ≤ st.1.2) && decide (2 * st.1.2 * st.1.2 * st.2.1.2 < st.1.1 * st.2.2.2.2)

/-- one Euclid step. -/
def cfAdv (st : CFState) : CFState :=
  (st.1, (st.2.1.2, st.2.1.1 % st.2.1.2),
    (st.2.2.1.2, st.2.2.1.1 + st.2.1.1 / st.2.1.2 * st.2.2.1.2),
    (st.2.2.2.2, st.2.2.2.1 + st.2.1.1 / st.2.1.2 * st.2.2.2.2))

def cfStep (st : CFState) : CFState := if cfPass st then st else cfAdv st

def cfInit (N Q A : ℕ) : CFState := ((N, Q), (N, A), (1, 0), (0, 1))

/-- the fraction read from a state. -/
def cfOut (st : CFState) : ℚ := (st.2.2.1.2 : ℚ) / (st.2.2.2.2 : ℚ)

/-- **the reconstruction**: `T` steps from the initial state. -/
def recon (N Q A T : ℕ) : ℚ := cfOut (cfStep^[T] (cfInit N Q A))

theorem cfStep_pass (st : CFState) (h : cfPass st = true) : ∀ f, cfStep^[f] st = st
  | 0 => rfl
  | f + 1 => by
    rw [Function.iterate_succ_apply, show cfStep st = st by simp [cfStep, h]]
    exact cfStep_pass st h f

set_option maxHeartbeats 400000 in
/-- **Legendre's argument.** `(s1, q1)`, `(s2, q2)` consecutive convergents, `q1 ≤ q < q2`, `2 q |ρ| < N`
with `ρ = q A - p N`: then `p / q = s1 / q1`. -/
theorem legendre_core (N A : ℤ) (e r1 r2 s1 s2 q1 q2 p q R : ℤ) (he : e = 1 ∨ e = -1)
    (h1 : q1 * A - s1 * N = e * r1) (h2 : q2 * A - s2 * N = -e * r2) (hd : s2 * q1 - s1 * q2 = e)
    (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) (hq1 : 1 ≤ q1) (hq : q1 ≤ q) (hq2 : q < q2)
    (hR1 : q * A - p * N ≤ R) (hR2 : -(q * A - p * N) ≤ R) (hN : 2 * q * R < N) :
    p * q1 = s1 * q := by
  by_contra hne
  have hee : e * e = 1 := by rcases he with h | h <;> rw [h] <;> norm_num
  obtain ⟨δ, hδ⟩ : ∃ δ : ℤ, δ = p * q1 - s1 * q := ⟨_, rfl⟩
  have hδ0 : δ ≠ 0 := fun h => hne (by linarith)
  obtain ⟨β, hβ⟩ : ∃ β : ℤ, β = e * δ := ⟨_, rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : ℤ, α = -e * (p * q2 - s2 * q) := ⟨_, rfl⟩
  have hqe : q = α * q1 + β * q2 := by
    rw [hα, hβ, hδ]; linear_combination (-q) * hee - e * q * hd
  have e2 : p = α * s1 + β * s2 := by
    rw [hα, hβ, hδ]; linear_combination (-p) * hee - e * p * hd
  have hρ : q * A - p * N = e * (α * r1 - β * r2) := by
    linear_combination A * hqe - N * e2 + α * h1 + β * h2
  have hβ0 : β ≠ 0 := by
    intro h
    rcases he with h' | h' <;> rw [hβ, h'] at h <;> simp at h <;> exact hδ0 h
  have hR0 : 0 ≤ R := by linarith
  -- `r1 ≤ R`
  have hr1R : r1 ≤ R := by
    rcases lt_or_gt_of_ne hβ0 with hb | hb
    · -- β ≤ -1, so α ≥ 1
      have hb' : β ≤ -1 := by omega
      have hαpos : 1 ≤ α := by
        by_contra hc
        have hα0 : α ≤ 0 := by omega
        nlinarith [mul_nonneg (neg_nonneg.mpr hα0) (by linarith : (0:ℤ) ≤ q1),
          mul_le_mul_of_nonneg_right hb' (by linarith : (0:ℤ) ≤ q2)]
      have key : r1 ≤ α * r1 - β * r2 := by
        nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ α - 1) hr1, mul_nonneg (by linarith : (0:ℤ) ≤ -β) hr2]
      rcases he with h | h <;> rw [h] at hρ <;> linarith
    · have hb' : 1 ≤ β := by omega
      have hαneg : α ≤ -1 := by
        by_contra hc
        have hα0 : 0 ≤ α := by omega
        nlinarith [mul_nonneg hα0 (by linarith : (0:ℤ) ≤ q1),
          mul_le_mul_of_nonneg_right hb' (by linarith : (0:ℤ) ≤ q2)]
      have key : α * r1 - β * r2 ≤ -r1 := by
        nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ -α - 1) hr1, mul_nonneg (by linarith : (0:ℤ) ≤ β) hr2]
      rcases he with h | h <;> rw [h] at hρ <;> linarith
  -- `N δ = - q1 ρ + q ρ1`
  have hNδ : N * δ = -(q1 * (q * A - p * N)) + q * (e * r1) := by rw [← h1, hδ]; ring
  have hqpos : 0 ≤ q := by linarith
  have a1 : q1 * R ≤ q * R := mul_le_mul_of_nonneg_right hq hR0
  have a2 : q * r1 ≤ q * R := mul_le_mul_of_nonneg_left hr1R hqpos
  have a3 : q1 * (q * A - p * N) ≤ q1 * R := mul_le_mul_of_nonneg_left hR1 (by linarith)
  have a4 : q1 * (-(q * A - p * N)) ≤ q1 * R := mul_le_mul_of_nonneg_left hR2 (by linarith)
  have a5 : 0 ≤ q * r1 := mul_nonneg hqpos hr1
  have a6 : 0 ≤ q * R := mul_nonneg hqpos hR0
  have hup : N * δ < N := by rcases he with h | h <;> rw [h] at hNδ <;> linarith
  have hlo : -N < N * δ := by rcases he with h | h <;> rw [h] at hNδ <;> linarith
  have hNpos : 0 < N := by linarith
  have d1 : δ < 1 := by by_contra hc; nlinarith [mul_le_mul_of_nonneg_left (not_lt.mp hc) hNpos.le]
  have d2 : -1 < δ := by
    by_contra hc
    have : δ ≤ -1 := not_lt.mp hc
    nlinarith [mul_le_mul_of_nonneg_left this hNpos.le]
  exact hδ0 (by omega)

/-- **an accepted convergent is the target.** -/
theorem pass_unique (N A Q : ℤ) (e r1 s1 q1 p q R : ℤ) (he : e = 1 ∨ e = -1)
    (h1 : q1 * A - s1 * N = e * r1) (hr1 : 0 ≤ r1) (hq1 : 1 ≤ q1) (hq0 : 1 ≤ q) (hqQ : q ≤ Q) (hq1Q : q1 ≤ Q)
    (hpass : 2 * Q * Q * r1 < N * q1)
    (hR1 : q * A - p * N ≤ R) (hR2 : -(q * A - p * N) ≤ R) (hN : 2 * Q * Q * R < N * q) :
    p * q1 = s1 * q := by
  obtain ⟨δ, hδ⟩ : ∃ δ : ℤ, δ = p * q1 - s1 * q := ⟨_, rfl⟩
  have hNδ : N * δ = -(q1 * (q * A - p * N)) + q * (e * r1) := by rw [← h1, hδ]; ring
  have hR0 : 0 ≤ R := by linarith
  have hQ : 1 ≤ Q := by linarith
  have hNpos : 0 < N := by
    by_contra hc
    have : N ≤ 0 := not_lt.mp hc
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ 2 * Q) (by linarith : (0:ℤ) ≤ Q)) hR0,
      mul_nonneg (neg_nonneg.mpr this) (by linarith : (0:ℤ) ≤ q)]
  have hQQ : 0 < 2 * Q * Q := by positivity
  -- 2Q² q1 R < N q q1,  2Q² q r1 < N q q1
  have b1 : 2 * Q * Q * (q1 * R) < N * q * q1 := by
    have := mul_lt_mul_of_pos_right hN (by linarith : (0:ℤ) < q1)
    nlinarith
  have b2 : 2 * Q * Q * (q * r1) < N * q * q1 := by
    have := mul_lt_mul_of_pos_right hpass (by linarith : (0:ℤ) < q)
    nlinarith
  have b3 : q * q1 ≤ Q * Q := by
    nlinarith [mul_le_mul_of_nonneg_left hq1Q (by linarith : (0:ℤ) ≤ q),
      mul_le_mul_of_nonneg_right hqQ (by linarith : (0:ℤ) ≤ Q)]
  have b4 : N * q * q1 ≤ N * (Q * Q) := by
    have := mul_le_mul_of_nonneg_left b3 hNpos.le
    nlinarith
  have a3 : q1 * (q * A - p * N) ≤ q1 * R := mul_le_mul_of_nonneg_left hR1 (by linarith)
  have a4 : q1 * (-(q * A - p * N)) ≤ q1 * R := mul_le_mul_of_nonneg_left hR2 (by linarith)
  have a5 : 0 ≤ q * r1 := mul_nonneg (by linarith) hr1
  have hup : 2 * Q * Q * (N * δ) < 2 * Q * Q * N := by
    rcases he with h | h <;> rw [h] at hNδ <;> rw [hNδ] <;> nlinarith
  have hlo : -(2 * Q * Q * N) < 2 * Q * Q * (N * δ) := by
    rcases he with h | h <;> rw [h] at hNδ <;> rw [hNδ] <;> nlinarith
  have hpos : 0 < 2 * Q * Q * N := mul_pos hQQ hNpos
  have d1 : δ < 1 := by
    by_contra hc
    have := mul_le_mul_of_nonneg_left (not_lt.mp hc) hpos.le
    nlinarith
  have d2 : -1 < δ := by
    by_contra hc
    have h' : δ ≤ -1 := not_lt.mp hc
    have := mul_le_mul_of_nonneg_left h' hpos.le
    nlinarith
  have : δ = 0 := by omega
  rw [this] at hδ; linarith

set_option maxHeartbeats 1000000 in
/-- the loop: from a state satisfying the invariant with `q1 ≤ q`, enough fuel reaches the target. -/
theorem cf_iter (N Q A : ℕ) (p : ℤ) (q : ℕ) (R : ℤ) (hq0 : 1 ≤ q) (hqQ : q ≤ Q)
    (hR1 : (q : ℤ) * A - p * N ≤ R) (hR2 : -((q : ℤ) * A - p * N) ≤ R) (hN : 2 * (Q : ℤ) * Q * R < N * q) :
    ∀ (f : ℕ) (r0 r1 s0 s1 q0 q1 : ℕ) (e : ℤ), (e = 1 ∨ e = -1) →
      (q0 : ℤ) * A - s0 * N = -e * r0 → (q1 : ℤ) * A - s1 * N = e * r1 → (s1 : ℤ) * q0 - s0 * q1 = -e →
      1 ≤ q1 → q0 ≤ q1 → r1 ≤ r0 → q1 ≤ q → 2 ^ f * (2 * Q) < 3 ^ f * (q0 + q1) →
      1 ≤ (cfStep^[f] ((N, Q), (r0, r1), (s0, s1), (q0, q1))).2.2.2.2 ∧
      p * ((cfStep^[f] ((N, Q), (r0, r1), (s0, s1), (q0, q1))).2.2.2.2 : ℤ) =
        ((cfStep^[f] ((N, Q), (r0, r1), (s0, s1), (q0, q1))).2.2.1.2 : ℤ) * q := by
  have hR0 : 0 ≤ R := by linarith
  have hNpos : 0 < (N : ℤ) := by
    by_contra hc
    have : (N : ℤ) ≤ 0 := not_lt.mp hc
    have hQ : (1 : ℤ) ≤ Q := by exact_mod_cast hq0.trans hqQ
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℤ) ≤ 2 * Q) (by linarith : (0:ℤ) ≤ Q)) hR0,
      mul_nonneg (neg_nonneg.mpr this) (by exact_mod_cast (Nat.zero_le q) : (0:ℤ) ≤ q)]
  intro f
  induction f with
  | zero =>
    intro r0 r1 s0 s1 q0 q1 e he i1 i2 i3 hq1 hq01 hr hq1q hfuel
    simp only [pow_zero, one_mul] at hfuel
    omega
  | succ f ih =>
    intro r0 r1 s0 s1 q0 q1 e he i1 i2 i3 hq1 hq01 hr hq1q hfuel
    by_cases hp : cfPass ((N, Q), (r0, r1), (s0, s1), (q0, q1)) = true
    · rw [cfStep_pass _ hp]
      have hp' := hp
      simp only [cfPass, Bool.and_eq_true, decide_eq_true_iff] at hp'
      exact ⟨hq1, pass_unique N A Q e r1 s1 q1 p q R he i2 (by positivity) (by exact_mod_cast hq1)
        (by exact_mod_cast hq0) (by exact_mod_cast hqQ) (by exact_mod_cast hp'.1) (by exact_mod_cast hp'.2)
        hR1 hR2 hN⟩
    · -- not accepted
      have hq1Q : q1 ≤ Q := hq1q.trans hqQ
      have hnp : ¬ (2 * Q * Q * r1 < N * q1) := by
        intro h; apply hp; simp only [cfPass, Bool.and_eq_true, decide_eq_true_iff]; exact ⟨hq1Q, h⟩
      have hr1 : 0 < r1 := by
        by_contra hc
        have : r1 = 0 := by omega
        apply hnp; rw [this]
        have : 0 < N := by exact_mod_cast hNpos
        simp only [mul_zero]; positivity
      set c := r0 / r1 with hc
      have hc1 : 1 ≤ c := (Nat.one_le_div_iff hr1).mpr hr
      have hmod : r0 = r1 * c + r0 % r1 := (Nat.div_add_mod r0 r1).symm
      have hmodZ : (r0 : ℤ) = r1 * c + (r0 % r1 : ℕ) := by exact_mod_cast hmod
      have j1 : ((q0 + c * q1 : ℕ) : ℤ) * A - ((s0 + c * s1 : ℕ) : ℤ) * N = -e * ((r0 % r1 : ℕ) : ℤ) := by
        push_cast
        have : ((q0 : ℤ) + c * q1) * A - ((s0 : ℤ) + c * s1) * N =
            ((q0 : ℤ) * A - s0 * N) + c * ((q1 : ℤ) * A - s1 * N) := by ring
        rw [this, i1, i2]
        have : ((r0 % r1 : ℕ) : ℤ) = r0 - r1 * c := by linarith
        push_cast at this
        rw [this]; ring
      have j3 : ((s0 + c * s1 : ℕ) : ℤ) * q1 - (s1 : ℤ) * ((q0 + c * q1 : ℕ) : ℤ) = -(-e) := by
        push_cast; linarith [i3, show ((s0 : ℤ) + c * s1) * q1 - (s1 : ℤ) * (q0 + c * q1) = -((s1 : ℤ) * q0 - s0 * q1) by ring]
      have hq2ge : q0 + q1 ≤ q0 + c * q1 := by nlinarith
      -- `q2 ≤ q`
      have hq2 : q0 + c * q1 ≤ q := by
        by_contra hlt
        have hlt' : q < q0 + c * q1 := not_le.mp hlt
        have hδ := legendre_core N A e r1 ((r0 % r1 : ℕ) : ℤ) s1 ((s0 + c * s1 : ℕ) : ℤ) q1
          ((q0 + c * q1 : ℕ) : ℤ) p q R he i2 j1 (by rw [j3]; ring) (by positivity) (by positivity)
          (by exact_mod_cast hq1) (by exact_mod_cast hq1q) (by exact_mod_cast hlt') hR1 hR2 (by
            have h1 : (0:ℤ) < q := by exact_mod_cast hq0
            have hqQ' : (q : ℤ) ≤ Q := by exact_mod_cast hqQ
            have h2 : (q : ℤ) * q ≤ Q * Q := by
              nlinarith [mul_le_mul_of_nonneg_left hqQ' h1.le, mul_le_mul_of_nonneg_right hqQ' (by linarith : (0:ℤ) ≤ Q)]
            have h3 : 2 * (Q : ℤ) * Q * R * q < N * q * q := by
              have := mul_lt_mul_of_pos_right hN h1; linarith
            have h4 : 2 * ((q : ℤ) * q) * R ≤ 2 * (Q * Q) * R := by
              have := mul_le_mul_of_nonneg_right h2 hR0; linarith
            have h5 : (2 * (q : ℤ) * R) * q < N * q := by nlinarith
            exact lt_of_mul_lt_mul_right h5 h1.le)
        -- then the convergent is accepted
        apply hnp
        have hqpos : (0:ℤ) < q := by exact_mod_cast hq0
        have hq1pos : (0:ℤ) < q1 := by exact_mod_cast hq1
        -- e r1 q = q1 ρ
        have e1 : e * (r1 : ℤ) * q = q1 * ((q : ℤ) * A - p * N) := by
          rw [← i2]; linear_combination (N : ℤ) * hδ
        have e2 : (r1 : ℤ) * q ≤ q1 * R := by
          rcases he with h | h <;> rw [h] at e1
          · nlinarith [mul_le_mul_of_nonneg_left hR1 hq1pos.le]
          · nlinarith [mul_le_mul_of_nonneg_left hR2 hq1pos.le]
        have e3 : 2 * (Q : ℤ) * Q * r1 * q < N * q1 * q := by
          have h1 : 2 * (Q : ℤ) * Q * (r1 * q) ≤ 2 * Q * Q * (q1 * R) :=
            mul_le_mul_of_nonneg_left e2 (by positivity)
          have h2 := mul_lt_mul_of_pos_right hN hq1pos
          nlinarith
        have e4 : 2 * (Q : ℤ) * Q * r1 < N * q1 := lt_of_mul_lt_mul_right e3 hqpos.le
        exact_mod_cast e4
      rw [Function.iterate_succ_apply,
        show cfStep ((N, Q), (r0, r1), (s0, s1), (q0, q1)) =
          ((N, Q), (r1, r0 % r1), (s1, s0 + c * s1), (q1, q0 + c * q1)) by
            simp only [cfStep, hp, cfAdv]; rfl]
      refine ih r1 (r0 % r1) s1 (s0 + c * s1) q1 (q0 + c * q1) (-e) (by rcases he with h | h <;> simp [h])
        (by rw [i2]; ring) j1 j3 (by omega) (by omega) (Nat.mod_lt _ hr1).le hq2 ?_
      have h3 : 3 * (q0 + q1) ≤ 2 * (q1 + (q0 + c * q1)) := by omega
      have h4 : 3 ^ (f + 1) * (q0 + q1) ≤ 3 ^ f * (2 * (q1 + (q0 + c * q1))) := by
        rw [pow_succ, mul_assoc]; exact Nat.mul_le_mul_left _ h3
      have h5 : 2 ^ (f + 1) * (2 * Q) = 2 * (2 ^ f * (2 * Q)) := by rw [pow_succ]; ring
      have h6 : 3 ^ f * (2 * (q1 + (q0 + c * q1))) = 2 * (3 ^ f * (q1 + (q0 + c * q1))) := by ring
      omega

/-- **MAIN (reconstruction).** -/
theorem recon_exact (N Q A T : ℕ) (v : ℚ) (hN : 0 < N) (hA : A ≤ N) (hden : v.den ≤ Q)
    (hclose : |(A : ℚ) / N - v| < 1 / (2 * (Q : ℚ) ^ 2)) (hT : 2 ^ T * (2 * Q) < 3 ^ T) :
    recon N Q A T = v := by
  have hqpos : 0 < v.den := v.den_pos
  have hQpos : 0 < Q := lt_of_lt_of_le hqpos hden
  set ρ : ℤ := (v.den : ℤ) * A - v.num * N with hρ
  -- `2 Q² |ρ| < N q`
  have hv : v = (v.num : ℚ) / v.den := (Rat.num_div_den v).symm
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hdq : (0 : ℚ) < v.den := by exact_mod_cast hqpos
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQpos
  have hρq : (ρ : ℚ) = N * v.den * ((A : ℚ) / N - v) := by
    rw [hρ]; push_cast
    have h1 : (N : ℚ) * v.den * ((A : ℚ) / N - v) = v.den * A - N * (v * v.den) := by field_simp
    rw [h1, Rat.mul_den_eq_num]; ring
  have habs : 2 * (Q : ℚ) ^ 2 * |(ρ : ℚ)| < N * v.den := by
    rw [hρq, abs_mul, abs_of_pos (mul_pos hNq hdq)]
    have := mul_lt_mul_of_pos_left hclose (mul_pos hNq hdq)
    have h2 : (N : ℚ) * v.den * (1 / (2 * (Q : ℚ) ^ 2)) = N * v.den / (2 * (Q : ℚ) ^ 2) := by ring
    rw [h2, lt_div_iff₀ (by positivity)] at this
    linarith
  have habsZ : 2 * (Q : ℤ) * Q * |ρ| < N * v.den := by
    have : ((2 * (Q : ℤ) * Q * |ρ| : ℤ) : ℚ) < ((N * v.den : ℤ) : ℚ) := by
      push_cast; rw [show (2 : ℚ) * Q * Q = 2 * (Q : ℚ) ^ 2 by ring]; exact habs
    exact_mod_cast this
  have key := cf_iter N Q A v.num v.den |ρ| hqpos hden (le_abs_self ρ) (neg_le_abs ρ) habsZ T N A 1 0 0 1 1
    (Or.inl rfl) (by norm_num) (by norm_num) (by norm_num) le_rfl (by omega) hA hqpos
    (by simpa using hT)
  unfold recon cfInit cfOut
  set st := cfStep^[T] ((N, Q), (N, A), (1, 0), (0, 1)) with hst
  obtain ⟨hz, key⟩ := key
  have hq1 : (0 : ℚ) < (st.2.2.2.2 : ℚ) := by exact_mod_cast hz
  have keyq : (v.num : ℚ) * (st.2.2.2.2 : ℚ) = (st.2.2.1.2 : ℚ) * (v.den : ℚ) := by exact_mod_cast key
  rw [div_eq_iff hq1.ne']
  have h2 : v * (st.2.2.2.2 : ℚ) * v.den = (st.2.2.1.2 : ℚ) * v.den := by
    rw [← keyq, ← Rat.mul_den_eq_num v]; ring
  exact (mul_right_cancel₀ hdq.ne' h2).symm


end SSGValues
