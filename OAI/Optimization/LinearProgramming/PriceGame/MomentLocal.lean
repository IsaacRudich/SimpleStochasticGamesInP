-- Ported verbatim (modulo toolchain fixes) from the openai_math repository, Apache-2.0. See LICENSE, NOTICE, PORTED_FILES.md.
module

public import OAI.PortCompat
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Push

@[expose] public section

open scoped BigOperators

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Moment

/-- Gain on allocated coordinates. Mass on the outside option contributes zero. -/
def allocationGain {E I : Type*} [Fintype I] (f : E → I → ℝ)
    (u : E → ℝ) (z : I → ℝ) (e : E) : ℝ := ∑ i, f e i * u e * z i

theorem allocationGain_abs_le_one {E I : Type*} [Fintype I] {f : E → I → ℝ}
    {u : E → ℝ} {z : I → ℝ} (e : E) (hf : ∀ i, 0 ≤ f e i) (hu : |u e| = 1)
    (hz : ∀ i, |z i| = 1) (hmass : ∑ i, f e i ≤ 1) :
    |allocationGain f u z e| ≤ 1 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  simpa [abs_mul, abs_of_nonneg (hf _), hu, hz] using hmass

theorem allocationGain_balanced {E I : Type*} [Fintype E] [Fintype I]
    (L : E → ℝ) (f : E → I → ℝ) (u : E → ℝ) (z : I → ℝ)
    (hbal : ∀ i, ∑ e, L e * u e * f e i = 0) :
    ∑ e, L e * allocationGain f u z e = 0 := by
  simp only [allocationGain, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  calc
    ∑ e, L e * (f e i * u e * z i) = (∑ e, L e * u e * f e i) * z i := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ = 0 := by rw [hbal i, zero_mul]

/-- Weight immediately before probe `r`, numbering probes from zero. -/
def localWeight {E : Type*} (η : ℝ) (initial : E → ℝ) (gain : ℕ → E → ℝ)
    (r : ℕ) (e : E) : ℝ := initial e * ∏ t ∈ Finset.range r, (1 + η * gain t e)

@[simp] theorem localWeight_zero {E : Type*} (η : ℝ) (initial : E → ℝ)
    (gain : ℕ → E → ℝ) (e : E) : localWeight η initial gain 0 e = initial e := by
  simp [localWeight]

@[simp] theorem localWeight_succ {E : Type*} (η : ℝ) (initial : E → ℝ)
    (gain : ℕ → E → ℝ) (r : ℕ) (e : E) :
    localWeight η initial gain (r + 1) e = localWeight η initial gain r e * (1 + η * gain r e) := by
  simp [localWeight, Finset.prod_range_succ, mul_assoc]

theorem localWeight_sum_eq {E : Type*} [Fintype E] (η : ℝ) (initial : E → ℝ)
    (gain : ℕ → E → ℝ) (r : ℕ)
    (hbal : ∀ t < r, ∑ e, localWeight η initial gain t e * gain t e = 0) :
    ∑ e, localWeight η initial gain r e = ∑ e, initial e := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hprev := ih fun t ht ↦ hbal t (Nat.lt_trans ht (Nat.lt_succ_self _))
    calc
      ∑ e, localWeight η initial gain (r + 1) e =
          ∑ e, (localWeight η initial gain r e + η * (localWeight η initial gain r e * gain r e)) :=
        Finset.sum_congr rfl fun _ _ ↦ by rw [localWeight_succ]; ring
      _ = ∑ e, initial e := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hbal r (Nat.lt_succ_self r), hprev]
        ring

/-- The lower Taylor estimate for the logarithm on the half-unit interval. -/
theorem sub_sq_le_log_one_add (x : ℝ) (hx : |x| ≤ 1 / 2) :
    x - x ^ 2 ≤ Real.log (1 + x) := by
  -- PORT NOTE (D2): the original proof used Complex.norm_log_one_add_sub_self_le
  -- (Mathlib.Analysis.SpecialFunctions.Complex.LogBounds); replaced by a real-only proof
  -- to avoid building that part of Mathlib. Statement unchanged.
  have h1 := (abs_le.mp hx).1
  have h2 := (abs_le.mp hx).2
  have hpos : 0 < 1 + x := by linarith
  rw [Real.le_log_iff_exp_le hpos]
  rcases le_or_gt 0 x with hx0 | hx0
  · -- x ≥ 0: use 1 - 1/(1+x) ≤ log (1+x)
    have hl := Real.one_sub_inv_le_log_of_pos hpos
    have hb : x - x ^ 2 ≤ 1 - (1 + x)⁻¹ := by
      rw [show 1 - (1 + x)⁻¹ = x / (1 + x) by field_simp; ring]
      rw [le_div_iff₀ hpos]
      nlinarith [pow_nonneg hx0 3]
    have := le_trans hb hl
    exact (Real.le_log_iff_exp_le hpos).mp this
  · -- x < 0: exp (x - x^2) = (exp (x^2 - x))⁻¹ ≤ (1 + z + z^2/2)⁻¹ ≤ 1 + x
    have hzpos : 0 ≤ x ^ 2 - x := by nlinarith
    have hq := Real.quadratic_le_exp_of_nonneg hzpos
    have hqpos : 0 < 1 + (x ^ 2 - x) + (x ^ 2 - x) ^ 2 / 2 := by positivity
    have hexp : Real.exp (x - x ^ 2) = (Real.exp (x ^ 2 - x))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [hexp]
    calc (Real.exp (x ^ 2 - x))⁻¹ ≤ (1 + (x ^ 2 - x) + (x ^ 2 - x) ^ 2 / 2)⁻¹ :=
          inv_anti₀ hqpos hq
      _ ≤ 1 + x := by
          rw [inv_le_iff_one_le_mul₀ hqpos]
          have ht : 0 < -x := by linarith
          have ht2 : -x ≤ 1 / 2 := by linarith
          nlinarith [mul_pos ht ht, mul_pos (mul_pos ht ht) ht, mul_pos (mul_pos ht ht) (mul_pos ht ht)]

theorem exp_gain_sub_sq_le_update {η g : ℝ} (hη : 0 ≤ η) (hη' : η ≤ 1 / 2)
    (hg : |g| ≤ 1) : Real.exp (η * g - η ^ 2) ≤ 1 + η * g := by
  have habs : |η * g| ≤ η := by
    rw [abs_mul, abs_of_nonneg hη]
    simpa using mul_le_mul_of_nonneg_left hg hη
  have hsq : (η * g) ^ 2 ≤ η ^ 2 := by
    simpa only [sq_abs] using (pow_le_pow_left₀ (abs_nonneg (η * g)) habs 2)
  have hlog := sub_sq_le_log_one_add _ (habs.trans hη')
  have hpos : 0 < 1 + η * g := by linarith [(abs_le.mp (habs.trans hη')).1]
  exact (Real.exp_le_exp.mpr (by linarith : η * g - η ^ 2 ≤ Real.log (1 + η * g))).trans_eq
    (Real.exp_log hpos)

theorem local_exponential_estimate {E : Type*} [Fintype E]
    (η : ℝ) (initial : E → ℝ) (gain : ℕ → E → ℝ) (r : ℕ)
    (hinit : ∀ e, 0 ≤ initial e) (hη : 0 ≤ η) (hη' : η ≤ 1 / 2)
    (hg : ∀ t < r, ∀ e, |gain t e| ≤ 1)
    (hbal : ∀ t < r, ∑ e, localWeight η initial gain t e * gain t e = 0) :
    (∑ e, initial e * Real.exp (η * ∑ t ∈ Finset.range r, gain t e)) ≤
      Real.exp (η ^ 2 * r) * ∑ e, initial e := by
  have hpoint (e : E) :
      Real.exp (η * ∑ t ∈ Finset.range r, gain t e - η ^ 2 * r) ≤
        ∏ t ∈ Finset.range r, (1 + η * gain t e) := by
    calc
      _ = ∏ t ∈ Finset.range r, Real.exp (η * gain t e - η ^ 2) := by
        rw [← Real.exp_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp [mul_comm]
      _ ≤ _ := Finset.prod_le_prod₀ (fun t _ ↦ (Real.exp_pos _).le)
        (fun t ht ↦ exp_gain_sub_sq_le_update hη hη' (hg t (Finset.mem_range.mp ht) e))
  rw [← localWeight_sum_eq η initial gain r hbal, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have hs :
      Real.exp (η * ∑ t ∈ Finset.range r, gain t e) =
        Real.exp (η ^ 2 * r) * Real.exp (η * ∑ t ∈ Finset.range r, gain t e - η ^ 2 * r) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hs, localWeight, mul_left_comm (initial e)]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hpoint e) (hinit e))
    (Real.exp_pos _).le

end Moment
end PriceGame
end LinearProgramming
end Optimization
end OAI
