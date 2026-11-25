module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# SSGinP.Machine.MachineBound: polynomial bounds of the form `(x+2)^k`
-/

namespace SSG28MachineBound

theorem le_pow_self (c x : ℕ) : c ≤ (x + 2) ^ c :=
  le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_left (by omega) c)

theorem pow_mono {x a b : ℕ} (h : a ≤ b) : (x + 2) ^ a ≤ (x + 2) ^ b :=
  Nat.pow_le_pow_right (by omega) h

theorem one_le_pow (x a : ℕ) : 1 ≤ (x + 2) ^ a := Nat.one_le_pow _ _ (by omega)

theorem add_pow_le (x a b : ℕ) : (x + 2) ^ a + (x + 2) ^ b ≤ (x + 2) ^ (max a b + 1) := by
  have h1 := pow_mono (x := x) (le_max_left a b)
  have h2 := pow_mono (x := x) (le_max_right a b)
  have : (x + 2) ^ (max a b + 1) = (x + 2) ^ max a b * (x + 2) := pow_succ _ _
  rw [this]
  have h3 : (x + 2) ^ max a b * (x + 2) = (x + 2) ^ max a b * x + 2 * (x + 2) ^ max a b := by ring
  rw [h3]; omega

/-- a polynomial with natural coefficients is bounded by a power of `x + 2`. -/
theorem poly_le (p : Polynomial ℕ) : ∃ k, ∀ x, p.eval x ≤ (x + 2) ^ k := by
  refine ⟨(Finset.range (p.natDegree + 1)).sum (fun i => p.coeff i) + p.natDegree, fun x => ?_⟩
  rw [Polynomial.eval_eq_sum_range]
  set S := (Finset.range (p.natDegree + 1)).sum (fun i => p.coeff i)
  have h1 : ∀ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i ≤ p.coeff i * (x + 2) ^ p.natDegree := by
    intro i hi
    apply Nat.mul_le_mul_left
    calc x ^ i ≤ (x + 2) ^ i := Nat.pow_le_pow_left (by omega) i
      _ ≤ (x + 2) ^ p.natDegree := pow_mono (by simp at hi; omega)
  calc (Finset.range (p.natDegree + 1)).sum (fun i => p.coeff i * x ^ i)
      ≤ (Finset.range (p.natDegree + 1)).sum (fun i => p.coeff i * (x + 2) ^ p.natDegree) := Finset.sum_le_sum h1
    _ = S * (x + 2) ^ p.natDegree := by rw [Finset.sum_mul]
    _ ≤ (x + 2) ^ S * (x + 2) ^ p.natDegree := Nat.mul_le_mul_right _ (le_pow_self S x)
    _ = (x + 2) ^ (S + p.natDegree) := (pow_add _ _ _).symm

/-- composition: if `y ≤ (x+2)^a` then `(y+2)^b ≤ (x+2)^((a+2)*b)`. -/
theorem comp_le {x y a b : ℕ} (h : y ≤ (x + 2) ^ a) : (y + 2) ^ b ≤ (x + 2) ^ ((a + 2) * b) := by
  have h2 : y + 2 ≤ (x + 2) ^ (a + 2) := by
    have e : (x + 2) ^ (a + 2) = (x + 2) ^ a * ((x + 2) * (x + 2)) := by ring
    rw [e]
    have := one_le_pow x a
    have h4 : (x + 2) ^ a * ((x + 2) * (x + 2)) = (x + 2) ^ a * (x * x + 4 * x) + 4 * (x + 2) ^ a := by ring
    rw [h4]; omega
  calc (y + 2) ^ b ≤ ((x + 2) ^ (a + 2)) ^ b := Nat.pow_le_pow_left h2 b
    _ = (x + 2) ^ ((a + 2) * b) := (pow_mul _ _ _).symm

end SSG28MachineBound
