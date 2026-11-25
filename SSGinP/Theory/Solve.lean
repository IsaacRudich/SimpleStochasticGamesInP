module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# SSGinP.Theory.Solve: Gauss–Jordan elimination over ℚ, verified

`gj A b : Option (Fin n → ℚ)`: column by column, find the first row `≥ k` with a nonzero entry in column `k`, swap
it into place, normalise, eliminate the column from all other rows.

* `gj_sound`    : if `gj A b = some y` then `y` is the unique solution of `A y = b`.
* `gj_complete` : if `A y = 0` only for `y = 0`, then `gj A b` returns some `y` (hence the solution).
Operation count: `n` pivot steps, each `O(n^2)` field operations on ℚ (bit sizes of the intermediate rationals are
polynomial by Edmonds' theorem; not formalised here).
-/

namespace SSG

open Finset

variable {n : ℕ}

abbrev Mat (n : ℕ) := Fin n → Fin n → ℚ
abbrev Vec (n : ℕ) := Fin n → ℚ

theorem mul_sum' {ι : Type*} (s : Finset ι) (c : ℚ) (f : ι → ℚ) : c * ∑ j ∈ s, f j = ∑ j ∈ s, c * f j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, mul_add, ih]

/-- homogenised solution set: `A y = t b`. -/
def HSol (A : Mat n) (b : Vec n) (t : ℚ) (y : Vec n) : Prop := ∀ i, ∑ j, A i j * y j = t * b i

/-- the transposition of rows `k`, `p`. -/
def sw (k p : Fin n) (i : Fin n) : Fin n := if i = k then p else if i = p then k else i

theorem sw_sw (k p i : Fin n) : sw k p (sw k p i) = i := by
  unfold sw
  by_cases h1 : i = k
  · subst h1; by_cases h2 : p = i <;> simp [h2]
  · by_cases h2 : i = p
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem hsol_sw (A : Mat n) (b : Vec n) (t : ℚ) (y : Vec n) (k p : Fin n) :
    HSol (fun i => A (sw k p i)) (fun i => b (sw k p i)) t y ↔ HSol A b t y := by
  constructor
  · intro h i; have := h (sw k p i); simp only [sw_sw] at this; exact this
  · intro h i; exact h (sw k p i)

/-- one elimination step at column `k` with pivot row `k` (after the swap), pivot value `c = P k k`. -/
def elimA (P : Mat n) (k : Fin n) : Mat n := fun i j =>
  if i = k then P k j / P k k else P i j - P i k * (P k j / P k k)
def elimB (P : Mat n) (b : Vec n) (k : Fin n) : Vec n := fun i =>
  if i = k then b k / P k k else b i - P i k * (b k / P k k)

theorem sum_comb (a p y : Vec n) (α c : ℚ) :
    ∑ j, (a j - α * (p j / c)) * y j = ∑ j, a j * y j - (α / c) * ∑ j, p j * y j := by
  rw [mul_sum', ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _; ring

theorem hsol_elim (P : Mat n) (b : Vec n) (k : Fin n) (hc : P k k ≠ 0) (t : ℚ) (y : Vec n) :
    HSol (elimA P k) (elimB P b k) t y ↔ HSol P b t y := by
  have rowk : (∑ j, elimA P k k j * y j = t * elimB P b k k) ↔ (∑ j, P k j * y j = t * b k) := by
    simp only [elimA, elimB, if_true]
    have e : ∑ j, P k j / P k k * y j = (∑ j, P k j * y j) / P k k := by
      rw [div_eq_mul_inv, mul_comm, mul_sum']; apply Finset.sum_congr rfl; intro j _; ring
    rw [e]; constructor
    · intro h; field_simp at h; linarith
    · intro h; rw [h]; field_simp
  have rowi : ∀ i, i ≠ k → (∑ j, P k j * y j = t * b k) →
      ((∑ j, elimA P k i j * y j = t * elimB P b k i) ↔ (∑ j, P i j * y j = t * b i)) := by
    intro i hi hk
    simp only [elimA, elimB, hi, if_false]
    rw [sum_comb (P i) (P k) y (P i k) (P k k), hk]
    generalize (∑ j, P i j * y j) = S
    constructor
    · intro h
      have h2 : (S - t * b i) * P k k = 0 := by
        field_simp at h; ring_nf; ring_nf at h; linarith
      rcases mul_eq_zero.mp h2 with h3 | h3
      · linarith
      · exact absurd h3 hc
    · intro h; rw [h]; field_simp
  constructor
  · intro h
    have hk := rowk.mp (h k)
    intro i
    by_cases hi : i = k
    · subst hi; exact hk
    · exact (rowi i hi hk).mp (h i)
  · intro h
    have hk := h k
    intro i
    by_cases hi : i = k
    · subst hi; exact rowk.mpr hk
    · exact (rowi i hi hk).mpr (h i)

/-- invariant: columns `< k` are unit vectors (`A i j = [i = j]`). -/
def Inv (k : ℕ) (A : Mat n) : Prop := ∀ j : Fin n, j.val < k → ∀ i, A i j = if i = j then 1 else 0

/-- pivot search: first row `p` with `k ≤ p` and `A p k ≠ 0`. -/
def pivot (A : Mat n) (k : Fin n) : Option (Fin n) :=
  (List.finRange n).find? (fun i => decide (k.val ≤ i.val ∧ A i k ≠ 0))

theorem pivot_some {A : Mat n} {k p : Fin n} (h : pivot A k = some p) : k.val ≤ p.val ∧ A p k ≠ 0 := by
  have := List.find?_some h; simpa using this

theorem pivot_none {A : Mat n} {k : Fin n} (h : pivot A k = none) : ∀ i : Fin n, k.val ≤ i.val → A i k = 0 := by
  intro i hi
  have := List.find?_eq_none.mp h i (List.mem_finRange i)
  simp only [decide_eq_true_eq, not_and, not_not] at this
  exact this hi

/-- the swapped matrix. -/
def swA (A : Mat n) (k p : Fin n) : Mat n := fun i => A (sw k p i)
def swB (b : Vec n) (k p : Fin n) : Vec n := fun i => b (sw k p i)

theorem inv_step (A : Mat n) (k p : Fin n) (hA : Inv k.val A) (hp : k.val ≤ p.val) (hc : A p k ≠ 0) :
    Inv (k.val + 1) (elimA (swA A k p) k) ∧ (swA A k p) k k ≠ 0 := by
  have hP : (swA A k p) k k = A p k := by simp [swA, sw]
  refine ⟨?_, by rw [hP]; exact hc⟩
  -- columns `j < k` of the swapped matrix are still unit vectors
  have col : ∀ j : Fin n, j.val < k.val → ∀ i, swA A k p i j = if i = j then 1 else 0 := by
    intro j hj i
    simp only [swA]
    rw [hA j hj]
    have hjk : j ≠ k := fun e => by rw [e] at hj; omega
    have hjp : j ≠ p := fun e => by rw [e] at hj; omega
    have fix : sw k p j = j := by simp [sw, hjk, hjp]
    have iff : sw k p i = j ↔ i = j := by
      constructor
      · intro e; rw [← sw_sw k p i, e, fix]
      · intro e; rw [e, fix]
    exact if_congr iff rfl rfl
  intro j hj i
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
  · have hjk : j ≠ k := fun e => by rw [e] at hj; omega
    simp only [elimA]
    rw [col j hj k]
    by_cases hi : i = k
    · subst hi; simp [Ne.symm hjk]
    · simp only [hi, if_false, if_neg (Ne.symm hjk)]; rw [col j hj i]; simp
  · have hjk : j = k := Fin.ext hj
    subst hjk
    simp only [elimA]
    rw [hP]
    by_cases hi : i = j
    · subst hi; simp [hc]
    · simp only [hi, if_false]; field_simp; ring

/-- Gauss–Jordan from column `k` on. -/
def gjAux (A : Mat n) (b : Vec n) (k : ℕ) : Option (Vec n) :=
  if h : k < n then
    match pivot A ⟨k, h⟩ with
    | none => none
    | some p => gjAux (elimA (swA A ⟨k, h⟩ p) ⟨k, h⟩) (elimB (swA A ⟨k, h⟩ p) (swB b ⟨k, h⟩ p) ⟨k, h⟩) (k + 1)
  else some b
termination_by n - k

/-- **Gauss–Jordan elimination.** -/
def gj (A : Mat n) (b : Vec n) : Option (Vec n) := gjAux A b 0

theorem hsol_step (A : Mat n) (b : Vec n) (k p : Fin n) (hc : (swA A k p) k k ≠ 0) (t : ℚ) (y : Vec n) :
    HSol (elimA (swA A k p) k) (elimB (swA A k p) (swB b k p) k) t y ↔ HSol A b t y := by
  rw [hsol_elim _ _ k hc]
  exact hsol_sw A b t y k p

theorem gjAux_sound : ∀ (d k : ℕ) (A : Mat n) (b : Vec n), n - k = d → Inv k A → ∀ y, gjAux A b k = some y →
    ∀ z, HSol A b 1 z ↔ z = y := by
  intro d
  induction d with
  | zero =>
    intro k A b hd hI y hy z
    have hk : ¬ k < n := by omega
    rw [gjAux, dif_neg hk] at hy
    cases hy
    constructor
    · intro h; funext i
      have := h i
      have e : ∑ j, A i j * z j = z i := by
        rw [Finset.sum_eq_single i]
        · rw [hI i (by omega) i]; simp
        · intro j _ hj; rw [hI j (by omega) i]; simp [Ne.symm hj]
        · simp
      rw [e] at this; linarith
    · intro e i; subst e
      rw [Finset.sum_eq_single i]
      · rw [hI i (by omega) i]; simp
      · intro j _ hj; rw [hI j (by omega) i]; simp [Ne.symm hj]
      · simp
  | succ d ih =>
    intro k A b hd hI y hy z
    have hk : k < n := by omega
    rw [gjAux, dif_pos hk] at hy
    split at hy
    · cases hy
    · rename_i p hp
      obtain ⟨hle, hc⟩ := pivot_some hp
      obtain ⟨hI', hc'⟩ := inv_step A ⟨k, hk⟩ p hI hle hc
      rw [← hsol_step A b ⟨k, hk⟩ p hc' 1 z]
      exact ih (k + 1) _ _ (by omega) hI' y hy z

theorem gjAux_complete : ∀ (d k : ℕ) (A : Mat n) (b : Vec n), n - k = d → Inv k A →
    (∀ y, HSol A b 0 y → y = 0) → ∃ y, gjAux A b k = some y := by
  intro d
  induction d with
  | zero =>
    intro k A b hd _ _
    have hk : ¬ k < n := by omega
    rw [gjAux, dif_neg hk]; exact ⟨b, rfl⟩
  | succ d ih =>
    intro k A b hd hI hinj
    have hk : k < n := by omega
    rw [gjAux, dif_pos hk]
    split
    · -- stuck: build a kernel vector
      rename_i hp
      exfalso
      have hz := pivot_none hp
      let K : Fin n := ⟨k, hk⟩
      let y : Vec n := fun l => if l = K then 1 else if l.val < k then -A l K else 0
      have hy : HSol A b 0 y := by
        intro i
        have term : ∀ l, A i l * y l = (if l = K then A i K else 0) + (if l = i ∧ i.val < k then -A i K else 0) := by
          intro l
          simp only [y]
          by_cases h1 : l = K
          · subst h1
            have : ¬ (K = i ∧ i.val < k) := fun ⟨e, hlt⟩ => by rw [← e] at hlt; simp [K] at hlt
            simp [this]
          · by_cases h2 : l.val < k
            · rw [hI l h2 i]
              by_cases h3 : i = l
              · subst h3; simp [h1, h2]
              · simp [h1, h2, h3, Ne.symm h3]
            · have : ¬ (l = i ∧ i.val < k) := fun ⟨e, hlt⟩ => by rw [e] at h2; exact h2 hlt
              simp [h1, h2, this]
        rw [Finset.sum_congr rfl (fun l _ => term l), Finset.sum_add_distrib]
        rw [Finset.sum_ite_eq' Finset.univ K]
        simp only [Finset.mem_univ, if_true, zero_mul]
        by_cases hik : i.val < k
        · simp only [hik, and_true]
          rw [Finset.sum_ite_eq' Finset.univ i]; simp
        · simp only [hik, and_false, if_false, Finset.sum_const_zero, add_zero]
          exact hz i (by simp [K]; omega)
      have h0 := hinj y hy
      have := congrFun h0 K
      simp [y] at this
    · rename_i p hp
      obtain ⟨hle, hc⟩ := pivot_some hp
      obtain ⟨hI', hc'⟩ := inv_step A ⟨k, hk⟩ p hI hle hc
      apply ih (k + 1) _ _ (by omega) hI'
      intro y hy
      exact hinj y ((hsol_step A b ⟨k, hk⟩ p hc' 0 y).mp hy)

theorem inv_zero (A : Mat n) : Inv 0 A := fun j hj => absurd hj (Nat.not_lt_zero _)

/-- **soundness**: the output is the unique solution of `A y = b`. -/
theorem gj_sound (A : Mat n) (b : Vec n) (y : Vec n) (h : gj A b = some y) : ∀ z, HSol A b 1 z ↔ z = y :=
  gjAux_sound (n - 0) 0 A b rfl (inv_zero A) y h

/-- **completeness**: if `A` is injective, Gauss–Jordan succeeds. -/
theorem gj_complete (A : Mat n) (b : Vec n) (hinj : ∀ y, HSol A b 0 y → y = 0) : ∃ y, gj A b = some y :=
  gjAux_complete (n - 0) 0 A b rfl (inv_zero A) hinj

end SSG
