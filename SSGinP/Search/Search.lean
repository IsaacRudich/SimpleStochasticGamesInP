module

public import OAI.Optimization.LinearProgramming.OracleSpec.PriceGame
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push

@[expose] public section

/-!
# SSGinP.Search.Search: deciding `θ < v k` for a cone contraction with ONE call of the anchored
one-sided sign-recovery theorem (`OracleSpec.ExtremalSignRecovery`, ported from openai_math).

Goods: `Fin (2*n+1)`; good `0` is a dummy (the anchor), good `1+j` is `up j`, good `1+n+j` is
`down j`. Prices are read relative to the dummy's price. Labels:
* up j   : `[F_j(lo) > lo_j]`,   lo_j = δ w_j (q(up j) - q 0)
* down j : `[F_j(hi) < hi_j]`,   hi_j = -δ w_j (q(down j) - q 0)
* dummy  : `[lo_k > θ]`.
If `θ + Δ ≤ v k`, the hypothesis (positive, all goods, costs `K - a_j`, `K + b_j`, `K - T`) is
consistent; if `v k ≤ θ - Δ`, the mirrored negative hypothesis is. Here `a_j = ⌊v_j/(δ w_j)⌋`,
`b_j = ⌈v_j/(δ w_j)⌉`. Only two one-sided cone bounds of `F` around `v` are used (they follow from
monotonicity plus the weighted contraction FACT W).
-/

namespace SSG28Search

open OAI.Optimization.LinearProgramming.OracleSpec

/-- A map with a weighted one-sided contraction toward `v` (monotone + FACT W give this). -/
structure Cone (n : ℕ) where
  F : (Fin n → ℚ) → (Fin n → ℚ)
  v : Fin n → ℚ
  w : Fin n → ℚ
  γ : ℚ
  hw : ∀ j, 1 ≤ w j ∧ w j ≤ 2
  hv : ∀ j, 0 ≤ v j ∧ v j ≤ 1
  hγ : 0 < γ ∧ γ ≤ 1
  lower : ∀ (x : Fin n → ℚ) (M : ℚ), 0 ≤ M → (∀ j, v j - M * w j ≤ x j) →
    ∀ i, v i - (1 - γ) * M * w i ≤ F x i
  upper : ∀ (x : Fin n → ℚ) (M : ℚ), 0 ≤ M → (∀ j, x j ≤ v j + M * w j) →
    ∀ i, F x i ≤ v i + (1 - γ) * M * w i

variable {n : ℕ}

def dummy (n : ℕ) : Fin (2*n+1) := ⟨0, by omega⟩
def upG (j : Fin n) : Fin (2*n+1) := ⟨1 + j.val, by omega⟩
def downG (j : Fin n) : Fin (2*n+1) := ⟨1 + n + j.val, by omega⟩

/-- The classification of goods. -/
theorem goods_cases (g : Fin (2*n+1)) :
    g = dummy n ∨ (∃ j : Fin n, g = upG j) ∨ (∃ j : Fin n, g = downG j) := by
  rcases g with ⟨g, hg⟩
  by_cases h0 : g = 0
  · left; subst h0; rfl
  by_cases h1 : g ≤ n
  · right; left; exact ⟨⟨g-1, by omega⟩, by simp [upG]; omega⟩
  · right; right; exact ⟨⟨g-1-n, by omega⟩, by simp [downG]; omega⟩

theorem upG_ne_dummy (j : Fin n) : upG j ≠ dummy n := by
  simp [upG, dummy, Fin.ext_iff]
theorem downG_ne_dummy (j : Fin n) : downG j ≠ dummy n := by
  simp [downG, dummy, Fin.ext_iff]
theorem upG_ne_downG (j l : Fin n) : upG j ≠ downG l := by
  simp [upG, downG, Fin.ext_iff]; omega
theorem upG_inj {j l : Fin n} (h : upG j = upG l) : j = l := by
  simp [upG, Fin.ext_iff] at h; exact Fin.ext h
theorem downG_inj {j l : Fin n} (h : downG j = downG l) : j = l := by
  simp [downG, Fin.ext_iff] at h; exact Fin.ext h

section
variable (C : Cone n) (δ θ : ℚ) (k : Fin n)

def lo (q : Fin (2*n+1) → ℚ) (j : Fin n) : ℚ := δ * C.w j * (q (upG j) - q (dummy n))
def hi (q : Fin (2*n+1) → ℚ) (j : Fin n) : ℚ := -(δ * C.w j * (q (downG j) - q (dummy n)))

open Classical in
/-- The label of good `g` at price vector `q`. -/
noncomputable def label (g : Fin (2*n+1)) (q : Fin (2*n+1) → ℚ) : Bool :=
  if g = dummy n then decide (θ < lo C δ q k)
  else if h : ∃ j, g = upG j then decide (lo C δ q h.choose < C.F (lo C δ q) h.choose)
  else if h' : ∃ j, g = downG j then decide (C.F (hi C δ q) h'.choose < hi C δ q h'.choose)
  else false

theorem label_dummy (q) : label C δ θ k (dummy n) q = decide (θ < lo C δ q k) := by
  simp [label]

theorem label_up (j : Fin n) (q) :
    label C δ θ k (upG j) q = decide (lo C δ q j < C.F (lo C δ q) j) := by
  have hne := upG_ne_dummy j
  have hex : ∃ l, upG j = upG l := ⟨j, rfl⟩
  have hc : hex.choose = j := (upG_inj hex.choose_spec).symm
  simp only [label, hne, if_false, hex, dif_pos]
  rw [hc]

theorem label_down (j : Fin n) (q) :
    label C δ θ k (downG j) q = decide (C.F (hi C δ q) j < hi C δ q j) := by
  have hne := downG_ne_dummy j
  have hnu : ¬ ∃ l, downG j = upG l := fun ⟨l, hl⟩ => upG_ne_downG l j hl.symm
  have hex : ∃ l, downG j = downG l := ⟨j, rfl⟩
  have hc : hex.choose = j := (downG_inj hex.choose_spec).symm
  simp only [label, hne, if_false, hnu, dif_neg, not_false_eq_true, hex, dif_pos]
  rw [hc]

end

/-! ### Costs -/

section
variable (C : Cone n) (δ : ℚ) (K T : ℕ)

noncomputable def a (j : Fin n) : ℕ := ⌊C.v j / (δ * C.w j)⌋₊
noncomputable def b (j : Fin n) : ℕ := ⌈C.v j / (δ * C.w j)⌉₊

open Classical in
/-- Costs of the positive hypothesis. -/
noncomputable def costPos (g : Fin (2*n+1)) : ℕ :=
  if g = dummy n then K - T
  else if h : ∃ j, g = upG j then K - a C δ h.choose
  else if h' : ∃ j, g = downG j then K + b C δ h'.choose
  else 0

open Classical in
/-- Costs of the negative hypothesis. -/
noncomputable def costNeg (g : Fin (2*n+1)) : ℕ :=
  if g = dummy n then K - T
  else if h : ∃ j, g = upG j then K + b C δ h.choose
  else if h' : ∃ j, g = downG j then K - a C δ h'.choose
  else 0

theorem costPos_dummy : costPos C δ K T (dummy n) = K - T := by simp [costPos]
theorem costNeg_dummy : costNeg C δ K T (dummy n) = K - T := by simp [costNeg]

theorem costPos_up (j : Fin n) : costPos C δ K T (upG j) = K - a C δ j := by
  have hne := upG_ne_dummy j
  have hex : ∃ l, upG j = upG l := ⟨j, rfl⟩
  have hc : hex.choose = j := (upG_inj hex.choose_spec).symm
  simp only [costPos, hne, if_false, hex, dif_pos]; rw [hc]
theorem costNeg_up (j : Fin n) : costNeg C δ K T (upG j) = K + b C δ j := by
  have hne := upG_ne_dummy j
  have hex : ∃ l, upG j = upG l := ⟨j, rfl⟩
  have hc : hex.choose = j := (upG_inj hex.choose_spec).symm
  simp only [costNeg, hne, if_false, hex, dif_pos]; rw [hc]
theorem costPos_down (j : Fin n) : costPos C δ K T (downG j) = K + b C δ j := by
  have hne := downG_ne_dummy j
  have hnu : ¬ ∃ l, downG j = upG l := fun ⟨l, hl⟩ => upG_ne_downG l j hl.symm
  have hex : ∃ l, downG j = downG l := ⟨j, rfl⟩
  have hc : hex.choose = j := (downG_inj hex.choose_spec).symm
  simp only [costPos, hne, if_false, hnu, dif_neg, not_false_eq_true, hex, dif_pos]; rw [hc]
theorem costNeg_down (j : Fin n) : costNeg C δ K T (downG j) = K - a C δ j := by
  have hne := downG_ne_dummy j
  have hnu : ¬ ∃ l, downG j = upG l := fun ⟨l, hl⟩ => upG_ne_downG l j hl.symm
  have hex : ∃ l, downG j = downG l := ⟨j, rfl⟩
  have hc : hex.choose = j := (downG_inj hex.choose_spec).symm
  simp only [costNeg, hne, if_false, hnu, dif_neg, not_false_eq_true, hex, dif_pos]; rw [hc]

end

/-! ### Rounding facts -/

section
variable (C : Cone n) {δ : ℚ} (hδ : 0 < δ)
include hδ

theorem dw_pos (j : Fin n) : 0 < δ * C.w j := mul_pos hδ (by linarith [(C.hw j).1])

theorem a_le (j : Fin n) : δ * C.w j * (a C δ j : ℚ) ≤ C.v j := by
  have h := Nat.floor_le (div_nonneg (C.hv j).1 (dw_pos C hδ j).le)
  have := mul_le_mul_of_nonneg_left h (dw_pos C hδ j).le
  rwa [mul_div_cancel₀ _ (dw_pos C hδ j).ne'] at this

theorem a_gt (j : Fin n) : C.v j < δ * C.w j * ((a C δ j : ℚ) + 1) := by
  have h := Nat.lt_floor_add_one (C.v j / (δ * C.w j))
  have := mul_lt_mul_of_pos_left h (dw_pos C hδ j)
  rwa [mul_div_cancel₀ _ (dw_pos C hδ j).ne'] at this

theorem b_ge (j : Fin n) : C.v j ≤ δ * C.w j * (b C δ j : ℚ) := by
  have h := Nat.le_ceil (C.v j / (δ * C.w j))
  have := mul_le_mul_of_nonneg_left h (dw_pos C hδ j).le
  rwa [mul_div_cancel₀ _ (dw_pos C hδ j).ne'] at this

theorem b_lt (j : Fin n) : δ * C.w j * ((b C δ j : ℚ) - 1) < C.v j := by
  have h := Nat.ceil_lt_add_one (div_nonneg (C.hv j).1 (dw_pos C hδ j).le)
  have h' : (b C δ j : ℚ) - 1 < C.v j / (δ * C.w j) := by
    unfold b; linarith
  have := mul_lt_mul_of_pos_left h' (dw_pos C hδ j)
  rwa [mul_div_cancel₀ _ (dw_pos C hδ j).ne'] at this

theorem a_le_inv (j : Fin n) : (a C δ j : ℚ) ≤ 1 / δ := by
  have h1 := a_le C hδ j
  have hw := (C.hw j).1
  have hv := (C.hv j).2
  rw [le_div_iff₀ hδ]
  have : δ * (a C δ j : ℚ) ≤ δ * C.w j * (a C δ j : ℚ) := by
    have : (0:ℚ) ≤ a C δ j := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hw (mul_nonneg hδ.le this)]
  linarith

end

/-! ### The two consistency theorems -/

section
variable (C : Cone n) {δ θ Δ : ℚ} (k : Fin n) {K T : ℕ}

/-- Parameters: `T γ ≥ 1`, `2δ(T+1) < Δ`, `T ≤ K`, `1/δ ≤ K`. -/
structure Params (C : Cone n) (δ Δ : ℚ) (K T : ℕ) : Prop where
  hδ : 0 < δ
  hT : 1 ≤ (T : ℚ) * C.γ
  hΔ : 2 * δ * ((T : ℚ) + 1) < Δ
  hTK : T ≤ K
  hK : 1 / δ ≤ (K : ℚ)

variable {C k}

theorem a_le_K (P : Params C δ Δ K T) (j : Fin n) : a C δ j ≤ K := by
  have := (a_le_inv C P.hδ j).trans P.hK
  exact_mod_cast this

/-- The key inequality: with `m ≥ T`, `γ (m+1) > 1`. -/
theorem key_gap (P : Params C δ Δ K T) {m : ℚ} (hm : (T : ℚ) ≤ m) :
    (1 - C.γ) * (m + 1) < m := by
  have hγ := C.hγ
  have : 1 ≤ m * C.γ := le_trans P.hT (mul_le_mul_of_nonneg_right hm hγ.1.le)
  nlinarith

theorem pos_consistent (P : Params C δ Δ K T) (hk : θ + Δ ≤ C.v k)
    (i : Fin (2*n+1)) (q : Fin (2*n+1) → ℚ)
    (hmin : ∀ g, adjustedCost true (costPos C δ K T) q i ≤ adjustedCost true (costPos C δ K T) q g) :
    label C δ θ k i q = true := by
  have hδ := P.hδ
  simp only [adjustedCost, if_true] at hmin
  have hTK := P.hTK
  have cd : ((costPos C δ K T (dummy n) : ℕ) : ℚ) = (K : ℚ) - T := by
    rw [costPos_dummy]; push_cast [hTK]; ring
  have cu : ∀ j, ((costPos C δ K T (upG j) : ℕ) : ℚ) = (K : ℚ) - a C δ j := by
    intro j; rw [costPos_up]; push_cast [a_le_K P j]; ring
  have cdn : ∀ j, ((costPos C δ K T (downG j) : ℕ) : ℚ) = (K : ℚ) + b C δ j := by
    intro j; rw [costPos_down]; push_cast; ring
  rcases goods_cases i with rfl | ⟨l, rfl⟩ | ⟨l, rfl⟩
  · -- dummy minimiser: compare with up k
    rw [label_dummy]
    have h := hmin (upG k)
    rw [cd, cu] at h
    have hlo : δ * C.w k * ((a C δ k : ℚ) - T) ≤ lo C δ q k := by
      unfold lo; apply mul_le_mul_of_nonneg_left _ (dw_pos C hδ k).le; linarith
    have h1 := a_gt C hδ k
    have hw := C.hw k
    have : C.v k - δ * C.w k * ((T : ℚ) + 1) ≤ lo C δ q k := by nlinarith
    have : δ * C.w k * ((T : ℚ) + 1) ≤ 2 * δ * ((T : ℚ) + 1) := by
      have : (0:ℚ) ≤ T + 1 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hw.2 (mul_nonneg hδ.le this)]
    have := P.hΔ
    simp only [decide_eq_true_eq]; linarith
  · -- up l minimiser
    rw [label_up]
    have hd := hmin (dummy n)
    rw [cd, cu] at hd
    set m : ℚ := (a C δ l : ℚ) - (q (upG l) - q (dummy n)) with hm
    have hmT : (T : ℚ) ≤ m := by rw [hm]; linarith
    have hm0 : (0 : ℚ) ≤ m + 1 := by have : (0:ℚ) ≤ T := Nat.cast_nonneg _; linarith
    have hlow : ∀ j, C.v j - δ * (m + 1) * C.w j ≤ lo C δ q j := by
      intro j
      have h := hmin (upG j)
      rw [cu, cu] at h
      have h1 := a_gt C hδ j
      have : δ * C.w j * ((a C δ j : ℚ) - m) ≤ lo C δ q j := by
        unfold lo; apply mul_le_mul_of_nonneg_left _ (dw_pos C hδ j).le; rw [hm]; linarith
      nlinarith
    have hF := C.lower (lo C δ q) (δ * (m + 1)) (mul_nonneg hδ.le hm0) hlow l
    have hli : lo C δ q l ≤ C.v l - δ * m * C.w l := by
      have h2 := a_le C hδ l
      have : lo C δ q l = δ * C.w l * ((a C δ l : ℚ) - m) := by unfold lo; rw [hm]; ring
      rw [this]; nlinarith
    have hg := key_gap P hmT
    have hw := (C.hw l).1
    have : (1 - C.γ) * (δ * (m + 1)) * C.w l < δ * m * C.w l := by
      have h3 : 0 < δ * C.w l := dw_pos C hδ l
      have := mul_lt_mul_of_pos_left hg h3
      nlinarith
    simp only [decide_eq_true_eq]; linarith
  · -- down l minimiser
    rw [label_down]
    have hd := hmin (dummy n)
    rw [cd, cdn] at hd
    set m : ℚ := -(b C δ l : ℚ) - (q (downG l) - q (dummy n)) with hm
    have hmT : (T : ℚ) ≤ m := by rw [hm]; linarith
    have hm0 : (0 : ℚ) ≤ m + 1 := by have : (0:ℚ) ≤ T := Nat.cast_nonneg _; linarith
    have hup : ∀ j, hi C δ q j ≤ C.v j + δ * (m + 1) * C.w j := by
      intro j
      have h := hmin (downG j)
      rw [cdn, cdn] at h
      have h1 := b_lt C hδ j
      have : hi C δ q j ≤ δ * C.w j * ((b C δ j : ℚ) + m) := by
        unfold hi
        have : -(q (downG j) - q (dummy n)) ≤ (b C δ j : ℚ) + m := by rw [hm]; linarith
        nlinarith [dw_pos C hδ j]
      nlinarith
    have hF := C.upper (hi C δ q) (δ * (m + 1)) (mul_nonneg hδ.le hm0) hup l
    have hli : C.v l + δ * m * C.w l ≤ hi C δ q l := by
      have h2 := b_ge C hδ l
      have : hi C δ q l = δ * C.w l * ((b C δ l : ℚ) + m) := by unfold hi; rw [hm]; ring
      rw [this]; nlinarith
    have hg := key_gap P hmT
    have : (1 - C.γ) * (δ * (m + 1)) * C.w l < δ * m * C.w l := by
      have h3 : 0 < δ * C.w l := dw_pos C hδ l
      have := mul_lt_mul_of_pos_left hg h3
      nlinarith
    simp only [decide_eq_true_eq]; linarith

theorem neg_consistent (P : Params C δ Δ K T) (hk : C.v k ≤ θ - Δ)
    (i : Fin (2*n+1)) (q : Fin (2*n+1) → ℚ)
    (hmin : ∀ g, adjustedCost false (costNeg C δ K T) q i ≤ adjustedCost false (costNeg C δ K T) q g) :
    label C δ θ k i q = false := by
  have hδ := P.hδ
  simp only [adjustedCost, Bool.false_eq_true, if_false] at hmin
  have hTK := P.hTK
  have cd : ((costNeg C δ K T (dummy n) : ℕ) : ℚ) = (K : ℚ) - T := by
    rw [costNeg_dummy]; push_cast [hTK]; ring
  have cu : ∀ j, ((costNeg C δ K T (upG j) : ℕ) : ℚ) = (K : ℚ) + b C δ j := by
    intro j; rw [costNeg_up]; push_cast; ring
  have cdn : ∀ j, ((costNeg C δ K T (downG j) : ℕ) : ℚ) = (K : ℚ) - a C δ j := by
    intro j; rw [costNeg_down]; push_cast [a_le_K P j]; ring
  rcases goods_cases i with rfl | ⟨l, rfl⟩ | ⟨l, rfl⟩
  · rw [label_dummy]
    have h := hmin (upG k)
    rw [cd, cu] at h
    have hlo : lo C δ q k ≤ δ * C.w k * ((b C δ k : ℚ) + T) := by
      unfold lo; apply mul_le_mul_of_nonneg_left _ (dw_pos C hδ k).le; linarith
    have h1 := b_lt C hδ k
    have hw := C.hw k
    have : lo C δ q k ≤ C.v k + δ * C.w k * ((T : ℚ) + 1) := by nlinarith
    have : δ * C.w k * ((T : ℚ) + 1) ≤ 2 * δ * ((T : ℚ) + 1) := by
      have : (0:ℚ) ≤ T + 1 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hw.2 (mul_nonneg hδ.le this)]
    have := P.hΔ
    simp only [decide_eq_false_iff_not, not_lt]; linarith
  · rw [label_up]
    have hd := hmin (dummy n)
    rw [cd, cu] at hd
    set m : ℚ := (q (upG l) - q (dummy n)) - (b C δ l : ℚ) with hm
    have hmT : (T : ℚ) ≤ m := by rw [hm]; linarith
    have hm0 : (0 : ℚ) ≤ m + 1 := by have : (0:ℚ) ≤ T := Nat.cast_nonneg _; linarith
    have hup : ∀ j, lo C δ q j ≤ C.v j + δ * (m + 1) * C.w j := by
      intro j
      have h := hmin (upG j)
      rw [cu, cu] at h
      have h1 := b_lt C hδ j
      have : lo C δ q j ≤ δ * C.w j * ((b C δ j : ℚ) + m) := by
        unfold lo; apply mul_le_mul_of_nonneg_left _ (dw_pos C hδ j).le; rw [hm]; linarith
      nlinarith
    have hF := C.upper (lo C δ q) (δ * (m + 1)) (mul_nonneg hδ.le hm0) hup l
    have hli : C.v l + δ * m * C.w l ≤ lo C δ q l := by
      have h2 := b_ge C hδ l
      have : lo C δ q l = δ * C.w l * ((b C δ l : ℚ) + m) := by unfold lo; rw [hm]; ring
      rw [this]; nlinarith
    have hg := key_gap P hmT
    have : (1 - C.γ) * (δ * (m + 1)) * C.w l < δ * m * C.w l := by
      have h3 : 0 < δ * C.w l := dw_pos C hδ l
      have := mul_lt_mul_of_pos_left hg h3
      nlinarith
    simp only [decide_eq_false_iff_not, not_lt]; linarith
  · rw [label_down]
    have hd := hmin (dummy n)
    rw [cd, cdn] at hd
    set m : ℚ := (q (downG l) - q (dummy n)) + (a C δ l : ℚ) with hm
    have hmT : (T : ℚ) ≤ m := by rw [hm]; linarith
    have hm0 : (0 : ℚ) ≤ m + 1 := by have : (0:ℚ) ≤ T := Nat.cast_nonneg _; linarith
    have hlow : ∀ j, C.v j - δ * (m + 1) * C.w j ≤ hi C δ q j := by
      intro j
      have h := hmin (downG j)
      rw [cdn, cdn] at h
      have h1 := a_gt C hδ j
      have : δ * C.w j * ((a C δ j : ℚ) - m) ≤ hi C δ q j := by
        unfold hi
        have : (a C δ j : ℚ) - m ≤ -(q (downG j) - q (dummy n)) := by rw [hm]; linarith
        nlinarith [dw_pos C hδ j]
      nlinarith
    have hF := C.lower (hi C δ q) (δ * (m + 1)) (mul_nonneg hδ.le hm0) hlow l
    have hli : hi C δ q l ≤ C.v l - δ * m * C.w l := by
      have h2 := a_le C hδ l
      have : hi C δ q l = δ * C.w l * ((a C δ l : ℚ) - m) := by unfold hi; rw [hm]; ring
      rw [this]; nlinarith
    have hg := key_gap P hmT
    have : (1 - C.γ) * (δ * (m + 1)) * C.w l < δ * m * C.w l := by
      have h3 : 0 < δ * C.w l := dw_pos C hδ l
      have := mul_lt_mul_of_pos_left hg h3
      nlinarith
    simp only [decide_eq_false_iff_not, not_lt]; linarith

end

section
variable {C : Cone n} {δ θ Δ : ℚ} {k : Fin n} {K T : ℕ}

theorem b_le_K (P : Params C δ Δ K T) (j : Fin n) : b C δ j ≤ K := by
  unfold b
  apply Nat.ceil_le.mpr
  have hδ := P.hδ
  have hw := (C.hw j).1
  have hv := (C.hv j).2
  have h1 : C.v j / (δ * C.w j) ≤ 1 / δ := by
    rw [div_le_div_iff₀ (dw_pos C hδ j) hδ]
    nlinarith [mul_le_mul_of_nonneg_left hw hδ.le]
  exact h1.trans P.hK

theorem costPos_le (P : Params C δ Δ K T) (g : Fin (2*n+1)) : costPos C δ K T g ≤ 2 * K := by
  rcases goods_cases g with rfl | ⟨l, rfl⟩ | ⟨l, rfl⟩
  · rw [costPos_dummy]; omega
  · rw [costPos_up]; omega
  · rw [costPos_down]; have := b_le_K P l; omega

theorem costNeg_le (P : Params C δ Δ K T) (g : Fin (2*n+1)) : costNeg C δ K T g ≤ 2 * K := by
  rcases goods_cases g with rfl | ⟨l, rfl⟩ | ⟨l, rfl⟩
  · rw [costNeg_dummy]; omega
  · rw [costNeg_up]; have := b_le_K P l; omega
  · rw [costNeg_down]; omega

end

end SSG28Search
