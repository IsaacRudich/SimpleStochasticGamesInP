module

public import SSGinP.GameFacts
public import SSGinP.Theory.Solve
public import Mathlib.Data.Rat.Floor

@[expose] public section

/-!
# SSGinP.Theory.Theory: the value operator of a simple stochastic game, standalone

* `ev`, `F`            : the value operator (`F x i` = max / min / average of the children' values; terminals 0 / 1).
* `Fp`                 : the operator of the Markov chain obtained by fixing one chosen arc `π i` at every max and min node (a pair of strategies).
* `Ranked`, `cmp`      : rank certificates and the comparison principle.
* `peel`, `prank`, `peelAll`: the peeling procedure (computable): `peelAll G = true ↔ Ranked G (prank G)`-certificate.
* `fix_unique`, `fix_bounds`: uniqueness of the fixed point of `F` and `0 ≤ v ≤ 1` on ranked games.
* `fix_exists`         : existence of a rational fixed point (induction on the number of free choices; base case:
                         Gauss–Jordan on the chain system, `SSGinP.Theory.Solve`).
* `denom_bound`        : the fixed point has a common denominator `D ≤ 3^n` (pigeonhole on fractional parts).
* `contraction` (THEOREM W): the weighted max-norm contraction with weights `w i = 2 - 3^-(prank i)`, `γ = 1/(4·3^n)`.
-/

namespace SSG

open Finset

variable {n : ℕ}

/-! ## 1. value operator -/

/-- internal helper (not used in the primary definitions): the child selected by a Boolean, `false ↦ j`,
`true ↦ k`. -/
def Game.child (G : Game n) (i : Fin n) : Bool → Fin n
  | false => G.childJ i
  | true => G.childK i

/-- internal: an arc choice from a Boolean (`false ↦ j`, `true ↦ k`). -/
def ArcChoice.ofBool : Bool → ArcChoice
  | false => .j
  | true => .k

/-- internal: the Boolean of an arc choice. -/
def ArcChoice.toBool : ArcChoice → Bool
  | .j => false
  | .k => true

@[simp] theorem chosen_ofBool (G : Game n) (i : Fin n) (b : Bool) : G.chosen i (ArcChoice.ofBool b) = G.child i b := by
  cases b <;> rfl

@[simp] theorem chosen_eq_child (G : Game n) (i : Fin n) (c : ArcChoice) : G.chosen i c = G.child i c.toBool := by
  cases c <;> rfl

@[simp] theorem toBool_ofBool (b : Bool) : (ArcChoice.ofBool b).toBool = b := by cases b <;> rfl

theorem child_false (G : Game n) (i : Fin n) : G.child i false = G.childJ i := rfl
theorem child_true (G : Game n) (i : Fin n) : G.child i true = G.childK i := rfl

/-- the value of node `j` read from `x`: a terminal has its constant value. -/
def ev (G : Game n) (x : Fin n → ℚ) (j : Fin n) : ℚ :=
  match G.nodeType j with
  | .terminal0 => 0
  | .terminal1 => 1
  | _ => x j

/-- **the value operator** `F`. -/
def F (G : Game n) (x : Fin n → ℚ) : Fin n → ℚ := fun i =>
  match G.nodeType i with
  | .terminal0 => 0
  | .terminal1 => 1
  | .max => max (ev G x (G.child i false)) (ev G x (G.child i true))
  | .min => min (ev G x (G.child i false)) (ev G x (G.child i true))
  | .average => (ev G x (G.child i false) + ev G x (G.child i true)) / 2

/-- node `i` is **satisfied** by the assignment `x`: its equation holds (a max node has the max of its children's
values, a min node the min, an average node the average; terminal-0 and terminal-1 have values 0 and 1). -/
def Satisfied (G : Game n) (x : Fin n → ℚ) (i : Fin n) : Prop := x i = F G x i

/-- a **stable assignment**: every node is satisfied. -/
def Stable (G : Game n) (x : Fin n → ℚ) : Prop := ∀ i, Satisfied G x i

theorem stable_iff (G : Game n) (x : Fin n → ℚ) : Stable G x ↔ F G x = x := by
  constructor
  · intro h; funext i; exact (h i).symm
  · intro h i; exact (congrFun h i).symm

/-- the operator of `G_{σ,τ}` when `π` gives the chosen arc at every max and min node. -/
def Fp (G : Game n) (π : Fin n → Bool) (x : Fin n → ℚ) : Fin n → ℚ := fun i =>
  match G.nodeType i with
  | .terminal0 => 0
  | .terminal1 => 1
  | .max => ev G x (G.child i (π i))
  | .min => ev G x (G.child i (π i))
  | .average => (ev G x (G.child i false) + ev G x (G.child i true)) / 2

/-- difference read through `ev`: terminals contribute `0`. -/
def de (G : Game n) (d : Fin n → ℚ) (j : Fin n) : ℚ := if isTerminal G j then 0 else d j

theorem ev_sub (G : Game n) (u w : Fin n → ℚ) (j : Fin n) : ev G u j - ev G w j = de G (fun i => u i - w i) j := by
  unfold ev de isTerminal; cases G.nodeType j <;> simp

theorem ev_of_fix (G : Game n) (v : Fin n → ℚ) (hv : ∀ i, isTerminal G i = true → F G v i = v i) (j : Fin n) :
    ev G v j = v j := by
  have := hv j
  unfold ev; unfold isTerminal F at this
  cases h : G.nodeType j <;> simp [h] at this ⊢ <;> linarith

/-! ## 2. rank certificates and the comparison principle -/

/-- a rank certificate: a average node has a child of smaller rank, a max/min node has both. -/
def Ranked (G : Game n) (r : Fin n → ℕ) : Prop :=
  ∀ i, (G.nodeType i = .average → r (G.child i false) < r i ∨ r (G.child i true) < r i) ∧
       (G.nodeType i = .max ∨ G.nodeType i = .min → r (G.child i false) < r i ∧ r (G.child i true) < r i)

theorem exists_max_list {α : Type} (l : List α) (f : α → ℚ) (hl : l ≠ []) : ∃ i ∈ l, ∀ j ∈ l, f j ≤ f i := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    by_cases h : l = []
    · subst h; exact ⟨a, by simp, fun j hj => by simp at hj; rw [hj]⟩
    · obtain ⟨i, hi, hmax⟩ := ih h
      by_cases c : f a ≤ f i
      · refine ⟨i, by simp [hi], fun j hj => ?_⟩
        simp at hj; rcases hj with hj | hj
        · rw [hj]; exact c
        · exact hmax j hj
      · refine ⟨a, by simp, fun j hj => ?_⟩
        simp at hj; rcases hj with hj | hj
        · rw [hj]
        · have := hmax j hj; linarith

theorem exists_max (f : Fin n → ℚ) (v0 : Fin n) : ∃ i, ∀ j, f j ≤ f i := by
  have hne : List.finRange n ≠ [] := fun h => by
    have := List.mem_finRange v0; rw [h] at this; simp at this
  obtain ⟨i, _, h⟩ := exists_max_list (List.finRange n) f hne
  exact ⟨i, fun j => h j (List.mem_finRange j)⟩

/-- **comparison principle**: on a ranked game, a vector that is `≤ 0` at terminals, at most the average of its
children at average nodes and at most some child at max/min nodes, is `≤ 0`. -/
theorem cmp (G : Game n) (r : Fin n → ℕ) (hr : Ranked G r) (d : Fin n → ℚ)
    (hs : ∀ i, isTerminal G i = true → d i ≤ 0)
    (hc : ∀ i, G.nodeType i = .average → 2 * d i ≤ de G d (G.child i false) + de G d (G.child i true))
    (hp : ∀ i, (G.nodeType i = .max ∨ G.nodeType i = .min) → ∃ a, d i ≤ de G d (G.child i a)) : ∀ i, d i ≤ 0 := by
  intro i0
  obtain ⟨m, hm⟩ := exists_max d i0
  by_contra hcon
  have hM : 0 < d m := lt_of_lt_of_le (lt_of_not_ge hcon) (hm i0)
  have hall : ∀ j, de G d j ≤ d m := by
    intro j; unfold de; split
    · exact le_of_lt hM
    · exact hm j
  have key : ∀ k : ℕ, ∀ i, r i < k → d i < d m := by
    intro k
    induction k with
    | zero => intro i h; omega
    | succ k ih =>
      intro i hi
      have hlow : ∀ j, r j < r i → de G d j < d m := by
        intro j hj; unfold de; split
        · exact hM
        · exact ih j (by omega)
      by_cases hsk : isTerminal G i = true
      · exact lt_of_le_of_lt (hs i hsk) hM
      · cases hk : G.nodeType i with
        | terminal0 => simp [isTerminal, hk] at hsk
        | terminal1 => simp [isTerminal, hk] at hsk
        | average =>
          have h1 := hc i hk
          have a0 := hall (G.child i false); have a1 := hall (G.child i true)
          rcases (hr i).1 hk with h | h
          · have := hlow _ h; linarith
          · have := hlow _ h; linarith
        | max =>
          obtain ⟨a, ha⟩ := hp i (Or.inl hk)
          have hl := (hr i).2 (Or.inl hk)
          cases a
          · have := hlow _ hl.1; linarith
          · have := hlow _ hl.2; linarith
        | min =>
          obtain ⟨a, ha⟩ := hp i (Or.inr hk)
          have hl := (hr i).2 (Or.inr hk)
          cases a
          · have := hlow _ hl.1; linarith
          · have := hlow _ hl.2; linarith
  exact absurd (key (r m + 1) m (by omega)) (lt_irrefl _)

/-! ## 3. peeling: a computable rank -/

def peelStep (G : Game n) (P : Fin n → Bool) (i : Fin n) : Bool :=
  P i || (match G.nodeType i with
    | .terminal0 => true
    | .terminal1 => true
    | .average => P (G.child i false) || P (G.child i true)
    | .max => P (G.child i false) && P (G.child i true)
    | .min => P (G.child i false) && P (G.child i true))

/-- `peel G k i`: node `i` is removed within `k` rounds. -/
def peel (G : Game n) : ℕ → Fin n → Bool
  | 0 => fun _ => false
  | k + 1 => peelStep G (peel G k)

/-- number of indices `k < N` with `b k = false`. -/
def cnt (b : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | N + 1 => cnt b N + (if b N then 0 else 1)

/-- **the computed rank**: the round in which the node is removed (minus one). -/
def prank (G : Game n) (i : Fin n) : ℕ := cnt (fun k => peel G (k + 1) i) n

/-- **the computable stopping test**: peeling removes every node within `n` rounds. -/
def peelAll (G : Game n) : Bool := decide (∀ i, peel G n i = true)

theorem peel_succ_of (G : Game n) (k : ℕ) (i : Fin n) (h : peel G k i = true) : peel G (k + 1) i = true := by
  simp [peel, peelStep, h]

theorem peel_mono (G : Game n) {k m : ℕ} (hkm : k ≤ m) (i : Fin n) (h : peel G k i = true) : peel G m i = true := by
  induction m with
  | zero => have : k = 0 := by omega
            subst this; exact h
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with hl | hl
    · exact peel_succ_of G m i (ih (by omega))
    · have : k = m + 1 := by omega
      subst this; exact h

section cnt
variable (b : ℕ → Bool) (hb : ∀ k m, k ≤ m → b k = true → b m = true)

include hb in
theorem cnt_le : ∀ N, cnt b N ≤ N := by
  intro N; induction N with
  | zero => simp [cnt]
  | succ N ih => simp only [cnt]; split <;> omega

include hb in
theorem cnt_le_of (j : ℕ) (hj : b j = true) : ∀ N, cnt b N ≤ j := by
  intro N; induction N with
  | zero => simp [cnt]
  | succ N ih =>
    simp only [cnt]
    by_cases h : b N = true
    · simp [h]; exact ih
    · have : N < j := by
        by_contra c; exact h (hb j N (by omega) hj)
      have := cnt_le b hb N
      simp [h]; omega

include hb in
theorem cnt_true : ∀ N, b (cnt b N) = true ∨ cnt b N = N := by
  intro N; induction N with
  | zero => right; rfl
  | succ N ih =>
    simp only [cnt]
    rcases ih with h | h
    · have hN : b N = true := hb _ N (cnt_le b hb N) h
      left; simp [hN, h]
    · by_cases hN : b N = true
      · left; simp [hN, h]
      · right; simp [hN, h]
end cnt

theorem peel_mono' (G : Game n) (i : Fin n) :
    ∀ k m, k ≤ m → (fun k => peel G (k + 1) i) k = true → (fun k => peel G (k + 1) i) m = true :=
  fun k m h hk => peel_mono G (by omega) i hk

theorem peel_zero (G : Game n) (i : Fin n) : peel G 0 i = false := rfl

/-- under `peelAll`, `prank i < n`, `i` is removed in round `prank i + 1` and not before. -/
theorem prank_facts (G : Game n) (hall : ∀ i, peel G n i = true) (i : Fin n) :
    prank G i < n ∧ peel G (prank G i + 1) i = true ∧ peel G (prank G i) i = false := by
  have hn : 0 < n := Fin.pos i
  have hb := peel_mono' G i
  have hlast : (fun k => peel G (k + 1) i) (n - 1) = true := by
    simp only; rw [show n - 1 + 1 = n by omega]; exact hall i
  have hle := cnt_le_of _ hb (n - 1) hlast n
  refine ⟨by unfold prank; omega, ?_, ?_⟩
  · rcases cnt_true _ hb n with h | h
    · exact h
    · unfold prank; omega
  · unfold prank
    generalize hc : cnt (fun k => peel G (k + 1) i) n = c
    cases c with
    | zero => rfl
    | succ c =>
      by_contra hcon
      have h1 : peel G (c + 1) i = true := by simpa using hcon
      have := cnt_le_of _ hb c h1 n
      omega

theorem prank_le_of_peel (G : Game n) (i : Fin n) (k : ℕ) (h : peel G (k + 1) i = true) : prank G i ≤ k :=
  cnt_le_of _ (peel_mono' G i) k h n

/-- **peeling yields a rank certificate**. -/
theorem prank_ranked (G : Game n) (hall : ∀ i, peel G n i = true) : Ranked G (prank G) := by
  intro i
  obtain ⟨_, h1, h0⟩ := prank_facts G hall i
  generalize hm : prank G i = m at h1 h0
  have step : peelStep G (peel G m) i = true := h1
  simp only [peelStep, h0, Bool.false_or] at step
  -- a child removed by round `m` has rank `< m`
  have low : ∀ j, peel G m j = true → prank G j < m := by
    intro j hj
    cases m with
    | zero => simp [peel] at hj
    | succ m => have := prank_le_of_peel G j m hj; omega
  constructor
  · intro hk
    rw [hk] at step
    simp only [Bool.or_eq_true] at step
    rcases step with h | h
    · left; exact low _ h
    · right; exact low _ h
  · intro hk
    rcases hk with hk | hk <;> rw [hk] at step <;> simp only [Bool.and_eq_true] at step <;>
      exact ⟨low _ step.1, low _ step.2⟩

theorem peelAll_iff (G : Game n) : peelAll G = true ↔ ∀ i, peel G n i = true := by
  simp [peelAll]

/-! ## 4. fixed points: uniqueness, bounds -/

/-- a fixed point is a chain fixed point for its greedy choice. -/
theorem fix_cmp_hyp (G : Game n) (v : Fin n → ℚ) (hv : F G v = v) (i : Fin n) :
    (G.nodeType i = .max → ∃ a, v i = ev G v (G.child i a) ∧ ∀ b, ev G v (G.child i b) ≤ v i) ∧
    (G.nodeType i = .min → ∃ a, v i = ev G v (G.child i a) ∧ ∀ b, v i ≤ ev G v (G.child i b)) ∧
    (G.nodeType i = .average → 2 * v i = ev G v (G.child i false) + ev G v (G.child i true)) ∧
    (G.nodeType i = .terminal0 → v i = 0) ∧ (G.nodeType i = .terminal1 → v i = 1) := by
  have h := congrFun hv i
  unfold F at h
  refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_, fun hk => ?_, fun hk => ?_⟩ <;> rw [hk] at h <;> try simp only at h
  · rcases max_choice (ev G v (G.child i false)) (ev G v (G.child i true)) with e | e
    · refine ⟨false, by rw [← h, e], fun b => ?_⟩
      cases b
      · rw [← h]; exact le_max_left _ _
      · rw [← h]; exact le_max_right _ _
    · refine ⟨true, by rw [← h, e], fun b => ?_⟩
      cases b
      · rw [← h]; exact le_max_left _ _
      · rw [← h]; exact le_max_right _ _
  · rcases min_choice (ev G v (G.child i false)) (ev G v (G.child i true)) with e | e
    · refine ⟨false, by rw [← h, e], fun b => ?_⟩
      cases b
      · rw [← h]; exact min_le_left _ _
      · rw [← h]; exact min_le_right _ _
    · refine ⟨true, by rw [← h, e], fun b => ?_⟩
      cases b
      · rw [← h]; exact min_le_left _ _
      · rw [← h]; exact min_le_right _ _
  · linarith
  · exact h.symm
  · exact h.symm

/-- sub-fixed-point comparison: if `u` is a fixed point of `F` and `w` is a fixed point of `F`, `u ≤ w`. -/
theorem fix_le (G : Game n) (r : Fin n → ℕ) (hr : Ranked G r) (u w : Fin n → ℚ) (hu : F G u = u) (hw : F G w = w) :
    ∀ i, u i ≤ w i := by
  have key := cmp G r hr (fun i => u i - w i) ?_ ?_ ?_
  · intro i; have := key i; linarith
  · intro i hs
    have a := fix_cmp_hyp G u hu i; have b := fix_cmp_hyp G w hw i
    unfold isTerminal at hs
    cases hk : G.nodeType i <;> simp [hk] at hs
    · rw [a.2.2.2.1 hk, b.2.2.2.1 hk]; simp
    · rw [a.2.2.2.2 hk, b.2.2.2.2 hk]; simp
  · intro i hk
    have a := (fix_cmp_hyp G u hu i).2.2.1 hk; have b := (fix_cmp_hyp G w hw i).2.2.1 hk
    rw [← ev_sub, ← ev_sub]; linarith
  · intro i hk
    rcases hk with hk | hk
    · obtain ⟨a, ha, _⟩ := (fix_cmp_hyp G u hu i).1 hk
      obtain ⟨_, _, hb⟩ := (fix_cmp_hyp G w hw i).1 hk
      refine ⟨a, ?_⟩; rw [← ev_sub]; have := hb a; linarith
    · obtain ⟨a, ha, _⟩ := (fix_cmp_hyp G w hw i).2.1 hk
      obtain ⟨_, _, hb⟩ := (fix_cmp_hyp G u hu i).2.1 hk
      refine ⟨a, ?_⟩; rw [← ev_sub]; have := hb a; linarith

/-- **uniqueness** of the fixed point on a ranked game. -/
theorem fix_unique (G : Game n) (r : Fin n → ℕ) (hr : Ranked G r) (u w : Fin n → ℚ) (hu : F G u = u)
    (hw : F G w = w) : u = w := by
  funext i; exact le_antisymm (fix_le G r hr u w hu hw i) (fix_le G r hr w u hw hu i)

theorem ev_bounds (G : Game n) (v : Fin n → ℚ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (j : Fin n) :
    0 ≤ ev G v j ∧ ev G v j ≤ 1 := by
  unfold ev; cases G.nodeType j <;> simp [hv j]

/-- **bounds**: a fixed point lies in `[0,1]^n`. -/
theorem fix_bounds (G : Game n) (r : Fin n → ℕ) (hr : Ranked G r) (v : Fin n → ℚ) (hv : F G v = v) :
    ∀ i, 0 ≤ v i ∧ v i ≤ 1 := by
  have evle : ∀ j, ev G v j - 1 ≤ de G (fun i => v i - 1) j := by
    intro j; unfold ev de isTerminal; cases G.nodeType j <;> simp
  have evge : ∀ j, -ev G v j ≤ de G (fun i => - v i) j := by
    intro j; unfold ev de isTerminal; cases G.nodeType j <;> simp
  have up := cmp G r hr (fun i => v i - 1) ?_ ?_ ?_
  have lo := cmp G r hr (fun i => - v i) ?_ ?_ ?_
  · intro i; have a := up i; have b := lo i; constructor <;> linarith
  -- lower bound hypotheses
  · intro i hs
    have a := fix_cmp_hyp G v hv i
    unfold isTerminal at hs
    cases hk : G.nodeType i <;> simp [hk] at hs
    · rw [a.2.2.2.1 hk]; simp
    · rw [a.2.2.2.2 hk]; simp
  · intro i hk
    have a := (fix_cmp_hyp G v hv i).2.2.1 hk
    have := evge (G.child i false); have := evge (G.child i true); (try simp only); linarith
  · intro i hk
    rcases hk with hk | hk
    · obtain ⟨a, ha, _⟩ := (fix_cmp_hyp G v hv i).1 hk
      exact ⟨a, by have := evge (G.child i a); (try simp only); linarith⟩
    · obtain ⟨a, ha, _⟩ := (fix_cmp_hyp G v hv i).2.1 hk
      exact ⟨a, by have := evge (G.child i a); (try simp only); linarith⟩
  -- upper bound hypotheses
  · intro i hs
    have a := fix_cmp_hyp G v hv i
    unfold isTerminal at hs
    cases hk : G.nodeType i <;> simp [hk] at hs
    · rw [a.2.2.2.1 hk]; norm_num
    · rw [a.2.2.2.2 hk]; norm_num
  · intro i hk
    have a := (fix_cmp_hyp G v hv i).2.2.1 hk
    have := evle (G.child i false); have := evle (G.child i true); (try simp only); linarith
  · intro i hk
    rcases hk with hk | hk
    · obtain ⟨a, ha, _⟩ := (fix_cmp_hyp G v hv i).1 hk
      exact ⟨a, by have := evle (G.child i a); (try simp only); linarith⟩
    · obtain ⟨a, ha, _⟩ := (fix_cmp_hyp G v hv i).2.1 hk
      exact ⟨a, by have := evle (G.child i a); (try simp only); linarith⟩

/-! ## 5. pointwise comparison and the chain system -/

/-- the comparison hypotheses at one node, for two vectors that satisfy the fixed-point equation there. -/
theorem cmp_at (G : Game n) (u w : Fin n → ℚ) (i : Fin n) (hu : F G u i = u i) (hw : F G w i = w i) :
    (isTerminal G i = true → u i - w i ≤ 0) ∧
    (G.nodeType i = .average → 2 * (u i - w i) ≤ de G (fun i => u i - w i) (G.child i false) +
        de G (fun i => u i - w i) (G.child i true)) ∧
    ((G.nodeType i = .max ∨ G.nodeType i = .min) → ∃ a, u i - w i ≤ de G (fun i => u i - w i) (G.child i a)) := by
  unfold F at hu hw
  refine ⟨fun hs => ?_, fun hk => ?_, fun hk => ?_⟩
  · unfold isTerminal at hs
    cases hk : G.nodeType i <;> simp [hk] at hs <;> rw [hk] at hu hw <;> simp only at hu hw <;> linarith
  · rw [hk] at hu hw; simp only at hu hw; rw [← ev_sub, ← ev_sub]; linarith
  · rcases hk with hk | hk <;> rw [hk] at hu hw <;> simp only at hu hw
    · rcases max_choice (ev G u (G.child i false)) (ev G u (G.child i true)) with e | e
      · refine ⟨false, ?_⟩; rw [← ev_sub]; have := le_max_left (ev G w (G.child i false)) (ev G w (G.child i true))
        linarith
      · refine ⟨true, ?_⟩; rw [← ev_sub]; have := le_max_right (ev G w (G.child i false)) (ev G w (G.child i true))
        linarith
    · rcases min_choice (ev G w (G.child i false)) (ev G w (G.child i true)) with e | e
      · refine ⟨false, ?_⟩; rw [← ev_sub]; have := min_le_left (ev G u (G.child i false)) (ev G u (G.child i true))
        linarith
      · refine ⟨true, ?_⟩; rw [← ev_sub]; have := min_le_right (ev G u (G.child i false)) (ev G u (G.child i true))
        linarith

/-- coefficient of the unknown `j` in the value of the target `t` (zero for a terminal target). -/
def cf (G : Game n) (t j : Fin n) : ℚ := if j = t ∧ isTerminal G t = false then 1 else 0

/-- the constant part of the value of the target `t`. -/
def sv (G : Game n) (t : Fin n) : ℚ :=
  match G.nodeType t with
  | .terminal1 => 1
  | _ => 0

theorem cf_sum (G : Game n) (t : Fin n) (y : Fin n → ℚ) : ∑ j, cf G t j * y j = de G y t := by
  unfold cf de
  by_cases hs : isTerminal G t = true
  · simp [hs]
  · have hs' : isTerminal G t = false := by simpa using hs
    simp only [hs', and_true, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp

theorem ev_split (G : Game n) (y : Fin n → ℚ) (t : Fin n) : ev G y t = sv G t + de G y t := by
  unfold ev sv de isTerminal; cases G.nodeType t <;> simp

/-- the linear system of the chain of `π`: `y - P y = b`. -/
def chainA (G : Game n) (π : Fin n → Bool) : Mat n := fun i j =>
  (if j = i then 1 else 0) -
    (match G.nodeType i with
     | .terminal0 => 0
     | .terminal1 => 0
     | .max => cf G (G.child i (π i)) j
     | .min => cf G (G.child i (π i)) j
     | .average => (cf G (G.child i false) j + cf G (G.child i true) j) / 2)

def chainB (G : Game n) (π : Fin n → Bool) : Vec n := fun i =>
  match G.nodeType i with
  | .terminal0 => 0
  | .terminal1 => 1
  | .max => sv G (G.child i (π i))
  | .min => sv G (G.child i (π i))
  | .average => (sv G (G.child i false) + sv G (G.child i true)) / 2

/-- the linear part of row `i`. -/
def lin (G : Game n) (π : Fin n → Bool) (y : Fin n → ℚ) (i : Fin n) : ℚ :=
  match G.nodeType i with
  | .terminal0 => 0
  | .terminal1 => 0
  | .max => de G y (G.child i (π i))
  | .min => de G y (G.child i (π i))
  | .average => (de G y (G.child i false) + de G y (G.child i true)) / 2

theorem chain_row (G : Game n) (π : Fin n → Bool) (y : Fin n → ℚ) (i : Fin n) :
    ∑ j, chainA G π i j * y j = y i - lin G π y i := by
  unfold chainA lin
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  congr 1
  cases G.nodeType i with
  | terminal0 => simp
  | terminal1 => simp
  | max => exact cf_sum G _ y
  | min => exact cf_sum G _ y
  | average =>
    have e : ∀ j, (cf G (G.child i false) j + cf G (G.child i true) j) / 2 * y j =
        (1 / 2) * (cf G (G.child i false) j * y j) + (1 / 2) * (cf G (G.child i true) j * y j) := by
      intro j; ring
    simp only [e, Finset.sum_add_distrib, ← mul_sum', cf_sum]; ring

theorem chain_sol (G : Game n) (π : Fin n → Bool) (y : Fin n → ℚ) :
    HSol (chainA G π) (chainB G π) 1 y ↔ Fp G π y = y := by
  constructor
  · intro h; funext i
    have := h i; rw [chain_row] at this
    unfold Fp; unfold lin chainB at this
    cases hk : G.nodeType i <;> simp only [hk] at this ⊢ <;> (try simp only [ev_split]) <;> linarith
  · intro h i
    rw [chain_row]
    have := congrFun h i
    unfold Fp at this; unfold lin chainB
    cases hk : G.nodeType i <;> simp only [hk] at this ⊢ <;> (try simp only [ev_split] at this) <;> linarith

theorem de_neg (G : Game n) (y : Fin n → ℚ) (j : Fin n) : de G (fun i => - y i) j = - de G y j := by
  unfold de; split <;> simp

/-- the chain system of a ranked game is injective. -/
theorem chain_inj (G : Game n) (r : Fin n → ℕ) (hr : Ranked G r) (π : Fin n → Bool) (y : Fin n → ℚ)
    (h : HSol (chainA G π) (chainB G π) 0 y) : y = 0 := by
  have eq : ∀ i, y i = lin G π y i := by
    intro i; have := h i; rw [chain_row] at this; linarith
  have side : ∀ (d : Fin n → ℚ), (∀ i, d i = lin G π d i) → ∀ i, d i ≤ 0 := by
    intro d hd
    apply cmp G r hr d
    · intro i hs; have := hd i; unfold lin at this; unfold isTerminal at hs
      cases hk : G.nodeType i <;> simp [hk] at hs this <;> linarith
    · intro i hk; have := hd i; unfold lin at this; rw [hk] at this; simp only at this; linarith
    · intro i hk; have := hd i; unfold lin at this
      rcases hk with hk | hk <;> rw [hk] at this <;> exact ⟨π i, le_of_eq this⟩
  have a := side y eq
  have b := side (fun i => - y i) (by
    intro i; have := eq i; unfold lin at this ⊢
    cases hk : G.nodeType i <;> simp only [hk, de_neg] at this ⊢ <;> linarith)
  funext i; have := a i; have := b i; simp only [Pi.zero_apply] at *; linarith

/-! ## 6. existence of a rational fixed point -/

/-- number of max/min nodes with two distinct children. -/
def nfree (G : Game n) : ℕ :=
  (Finset.univ.filter (fun i => (G.nodeType i = .max ∨ G.nodeType i = .min) ∧ G.child i false ≠ G.child i true)).card

/-- fix the choice `a` at node `u`. -/
def fixG (G : Game n) (u : Fin n) (a : Bool) : Game n where
  nodeType := G.nodeType
  childJ := fun i => if i = u then G.child u a else G.childJ i
  childK := fun i => if i = u then G.child u a else G.childK i
  startNode := G.startNode

theorem fixG_child (G : Game n) (u : Fin n) (a : Bool) (i : Fin n) (b : Bool) :
    (fixG G u a).child i b = if i = u then G.child u a else G.child i b := by
  cases b <;> simp [Game.child, fixG]

theorem fixG_nodeType (G : Game n) (u : Fin n) (a : Bool) : (fixG G u a).nodeType = G.nodeType := rfl

theorem fixG_ranked (G : Game n) (r : Fin n → ℕ) (hr : Ranked G r) (u : Fin n) (a : Bool)
    (hu : G.nodeType u = .max ∨ G.nodeType u = .min) : Ranked (fixG G u a) r := by
  intro i
  by_cases hi : i = u
  · subst hi
    have h := (hr i).2 hu
    have ha : r (G.child i a) < r i := by cases a; exact h.1; exact h.2
    refine ⟨fun hk => ?_, fun _ => ?_⟩
    · exfalso; change G.nodeType i = .average at hk; rcases hu with e | e <;> rw [e] at hk <;> cases hk
    · simp only [fixG_child, if_true]; exact ⟨ha, ha⟩
  · simp only [fixG_child, hi, if_false]; exact hr i

theorem F_fixG (G : Game n) (u : Fin n) (a : Bool) (x : Fin n → ℚ) (i : Fin n) (hi : i ≠ u) :
    F (fixG G u a) x i = F G x i := by
  simp only [F, ev, fixG_child, fixG_nodeType, hi, if_false]

theorem F_fixG_u (G : Game n) (u : Fin n) (a : Bool) (x : Fin n → ℚ) (hu : G.nodeType u = .max ∨ G.nodeType u = .min) :
    F (fixG G u a) x u = ev G x (G.child u a) := by
  rcases hu with h | h <;> simp [F, fixG_child, fixG_nodeType, h, ev]

theorem nfree_fixG (G : Game n) (u : Fin n) (a : Bool) (hu : (G.nodeType u = .max ∨ G.nodeType u = .min) ∧
    G.child u false ≠ G.child u true) : nfree (fixG G u a) < nfree G := by
  unfold nfree
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨u, by simp [hu], ?_⟩
    intro hmem; rw [Finset.mem_filter] at hmem; simp [fixG_child, fixG_nodeType] at hmem
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_cases h : i = u
    · subst h; simp [fixG_child, fixG_nodeType] at hi
    · simpa [fixG_child, fixG_nodeType, h] using hi

/-- comparison with one modified node `u0` whose two children coincide. -/
theorem cmp_two (H : Game n) (r : Fin n → ℕ) (hr : Ranked H r) (u0 : Fin n) (p q : Fin n → ℚ)
    (hp : ∀ i, i ≠ u0 → F H p i = p i) (hq : ∀ i, i ≠ u0 → F H q i = q i)
    (hk : H.nodeType u0 = .max ∨ H.nodeType u0 = .min)
    (hd : p u0 - q u0 ≤ ev H p (H.child u0 false) - ev H q (H.child u0 false)) : ∀ i, p i ≤ q i := by
  have key := cmp H r hr (fun i => p i - q i) ?_ ?_ ?_
  · intro i; have := key i; linarith
  · intro i hs
    by_cases hi : i = u0
    · subst hi; unfold isTerminal at hs; rcases hk with e | e <;> rw [e] at hs <;> simp at hs
    · exact (cmp_at H p q i (hp i hi) (hq i hi)).1 hs
  · intro i hc
    by_cases hi : i = u0
    · subst hi; rcases hk with e | e <;> rw [e] at hc <;> cases hc
    · exact (cmp_at H p q i (hp i hi) (hq i hi)).2.1 hc
  · intro i hc
    by_cases hi : i = u0
    · subst hi; exact ⟨false, by rw [← ev_sub]; exact hd⟩
    · exact (cmp_at H p q i (hp i hi) (hq i hi)).2.2 hc

theorem fix_exists_base (G : Game n) (r : Fin n → ℕ) (hr : Ranked G r) (h0 : nfree G = 0) : ∃ v, F G v = v := by
  have hall : ∀ i, (G.nodeType i = .max ∨ G.nodeType i = .min) → G.child i false = G.child i true := by
    intro i hi
    unfold nfree at h0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
    by_contra c; exact h0 (Finset.mem_univ i) ⟨hi, c⟩
  obtain ⟨y, hy⟩ := gj_complete (chainA G (fun _ => false)) (chainB G (fun _ => false))
    (chain_inj G r hr (fun _ => false))
  have hs := (gj_sound _ _ y hy y).mpr rfl
  rw [chain_sol] at hs
  refine ⟨y, ?_⟩
  have e : F G y = Fp G (fun _ => false) y := by
    funext i
    unfold F Fp
    cases hk : G.nodeType i <;> simp only
    · rw [hall i (Or.inl hk)]; simp
    · rw [hall i (Or.inr hk)]; simp
  rw [e, hs]

/-- **existence** of a rational fixed point of `F` on a ranked game. -/
theorem fix_exists : ∀ (k : ℕ) (G : Game n) (r : Fin n → ℕ), Ranked G r → nfree G ≤ k → ∃ v, F G v = v := by
  intro k
  induction k with
  | zero => intro G r hr hk; exact fix_exists_base G r hr (by omega)
  | succ k ih =>
    intro G r hr hk
    by_cases h0 : nfree G = 0
    · exact fix_exists_base G r hr h0
    obtain ⟨u, hu⟩ : ∃ u, (G.nodeType u = .max ∨ G.nodeType u = .min) ∧ G.child u false ≠ G.child u true := by
      have : 0 < nfree G := by omega
      unfold nfree at this
      obtain ⟨u, hu⟩ := Finset.card_pos.mp this
      exact ⟨u, by simpa using hu⟩
    obtain ⟨v0, h0'⟩ := ih (fixG G u false) r (fixG_ranked G r hr u false hu.1) (by have := nfree_fixG G u false hu; omega)
    obtain ⟨v1, h1'⟩ := ih (fixG G u true) r (fixG_ranked G r hr u true hu.1) (by have := nfree_fixG G u true hu; omega)
    have e0 : ∀ i, i ≠ u → F G v0 i = v0 i := fun i hi => by rw [← F_fixG G u false v0 i hi, h0']
    have e1 : ∀ i, i ≠ u → F G v1 i = v1 i := fun i hi => by rw [← F_fixG G u true v1 i hi, h1']
    have u0 : v0 u = ev G v0 (G.child u false) := by rw [← F_fixG_u G u false v0 hu.1, h0']
    have u1 : v1 u = ev G v1 (G.child u true) := by rw [← F_fixG_u G u true v1 hu.1, h1']
    -- the games `fixG G u a` see `v0`, `v1` as fixed points off `u`
    have f0 : ∀ (x : Fin n → ℚ), (∀ i, i ≠ u → F G x i = x i) → ∀ a, ∀ i, i ≠ u → F (fixG G u a) x i = x i :=
      fun x hx a i hi => by rw [F_fixG G u a x i hi]; exact hx i hi
    have r0 := fixG_ranked G r hr u false hu.1
    have r1 := fixG_ranked G r hr u true hu.1
    have evf : ∀ a (x : Fin n → ℚ) j, ev (fixG G u a) x j = ev G x j := fun _ _ _ => rfl
    have sf : ∀ a b, (fixG G u a).child u b = G.child u a := fun a b => by simp [fixG_child]
    have kf : ∀ a, (fixG G u a).nodeType u = G.nodeType u := fun _ => rfl
    rcases hu.1 with hmax | hmin
    · -- max node
      by_cases c0 : ev G v0 (G.child u true) ≤ ev G v0 (G.child u false)
      · refine ⟨v0, funext fun i => ?_⟩
        by_cases hi : i = u
        · subst hi; simp only [F, hmax]; rw [u0]; exact max_eq_left c0
        · exact e0 i hi
      by_cases c1 : ev G v1 (G.child u false) ≤ ev G v1 (G.child u true)
      · refine ⟨v1, funext fun i => ?_⟩
        by_cases hi : i = u
        · subst hi; simp only [F, hmax]; rw [u1]; exact max_eq_right c1
        · exact e1 i hi
      exfalso
      have a := cmp_two (fixG G u false) r r0 u v1 v0 (f0 v1 e1 false) (f0 v0 e0 false) (Or.inl hmax)
        (by rw [sf, evf, evf, u1, u0]; linarith)
      have b := cmp_two (fixG G u true) r r1 u v0 v1 (f0 v0 e0 true) (f0 v1 e1 true) (Or.inl hmax)
        (by rw [sf, evf, evf, u1, u0]; linarith)
      have : v0 = v1 := funext fun i => le_antisymm (b i) (a i)
      subst this; linarith
    · -- min node
      by_cases c0 : ev G v0 (G.child u false) ≤ ev G v0 (G.child u true)
      · refine ⟨v0, funext fun i => ?_⟩
        by_cases hi : i = u
        · subst hi; simp only [F, hmin]; rw [u0]; exact min_eq_left c0
        · exact e0 i hi
      by_cases c1 : ev G v1 (G.child u true) ≤ ev G v1 (G.child u false)
      · refine ⟨v1, funext fun i => ?_⟩
        by_cases hi : i = u
        · subst hi; simp only [F, hmin]; rw [u1]; exact min_eq_right c1
        · exact e1 i hi
      exfalso
      have a := cmp_two (fixG G u false) r r0 u v0 v1 (f0 v0 e0 false) (f0 v1 e1 false) (Or.inr hmin)
        (by rw [sf, evf, evf, u1, u0]; linarith)
      have b := cmp_two (fixG G u true) r r1 u v1 v0 (f0 v1 e1 true) (f0 v0 e0 true) (Or.inr hmin)
        (by rw [sf, evf, evf, u1, u0]; linarith)
      have : v0 = v1 := funext fun i => le_antisymm (a i) (b i)
      subst this; linarith

/-! ## 7. the denominator bound -/

/-- the average node label of the multiple `k·y`. -/
def clab (G : Game n) (y : Fin n → ℚ) (k : ℕ) (i : Fin n) : ℤ :=
  match G.nodeType i with
  | .average => ⌊(k : ℚ) * ev G y (G.child i false)⌋ + ⌊(k : ℚ) * ev G y (G.child i true)⌋ - 2 * ⌊(k : ℚ) * y i⌋
  | _ => 0

theorem clab_range (G : Game n) (y : Fin n → ℚ) (k : ℕ) (i : Fin n)
    (hc : G.nodeType i = .average → 2 * y i = ev G y (G.child i false) + ev G y (G.child i true)) :
    -1 ≤ clab G y k i ∧ clab G y k i ≤ 1 := by
  unfold clab
  cases hk : G.nodeType i with
  | average =>
    simp only
    have e := hc hk
    have a1 := Int.floor_le ((k : ℚ) * ev G y (G.child i false))
    have a2 := Int.lt_floor_add_one ((k : ℚ) * ev G y (G.child i false))
    have b1 := Int.floor_le ((k : ℚ) * ev G y (G.child i true))
    have b2 := Int.lt_floor_add_one ((k : ℚ) * ev G y (G.child i true))
    have c1 := Int.floor_le ((k : ℚ) * y i)
    have c2 := Int.lt_floor_add_one ((k : ℚ) * y i)
    have ek : (k : ℚ) * ev G y (G.child i false) + (k : ℚ) * ev G y (G.child i true) = 2 * ((k : ℚ) * y i) := by
      rw [← mul_add, ← e]; ring
    have lo : ((-2 : ℤ) : ℚ) < ((⌊(k : ℚ) * ev G y (G.child i false)⌋ + ⌊(k : ℚ) * ev G y (G.child i true)⌋ -
        2 * ⌊(k : ℚ) * y i⌋ : ℤ) : ℚ) := by push_cast; linarith
    have hi : ((⌊(k : ℚ) * ev G y (G.child i false)⌋ + ⌊(k : ℚ) * ev G y (G.child i true)⌋ -
        2 * ⌊(k : ℚ) * y i⌋ : ℤ) : ℚ) < ((2 : ℤ) : ℚ) := by push_cast; linarith
    have lo' := (Int.cast_lt (R := ℚ)).mp lo
    have hi' := (Int.cast_lt (R := ℚ)).mp hi
    omega
  | _ => simp

def clab3 (G : Game n) (y : Fin n → ℚ) (k : Fin (3 ^ n + 1)) : Fin n → Fin 3 :=
  fun i => ⟨((clab G y k.val i + 1).toNat) % 3, Nat.mod_lt _ (by norm_num)⟩

/-- fractional parts of a fixed-point multiple satisfy the average node relation up to the label. -/
theorem fract_average (G : Game n) (y : Fin n → ℚ) (k : ℕ) (i : Fin n) (hk : G.nodeType i = .average)
    (e : 2 * y i = ev G y (G.child i false) + ev G y (G.child i true)) :
    2 * Int.fract ((k : ℚ) * y i) = Int.fract ((k : ℚ) * ev G y (G.child i false)) +
      Int.fract ((k : ℚ) * ev G y (G.child i true)) + (clab G y k i : ℚ) := by
  unfold clab; rw [hk]; simp only
  unfold Int.fract; push_cast
  have ek : (k : ℚ) * ev G y (G.child i false) + (k : ℚ) * ev G y (G.child i true) = 2 * ((k : ℚ) * y i) := by
    rw [← mul_add, ← e]; ring
  linarith

theorem fract_ev (G : Game n) (y : Fin n → ℚ) (k₁ k₂ : ℕ) (t : Fin n) :
    Int.fract ((k₂ : ℚ) * ev G y t) - Int.fract ((k₁ : ℚ) * ev G y t) =
      de G (fun j => Int.fract ((k₂ : ℚ) * y j) - Int.fract ((k₁ : ℚ) * y j)) t := by
  unfold de ev isTerminal
  cases G.nodeType t <;> simp

/-- **denominator bound**: a fixed point of `F` on a ranked game has a common denominator `D ≤ 3^n`. -/
theorem denom_bound (G : Game n) (r : Fin n → ℕ) (hr : Ranked G r) (v : Fin n → ℚ) (hv : F G v = v) :
    ∃ D : ℕ, 0 < D ∧ D ≤ 3 ^ n ∧ ∀ i, ∃ z : ℤ, (D : ℚ) * v i = z := by
  have hc : ∀ i, G.nodeType i = .average → 2 * v i = ev G v (G.child i false) + ev G v (G.child i true) :=
    fun i hk => (fix_cmp_hyp G v hv i).2.2.1 hk
  -- pigeonhole
  obtain ⟨a, b, hne, hab⟩ : ∃ a b : Fin (3 ^ n + 1), a ≠ b ∧ clab3 G v a = clab3 G v b := by
    by_contra hcon
    have inj : Function.Injective (clab3 G v) := fun a b hab => by
      by_contra hne; exact hcon ⟨a, b, hne, hab⟩
    have := Fintype.card_le_of_injective _ inj
    simp [Fintype.card_fun] at this
  have heq : ∀ i, clab G v a.val i = clab G v b.val i := by
    intro i
    have h := congrArg Fin.val (congrFun hab i)
    simp only [clab3] at h
    have ra := clab_range G v a.val i (hc i)
    have rb := clab_range G v b.val i (hc i)
    omega
  -- the difference of fractional parts vanishes
  have key : ∀ k₁ k₂ : ℕ, (∀ i, clab G v k₁ i = clab G v k₂ i) →
      ∀ i, Int.fract ((k₂ : ℚ) * v i) = Int.fract ((k₁ : ℚ) * v i) := by
    intro k₁ k₂ hl
    let z : Fin n → ℚ := fun j => Int.fract ((k₂ : ℚ) * v j) - Int.fract ((k₁ : ℚ) * v j)
    have hz : ∀ (s : ℚ), s = 1 ∨ s = -1 → ∀ i, s * z i ≤ 0 := by
      intro s hs
      have des : ∀ t, de G (fun j => s * z j) t = s * de G z t := by
        intro t; unfold de; split <;> simp
      apply cmp G r hr (fun j => s * z j)
      · intro i hsk
        have a := fix_cmp_hyp G v hv i
        unfold isTerminal at hsk
        cases hk : G.nodeType i <;> simp [hk] at hsk
        · simp only [z]; rw [a.2.2.2.1 hk]; simp
        · simp only [z]; rw [a.2.2.2.2 hk]
          rw [show ((k₂ : ℚ)) * 1 = ((k₂ : ℤ) : ℚ) by simp, show ((k₁ : ℚ)) * 1 = ((k₁ : ℤ) : ℚ) by simp,
            Int.fract_intCast, Int.fract_intCast]; simp
      · intro i hk
        rw [des, des, ← fract_ev, ← fract_ev]
        have f2 := fract_average G v k₂ i hk (hc i hk)
        have f1 := fract_average G v k₁ i hk (hc i hk)
        rw [hl i] at f1
        simp only [z]
        rcases hs with e | e <;> subst e <;> linarith
      · intro i hk
        rcases hk with hk | hk
        · obtain ⟨c, hc', _⟩ := (fix_cmp_hyp G v hv i).1 hk
          refine ⟨c, ?_⟩; rw [des, ← fract_ev, ← hc']
        · obtain ⟨c, hc', _⟩ := (fix_cmp_hyp G v hv i).2.1 hk
          refine ⟨c, ?_⟩; rw [des, ← fract_ev, ← hc']
    intro i
    have h1 := hz 1 (Or.inl rfl) i; have h2 := hz (-1) (Or.inr rfl) i
    simp only [z] at h1 h2; linarith
  have fin : ∀ k₁ k₂ : ℕ, k₁ < k₂ → k₂ ≤ 3 ^ n → (∀ i, clab G v k₁ i = clab G v k₂ i) →
      ∃ D : ℕ, 0 < D ∧ D ≤ 3 ^ n ∧ ∀ i, ∃ z : ℤ, (D : ℚ) * v i = z := by
    intro k₁ k₂ hlt hle hl
    refine ⟨k₂ - k₁, by omega, by omega, fun i => ⟨⌊(k₂ : ℚ) * v i⌋ - ⌊(k₁ : ℚ) * v i⌋, ?_⟩⟩
    have e := key k₁ k₂ hl i
    unfold Int.fract at e
    rw [Nat.cast_sub (le_of_lt hlt)]; push_cast; linarith
  have ha := a.isLt; have hb := b.isLt
  rcases Nat.lt_or_gt_of_ne (fun e => hne (Fin.ext e)) with h | h
  · exact fin a.val b.val h (by omega) heq
  · exact fin b.val a.val h (by omega) (fun i => (heq i).symm)

/-! ## 8. THEOREM W: the weighted contraction -/

/-- weights `w i = 2 - 3^-(prank i)`. -/
def wt (G : Game n) (i : Fin n) : ℚ := 2 - (1 / 3 : ℚ) ^ (prank G i)

/-- contraction gap `γ = 1/(4·3^n)`. -/
def gam (n : ℕ) : ℚ := 1 / (4 * 3 ^ n)

theorem wt_bounds (G : Game n) (i : Fin n) : 1 ≤ wt G i ∧ wt G i ≤ 2 := by
  unfold wt
  have h0 : 0 ≤ (1 / 3 : ℚ) ^ prank G i := by positivity
  have h1 : (1 / 3 : ℚ) ^ prank G i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  constructor <;> linarith

theorem abs_max_sub (a b c d e : ℚ) (h1 : |a - c| ≤ e) (h2 : |b - d| ≤ e) : |max a b - max c d| ≤ e := by
  rw [abs_le] at *
  rcases le_total a b with h | h <;> rcases le_total c d with h' | h' <;>
    simp [max_eq_right, max_eq_left, h, h'] <;> constructor <;> linarith

theorem abs_min_sub (a b c d e : ℚ) (h1 : |a - c| ≤ e) (h2 : |b - d| ≤ e) : |min a b - min c d| ≤ e := by
  rw [abs_le] at *
  rcases le_total a b with h | h <;> rcases le_total c d with h' | h' <;>
    simp [min_eq_right, min_eq_left, h, h'] <;> constructor <;> linarith

/-- **THEOREM W (weighted contraction)**: on a game where peeling succeeds (equivalently, a stopping game), if
`|x_j - y_j| ≤ M w_j` for all `j` then `|F(x)_i - F(y)_i| ≤ (1 - γ) M w_i` for all `i`. -/
theorem contraction (G : Game n) (hall : ∀ i, peel G n i = true) (x y : Fin n → ℚ) (M : ℚ) (hM : 0 ≤ M)
    (h : ∀ j, |x j - y j| ≤ M * wt G j) : ∀ i, |F G x i - F G y i| ≤ (1 - gam n) * M * wt G i := by
  intro i
  have hr := prank_ranked G hall
  obtain ⟨hlt, _, _⟩ := prank_facts G hall i
  set r := prank G i with hrdef
  set t : ℚ := (1 / 3 : ℚ) ^ r with htdef
  have hwi := wt_bounds G i
  have hγ : 0 ≤ gam n ∧ gam n ≤ 1 / 4 := by
    unfold gam; constructor
    · positivity
    · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (1 : ℚ) ≤ 3 ^ n := one_le_pow₀ (by norm_num); linarith
  have rhs_nonneg : 0 ≤ (1 - gam n) * M * wt G i := by
    apply mul_nonneg (mul_nonneg (by linarith) hM) (by linarith)
  -- error of a target
  have err : ∀ j, |ev G x j - ev G y j| ≤ 2 * M ∧ (prank G j < r → |ev G x j - ev G y j| ≤ M * (2 - 3 * t)) := by
    intro j
    have ht3 : 3 * t ≤ 1 → 0 ≤ M * (2 - 3 * t) := fun h3 => mul_nonneg hM (by linarith)
    unfold ev
    cases hk : G.nodeType j with
    | terminal0 => simp; exact ⟨by linarith, fun hj => ht3 (by
        have : t ≤ (1 / 3 : ℚ) ^ (prank G j + 1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        rw [pow_succ] at this; have : (1/3 : ℚ) ^ prank G j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num); linarith)⟩
    | terminal1 => simp; exact ⟨by linarith, fun hj => ht3 (by
        have : t ≤ (1 / 3 : ℚ) ^ (prank G j + 1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        rw [pow_succ] at this; have : (1/3 : ℚ) ^ prank G j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num); linarith)⟩
    | _ =>
      all_goals
      simp only
      have hj := h j
      have hw := wt_bounds G j
      refine ⟨by nlinarith, fun hjr => ?_⟩
      have : t ≤ (1 / 3 : ℚ) ^ (prank G j + 1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      rw [pow_succ] at this
      have : wt G j ≤ 2 - 3 * t := by unfold wt; linarith
      calc |x j - y j| ≤ M * wt G j := hj
        _ ≤ M * (2 - 3 * t) := mul_le_mul_of_nonneg_left this hM
  -- the key numerical inequality
  have key : M * (2 - 3 / 2 * t) ≤ (1 - gam n) * M * wt G i := by
    have ht : gam n * 4 ≤ t := by
      unfold gam
      have : (1 / 3 : ℚ) ^ n ≤ t := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      rw [div_pow, one_pow] at this
      have h3 : (0 : ℚ) < 3 ^ n := by positivity
      field_simp; field_simp at this; linarith
    have ht0 : 0 ≤ t := by positivity
    have : 2 - 3 / 2 * t ≤ (1 - gam n) * wt G i := by
      unfold wt; rw [← htdef]; nlinarith [hγ.1]
    calc M * (2 - 3 / 2 * t) ≤ M * ((1 - gam n) * wt G i) := mul_le_mul_of_nonneg_left this hM
      _ = (1 - gam n) * M * wt G i := by ring
  have ht0 : 0 ≤ t := by positivity
  unfold F
  cases hk : G.nodeType i with
  | terminal0 => simp; exact rhs_nonneg
  | terminal1 => simp; exact rhs_nonneg
  | max =>
    simp only
    have hl := (hr i).2 (Or.inl hk)
    have a := (err (G.child i false)).2 hl.1; have b := (err (G.child i true)).2 hl.2
    have := abs_max_sub _ _ _ _ _ a b
    have : M * (2 - 3 * t) ≤ M * (2 - 3 / 2 * t) := mul_le_mul_of_nonneg_left (by linarith) hM
    linarith
  | min =>
    simp only
    have hl := (hr i).2 (Or.inr hk)
    have a := (err (G.child i false)).2 hl.1; have b := (err (G.child i true)).2 hl.2
    have := abs_min_sub _ _ _ _ _ a b
    have : M * (2 - 3 * t) ≤ M * (2 - 3 / 2 * t) := mul_le_mul_of_nonneg_left (by linarith) hM
    linarith
  | average =>
    simp only
    have e : (ev G x (G.child i false) + ev G x (G.child i true)) / 2 - (ev G y (G.child i false) +
        ev G y (G.child i true)) / 2 = ((ev G x (G.child i false) - ev G y (G.child i false)) +
        (ev G x (G.child i true) - ev G y (G.child i true))) / 2 := by ring
    rw [e, abs_div, abs_two]
    have tri := abs_add_le (ev G x (G.child i false) - ev G y (G.child i false))
      (ev G x (G.child i true) - ev G y (G.child i true))
    have bnd : |ev G x (G.child i false) - ev G y (G.child i false)| + |ev G x (G.child i true) - ev G y (G.child i true)|
        ≤ M * (2 - 3 * t) + 2 * M := by
      rcases (hr i).1 hk with hl | hl
      · have := (err _).2 hl; have := (err (G.child i true)).1; linarith
      · have := (err _).2 hl; have := (err (G.child i false)).1; linarith
    have : (M * (2 - 3 * t) + 2 * M) / 2 = M * (2 - 3 / 2 * t) := by ring
    rw [div_le_iff₀ (by norm_num : (0:ℚ) < 2)]
    linarith

end SSG
