module

public import SSGinP.Values.Exact
public import SSGinP.GameFacts
public import Mathlib.Computability.TuringMachine.Computable

@[expose] public section

/-!
# SSGinP.Values.Statement: the statement "values and optimal strategies in polynomial time"
# and its sanity lemmas

The six definitions `Solution`, `IsSolution`, `natBits`, `encodeSolution`, `SolvesSSGValues`, `PTimeWord` are in
`SSGinP.Defs`, in the namespace `SSG`.
The theorem itself (`SSG.ssg_values_in_P_proved`) is in SSGinP.Values.Main.

THE OUTPUT FORMAT (`natBits`, `encodeSolution`) IS USED ONLY HERE, IN SSGinP.Values.Output AND IN SSGinP.Values.Main.

Sanity lemmas:
1. `encodeSolution_length_proved`      : the word has length `4 n² + 2 n`.
2. `encodeSolution_injective_proved`   : two answers of the same game with the same word are equal;
   `natBits_injective`, `isSolution_value_bits_proved` : on a Stopping Game every value is a fraction `≥ 0` whose
   numerator and denominator are `< 2^(2n)`, and `natBits (2n)` is injective on such numbers (the `2 n` bits lose
   nothing).
3. `isSolution_value_unique_proved`    : the values are unique.
4. `ssgDecision_iff_value_proved`      : `SSGDecision G ↔ WellFormed G ∧ StoppingGame G ∧ 1/2 ≤ (value of the start node)`.
-/

namespace SSG

variable {n : Nat}

/-! ## sanity lemmas -/

/-- the statement's `IsSolution` is the one of the algorithm-level theorems (`SSGValues.IsSolution`). -/
theorem isSolution_iff (G : Game n) (s : Solution n) :
    IsSolution G s ↔ SSGValues.IsSolution G s.value s.maxStrategy s.minStrategy := by
  unfold IsSolution SSGValues.IsSolution
  refine forall_congr' fun i => and_congr Iff.rfl (forall_congr' fun σ => ?_)
  exact (SSGValues.isSolution_min_iff G σ s.minStrategy i (s.value i)).symm

theorem natBits_length (w m : Nat) : (natBits w m).length = w := by simp [natBits]

/-- **sanity 1**: the output word has length `4 n² + 2 n`. -/
theorem encodeSolution_length_proved (s : Solution n) : (encodeSolution s).length = 4 * n ^ 2 + 2 * n := by
  have h : ∀ l : List (Fin n), (l.flatMap fun i =>
      natBits (2 * n) (s.value i).num.toNat ++ natBits (2 * n) (s.value i).den).length = l.length * (4 * n) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.flatMap_cons, List.length_append, natBits_length, ih, List.length_cons]; ring
  unfold encodeSolution
  simp only [List.length_append, h, List.length_map, List.length_finRange]
  ring

/-- **sanity 3**: the values are unique. -/
theorem isSolution_value_unique_proved (G : Game n) (s s' : Solution n) (h : IsSolution G s) (h' : IsSolution G s') :
    s.value = s'.value :=
  SSGValues.isSolution_unique G _ _ _ _ _ _ ((isSolution_iff G s).mp h) ((isSolution_iff G s').mp h')

theorem decide_k_inj {a b : ArcChoice} (h : decide (a = .k) = decide (b = .k)) : a = b := by
  cases a <;> cases b <;> simp_all

/-- **sanity 2**: the word determines the answer (among the answers of one game). -/
theorem encodeSolution_injective_proved (G : Game n) (s s' : Solution n) (h : IsSolution G s) (h' : IsSolution G s')
    (he : encodeSolution s = encodeSolution s') : s = s' := by
  have hv := isSolution_value_unique_proved G s s' h h'
  obtain ⟨v, σ, τ⟩ := s
  obtain ⟨v', σ', τ'⟩ := s'
  simp only at hv
  subst hv
  unfold encodeSolution at he
  simp only [List.append_assoc, List.append_cancel_left_eq] at he
  obtain ⟨h1, h2⟩ := List.append_inj he (by simp)
  have e1 : σ = σ' := funext fun i => decide_k_inj (List.map_inj_left.mp h1 i (List.mem_finRange i))
  have e2 : τ = τ' := funext fun i => decide_k_inj (List.map_inj_left.mp h2 i (List.mem_finRange i))
  rw [e1, e2]

/-- `natBits w` loses nothing on numbers below `2^w`. -/
theorem natBits_injective (w a b : Nat) (ha : a < 2 ^ w) (hb : b < 2 ^ w) (h : natBits w a = natBits w b) :
    a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · have := congrArg (fun l => l[i]?) h
    simpa [natBits, hi] using this
  · have h1 : a < 2 ^ i := lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi))
    have h2 : b < 2 ^ i := lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi))
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

/-- on a Stopping Game the values of an answer are the stable assignment. -/
theorem isSolution_value_stable (G : Game n) (hs : StoppingGame G) (s : Solution n) (h : IsSolution G s) :
    F G s.value = s.value := by
  obtain ⟨v, hv⟩ := stable_point_exists G hs
  have := SSGValues.isSolution_unique G _ _ _ _ _ _ ((isSolution_iff G s).mp h)
    (SSGValues.greedy_isSolution G hs v hv)
  rw [this]; exact hv

/-- **sanity 2 (the `2 n` bits lose nothing)**: on a Stopping Game every value of an answer is `≥ 0` and its
numerator and denominator are below `2^(2n)`. -/
theorem isSolution_value_bits_proved (G : Game n) (hs : StoppingGame G) (s : Solution n) (h : IsSolution G s)
    (i : Fin n) :
    0 ≤ s.value i ∧ (s.value i).num.toNat < 2 ^ (2 * n) ∧ (s.value i).den < 2 ^ (2 * n) := by
  have hv := isSolution_value_stable G hs s h
  have hr := prank_ranked G (peelAll_of_stoppingGame G hs)
  obtain ⟨h0, h1⟩ := fix_bounds G (prank G) hr s.value hv i
  have hden := SSGValues.value_den G hs s.value hv i
  have hn : 1 ≤ n := Nat.one_le_of_lt i.2
  have h34 : 3 ^ n < 2 ^ (2 * n) := by
    rw [pow_mul]; exact Nat.pow_lt_pow_left (by norm_num) (by omega)
  have hnum0 : 0 ≤ (s.value i).num := Rat.num_nonneg.mpr h0
  have hnum : (s.value i).num ≤ (s.value i).den := by
    have := Rat.num_div_den (s.value i)
    have hd : (0 : ℚ) < (s.value i).den := by exact_mod_cast (s.value i).den_pos
    have h2 : ((s.value i).num : ℚ) ≤ (s.value i).den := by
      rw [← this, div_le_one hd] at h1; exact h1
    exact_mod_cast h2
  refine ⟨h0, ?_, by omega⟩
  have : (s.value i).num.toNat ≤ (s.value i).den := by omega
  omega

/-- **sanity 4**: consistency with the decision problem. -/
theorem ssgDecision_iff_value_proved (G : Game n) (s : Solution n) (h : IsSolution G s) :
    SSGDecision G ↔ WellFormed G ∧ StoppingGame G ∧ 1 / 2 ≤ s.value G.startNode := by
  unfold SSGDecision
  refine and_congr Iff.rfl (and_congr_right fun hs => ?_)
  rw [valueAtLeastHalf_iff G hs s.value (isSolution_value_stable G hs s h)]
  constructor <;> intro h' <;> linarith

end SSG
