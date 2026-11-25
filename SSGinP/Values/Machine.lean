module

public import SSGinP.Values.Engine

@[expose] public section

/-!
# SSGinP.Values.Machine: the engine calls as runs of the ported BIT MACHINE

Same procedure `SSGValues.solveWith`, with every threshold test "is the value of node `k` greater than `θ`?"
answered by one halting run of the fixed ported bit machine of `extremalSignRecovery` (openai_math), on the
public input `priceInput (128·27^n) (dummy n)` and with the oracle `ssgReply (withStart G k) θ (1/(64·27^n))`
(one evaluation of `F G` at one node per query; all replies `false` if `G` is not a well-formed Stopping Game).

* `run_det`          : halting runs of a bit machine are unique.
* `solve_by_machine` : one fixed machine `p` and constants `coefficient`, `degree` such that for every game `G`
                       on `n` nodes, every node `k` and every rational `θ` the run halts within
                       `coefficient · (7n+10)^degree` bit steps (all query and answer bits included) with a
                       one-bit output; and if `G` is a well-formed Stopping Game, then feeding these output bits
                       to `solveWith` returns the values of all nodes and optimal strategies (`= solve G`).
-/

namespace SSGValues

open SSG SSG28Search SSG28Reply OAI.Optimization.LinearProgramming OracleSpec PriceGame

variable {n : ℕ}

theorem tick_none_of_halted (p : BitProgram) (o : WordOracle) (c : p.Config) (h : c.pc = none) :
    p.tick o c = none := by
  unfold BitProgram.tick; simp [h]

/-- halting runs are unique. -/
theorem run_det (p : BitProgram) (o : WordOracle) {c c₁ c₂ : p.Config} {a b : ℕ}
    (h₁ : p.Run o c a c₁) (e₁ : c₁.pc = none) (h₂ : p.Run o c b c₂) (e₂ : c₂.pc = none) : c₁ = c₂ := by
  induction h₁ generalizing b with
  | refl c =>
    cases h₂ with
    | refl => rfl
    | step ht _ => rw [tick_none_of_halted p o _ e₁] at ht; cases ht
  | @step c c' c'' m k ht _ ih =>
    cases h₂ with
    | refl => rw [tick_none_of_halted p o _ e₂] at ht; cases ht
    | step ht' hr' =>
      rw [ht] at ht'
      cases ht'
      exact ih e₁ hr'

/-- the oracle of the call for node `k` and threshold `θ`. -/
noncomputable def callOracle (G : Game n) (k : Fin n) (θ : ℚ) : WordOracle :=
  fun _ w => [ssgReply (withStart G k) θ (rDelta n) w]

/-- correctness of one call: a transcript satisfying the ported postcondition, with our replies, outputs one bit
that is right whenever `|v k - θ| ≥ 1/(4·9^n)`. -/
theorem call_post (G : Game n) (hw : WellFormed G) (hs : StoppingGame G) (v : Fin n → ℚ) (hv : F G v = v)
    (k : Fin n) (θ : ℚ) (history : Transcript) (output : Word)
    (hpost : pricePost (rR n) (dummy n) history output)
    (hans : ∀ e ∈ history, e.2 = [ssgReply (withStart G k) θ (rDelta n) e.1]) :
    ∃ b, output = [b] ∧ (θ + Delta n ≤ v k → b = true) ∧ (v k ≤ θ - Delta n → b = false) := by
  have hs' := stopping_withStart G k hs
  have hw' : WellFormed (withStart G k) := hw
  have hok : okGame (withStart G k) = true := (okGame_iff _).mpr ⟨hw', hs'⟩
  have hr := prank_ranked G (peelAll_of_stoppingGame G hs)
  have ev : val (withStart G k) hs' = v :=
    fix_unique G (prank G) hr _ v (by have := val_fix (withStart G k) hs'; rwa [F_withStart] at this) hv
  have e : (ssgCone (withStart G k) hs').v k = v k := congrFun ev k
  have hΔ : 0 < Delta n := by unfold Delta; positivity
  have hans' : ∀ e ∈ history,
      e.2 = [wordReply (ssgCone (withStart G k) hs') (rDelta n) θ k e.1] := by
    intro e he; rw [hans e he, ssgReply_eq_wordReply (withStart G k) hs' hok]; rfl
  have key : (θ + Delta n ≤ (ssgCone (withStart G k) hs').v k ∨ (ssgCone (withStart G k) hs').v k ≤ θ - Delta n) →
      output = [decide (θ < v k)] := fun gap => by
    have := single_call_correct (k := k) (params (withStart G k) hs') (le_rfl : 2 * rK n ≤ rR n) gap
      history output hpost hans'
    rw [this, e]
  obtain ⟨b, hb⟩ := hpost.2.1
  refine ⟨b, hb, fun h => ?_, fun h => ?_⟩
  · have := key (Or.inl (by rw [e]; exact h))
    rw [hb] at this
    have hb' : b = decide (θ < v k) := by simpa using this
    rw [hb', decide_eq_true_iff]; linarith
  · have := key (Or.inr (by rw [e]; exact h))
    rw [hb] at this
    have hb' : b = decide (θ < v k) := by simpa using this
    rw [hb', decide_eq_false_iff_not]; linarith

/-- **values and optimal strategies by `n (2n+1)` runs of the ported bit machine.** -/
theorem solve_by_machine :
    ∃ (p : BitProgram) (coefficient degree : ℕ), ∀ (n : ℕ) (G : Game n),
      (∀ (k : Fin n) (θ : ℚ),
        p.ComputesWithin (callOracle G k θ) (priceInput (rR n) (dummy n)) (coefficient * (7 * n + 10) ^ degree)
          (fun h out => (∃ b, out = [b]) ∧
            ∀ e ∈ h, ∃ (i : Fin (2*n+1)) (q : Fin (2*n+1) → ℚ), e.1 = priceQuery i q)) ∧
      (WellFormed G → StoppingGame G → ∀ call : Fin n → ℚ → Bool,
        (∀ (k : Fin n) (θ : ℚ), ∃ (elapsed : ℕ) (c : p.Config),
          p.Run (callOracle G k θ) (p.initial (priceInput (rR n) (dummy n))) elapsed c ∧ c.pc = none ∧
            c.bufferRev.reverse = [call k θ]) →
        solveWith call G = solve G ∧
        ∃ s, solveWith call G = some s ∧ Stable G s.value ∧ IsSolution G s.value s.maxStrategy s.minStrategy) := by
  obtain ⟨p, coefficient, degree, hp⟩ := PriceGame.extremalSignRecovery
  refine ⟨p, coefficient, degree, fun n G => ?_⟩
  have run := fun (k : Fin n) (θ : ℚ) =>
    hp (2*n+1) (rR n) (by omega) (rR_pos n) (dummy n) (fun _ w => ssgReply (withStart G k) θ (rDelta n) w)
  constructor
  · intro k θ
    obtain ⟨el, c, hrun, hle, hhalt, hpost⟩ := run k θ
    refine ⟨el, c, hrun, hle.trans ?_, hhalt, hpost.2.1, hpost.1⟩
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
    have := log_rR n
    omega
  · intro hw hs call hcall
    obtain ⟨v, hv⟩ := stable_point_exists G hs
    have hf : ∀ k, Fuzzy (call k) (v k) (Delta n) := by
      intro k
      have one : ∀ θ, (θ + Delta n ≤ v k → call k θ = true) ∧ (v k ≤ θ - Delta n → call k θ = false) := by
        intro θ
        obtain ⟨el, c, hrun, -, hhalt, hpost⟩ := run k θ
        obtain ⟨el', c', hrun', hhalt', hout'⟩ := hcall k θ
        have hcc : c = c' := run_det p _ hrun hhalt hrun' hhalt'
        have hans := run_transcript_answers p (ssgReply (withStart G k) θ (rDelta n)) hrun (by
          intro e he; simp [BitProgram.initial] at he)
        obtain ⟨b, hb, h1, h2⟩ := call_post G hw hs v hv k θ _ _ hpost hans
        rw [hcc, hout'] at hb
        have hb' : call k θ = b := by simpa using hb
        rw [hb']; exact ⟨h1, h2⟩
      exact ⟨fun θ => (one θ).1, fun θ => (one θ).2⟩
    have h1 := solveWith_complete call G hs v hv hf
    have h2 := solveWith_complete (engineCall G) G hs v hv (engineCall_fuzzy G hs v hv)
    exact ⟨by rw [h1]; exact h2.symm, _, h1, (stable_iff G v).mpr hv, greedy_isSolution G hs v hv⟩


end SSGValues
