module

public import SSGinP.Search.Search
public import OAI.Optimization.LinearProgramming.PriceGame.ExtremalSign
public import OAI.Optimization.LinearProgramming.OracleSpec.PriceEncoding

@[expose] public section

/-!
# SSGinP.Search.SingleCall: one run of the ported sign-recovery BIT MACHINE decides `θ < v k`

`wordReply` answers a raw query word with `SSG28Search.label` of the decoded query
(decoding by the ported `priceQuery_injective`); malformed words get `false`.
`single_call_correct`: any halting transcript satisfying `pricePost` whose answers come from
`wordReply` outputs `[decide (θ < v k)]` (gap promise `|v k - θ| ≥ Δ`).
`single_call_machine`: the fixed ported BitProgram `p` of `extremalSignRecovery`, run on input
`priceInput R (dummy n)` with oracle `wordReply`, halts within
`coefficient * (2n+1 + log2 (R+1) + 1)^degree` bit steps with output `[decide (θ < v k)]`.
-/

namespace SSG28Search

open OAI.Optimization.LinearProgramming OracleSpec

variable {n : ℕ} {C : Cone n} {δ θ Δ : ℚ} {k : Fin n} {K T R : ℕ}

open Classical in
/-- The word-level reply. -/
noncomputable def wordReply (C : Cone n) (δ θ : ℚ) (k : Fin n) (w : Word) : Bool :=
  if h : ∃ iq : Fin (2*n+1) × (Fin (2*n+1) → ℚ), priceQuery iq.1 iq.2 = w then
    label C δ θ k h.choose.1 h.choose.2
  else false

theorem wordReply_priceQuery (C : Cone n) (δ θ : ℚ) (k : Fin n) (i : Fin (2*n+1))
    (q : Fin (2*n+1) → ℚ) : wordReply C δ θ k (priceQuery i q) = label C δ θ k i q := by
  have h : ∃ iq : Fin (2*n+1) × (Fin (2*n+1) → ℚ), priceQuery iq.1 iq.2 = priceQuery i q :=
    ⟨(i, q), rfl⟩
  have hc := (priceQuery_injective.mp h.choose_spec)
  simp only [wordReply, h, dif_pos]
  rw [hc.1, hc.2]

theorem single_call_correct (P : Params C δ Δ K T) (hR : 2 * K ≤ R)
    (gap : θ + Δ ≤ C.v k ∨ C.v k ≤ θ - Δ) (history : Transcript) (output : Word)
    (hpost : pricePost R (dummy n) history output)
    (hans : ∀ e ∈ history, e.2 = [wordReply C δ θ k e.1]) :
    output = [decide (θ < C.v k)] := by
  have hδ := P.hδ
  have hΔ : 0 < Δ := by
    have := P.hΔ
    have : (0:ℚ) < 2 * δ * ((T:ℚ) + 1) := by positivity
    linarith
  rcases gap with hk | hk
  · have hdec : decide (θ < C.v k) = true := by simp only [decide_eq_true_eq]; linarith
    rw [hdec]
    refine hpost.2.2 true Set.univ (costPos C δ K T) (Set.mem_univ _)
      (fun j _ => (costPos_le P j).trans hR) ?_
    intro i prices answer hmem _ hmin
    have ha : answer = [wordReply C δ θ k (priceQuery i prices)] := hans _ hmem
    rw [ha, wordReply_priceQuery]
    rw [pos_consistent P hk i prices (fun g => hmin g (Set.mem_univ g))]
  · have hdec : decide (θ < C.v k) = false := by
      simp only [decide_eq_false_iff_not, not_lt]; linarith
    rw [hdec]
    refine hpost.2.2 false Set.univ (costNeg C δ K T) (Set.mem_univ _)
      (fun j _ => (costNeg_le P j).trans hR) ?_
    intro i prices answer hmem _ hmin
    have ha : answer = [wordReply C δ θ k (priceQuery i prices)] := hans _ hmem
    rw [ha, wordReply_priceQuery]
    rw [neg_consistent P hk i prices (fun g => hmin g (Set.mem_univ g))]

/-- Every exchange recorded by a run with a query-only oracle carries that oracle's answer. -/
theorem run_transcript_answers (p : BitProgram) (r : Word → Bool) {c c' : p.Config} {m : ℕ}
    (h : p.Run (fun _ w => [r w]) c m c') (h0 : ∀ e ∈ c.transcript, e.2 = [r e.1]) :
    ∀ e ∈ c'.transcript, e.2 = [r e.1] := by
  induction h with
  | refl => exact h0
  | @step c c₁ c₂ m₁ k₁ htick _ ih =>
    apply ih
    intro e he
    unfold BitProgram.tick at htick
    cases hpc : c.pc with
    | none => simp [hpc] at htick
    | some q =>
      simp only [hpc, Option.bind_eq_bind, Option.bind_some] at htick
      split at htick <;> simp only [Option.some.injEq, Prod.mk.injEq, pure] at htick <;>
        obtain ⟨-, rfl⟩ := htick
      all_goals first
        | exact h0 e he
        | (simp only [List.mem_cons] at he
           rcases he with rfl | he
           · rfl
           · exact h0 e he)

/-- **S5, machine level.** The ported fixed bit machine, asked with our word replies, decides
`θ < v k` within its polynomial clock. -/
theorem single_call_machine :
    ∃ (p : BitProgram) (coefficient degree : ℕ),
      ∀ (n : ℕ) (C : Cone n) (δ θ Δ : ℚ) (k : Fin n) (K T R : ℕ),
        Params C δ Δ K T → 2 * K ≤ R → 0 < R →
        (θ + Δ ≤ C.v k ∨ C.v k ≤ θ - Δ) →
        p.ComputesWithin (fun _ w => [wordReply C δ θ k w]) (priceInput R (dummy n))
          (coefficient * (2*n+1 + (R + 1).log2 + 1) ^ degree)
          (fun _ out => out = [decide (θ < C.v k)]) := by
  obtain ⟨p, coefficient, degree, hp⟩ := PriceGame.extremalSignRecovery
  refine ⟨p, coefficient, degree, ?_⟩
  intro n C δ θ Δ k K T R P hR hR0 gap
  obtain ⟨elapsed, c, hrun, hle, hhalt, hpost⟩ :=
    hp (2*n+1) R (by omega) hR0 (dummy n) (fun _ w => wordReply C δ θ k w)
  refine ⟨elapsed, c, hrun, hle, hhalt, ?_⟩
  have hans := run_transcript_answers p (wordReply C δ θ k) hrun (by
    intro e he; simp [BitProgram.initial] at he)
  exact single_call_correct P hR gap _ _ hpost hans

end SSG28Search
