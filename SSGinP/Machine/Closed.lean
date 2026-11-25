module

public import OAI.Optimization.LinearProgramming.OracleSpec.Machine

@[expose] public section

/-!
# SSGinP.Machine.Closed: the shared closed-machine predicate

A *closed* `BitProgram` never executes `ask`: no state has an `ask` instruction. Then its runs do not
depend on the oracle (`closed_run_oracle`), so we fix the dummy oracle `noOracle`.
`DecidesWithin p input budget b`: the closed program halts on `input` within `budget` charged steps
with output word `[b]`.
-/

namespace SSG28Closed

open OAI.Optimization.LinearProgramming.OracleSpec

/-- no state of `p` carries an `ask` instruction. -/
def Closed (p : BitProgram) : Prop :=
  ∀ (q : Fin p.states) (o : Option Bool) (next : Fin p.states), p.instruction q o ≠ .ask next

/-- the oracle used to run closed programs (never consulted). -/
def noOracle : WordOracle := fun _ _ => []

/-- `p` halts on `input` within `budget` steps and outputs `[b]`. -/
def DecidesWithin (p : BitProgram) (input : Word) (budget : ℕ) (b : Bool) : Prop :=
  p.ComputesWithin noOracle input budget (fun _ out => out = [b])

/-- a closed program steps identically under every oracle. -/
theorem closed_tick (p : BitProgram) (hp : Closed p) (o o' : WordOracle) (c : p.Config) :
    p.tick o c = p.tick o' c := by
  unfold BitProgram.tick
  cases hpc : c.pc with
  | none => rfl
  | some q =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases h : p.instruction q (c.store (p.scan q)).head? with
    | ask next => exact absurd h (hp _ _ _)
    | _ => rfl

theorem closed_run_oracle (p : BitProgram) (hp : Closed p) (o o' : WordOracle) {c d : p.Config} {n : ℕ}
    (h : p.Run o c n d) : p.Run o' c n d := by
  induction h with
  | refl c => exact .refl c
  | step ht _ ih => exact .step (by rw [← closed_tick p hp o o']; exact ht) ih

end SSG28Closed
