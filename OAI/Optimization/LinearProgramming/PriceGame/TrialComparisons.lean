-- Ported verbatim (modulo toolchain fixes) from the openai_math repository, Apache-2.0. See LICENSE, NOTICE, PORTED_FILES.md.
module

public import OAI.Optimization.LinearProgramming.PriceGame.Experts
public import OAI.Optimization.LinearProgramming.PriceGame.StatesOracle

@[expose] public section

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States

variable {N ne R : ℕ} {anchor : Fin N}

/-- The selected experts agree with the hidden costs at every comparison actually made
by the current trial. Comparisons outside the trial's log impose no restriction. -/
def LoggedComparisons (h : Hidden N R anchor) (experts : Fin ne → Expert N)
    (sel : Skeleton N → Fin ne) (ps : List (Probe N)) : Prop :=
  ∀ p ∈ ps, ∀ sk, sk.positive = h.positive → ∀ t ∈ sk.testsAt p,
    compare (featureValue (experts (sel sk)).raw t.feature) t.threshold =
      compare (featureValue (priority h) t.feature) t.threshold

theorem LoggedComparisons.mono {h : Hidden N R anchor} {experts : Fin ne → Expert N}
    {sel : Skeleton N → Fin ne} {smaller larger : List (Probe N)}
    (keeps : LoggedComparisons h experts sel larger) (sub : ∀ p ∈ smaller, p ∈ larger) :
    LoggedComparisons h experts sel smaller :=
  fun p hp => keeps p (sub p hp)

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
