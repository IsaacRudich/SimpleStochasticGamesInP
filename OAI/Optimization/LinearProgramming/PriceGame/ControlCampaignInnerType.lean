-- Ported verbatim (modulo toolchain fixes) from the openai_math repository, Apache-2.0. See LICENSE, NOTICE, PORTED_FILES.md.
module

public import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignDriver

@[expose] public section

/-! # Live predicates on the outer and recursive program counters -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Driver

abbrev InnerPredicate := ℕ → ℕ → List PackedExpert → Trial.MachineState → Prop

def InnerHolds (P : InnerPredicate) : PC → Prop
  | .campaign _ => True
  | .trial c s => P c.dimension c.range c.state.population.experts s

end Driver
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
