-- Ported verbatim (modulo toolchain fixes) from the openai_math repository, Apache-2.0. See LICENSE, NOTICE, PORTED_FILES.md.
module

public import OAI.Optimization.LinearProgramming.PriceGame.ControlWireCampaign
public import OAI.Optimization.LinearProgramming.PriceGame.ControlWireState
public import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignDriver

@[expose] public section

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open ExactQuantumFactoring.BitStackProgram

/-- The suspended outer loop appears once, followed, in trial mode, by the active stack. -/
def combinedCode : Driver.PC → List Bool
  | .campaign c => false :: campaignCursorCode c
  | .trial c s => true :: prodCode campaignCursorCode stateCode (c,s)

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
