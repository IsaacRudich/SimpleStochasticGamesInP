-- Ported verbatim (modulo toolchain fixes) from the openai_math repository, Apache-2.0. See LICENSE, NOTICE, PORTED_FILES.md.
module

public import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignInit
public import OAI.Optimization.LinearProgramming.PriceGame.ControlWireCombined

@[expose] public section

/-! First-order entry into the complete public campaign. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure

noncomputable def initialPCP : Procedure eiPad Wire.combinedCode (fun i => Driver.PC.campaign
    (startCampaign i.goods i.range i.anchor.val (Campaign.rounds i.goods i.range))) :=
  ((prepend Wire.campaignCursorCode [false]).comp startFromPublicP).result (by intro _; rfl)

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
