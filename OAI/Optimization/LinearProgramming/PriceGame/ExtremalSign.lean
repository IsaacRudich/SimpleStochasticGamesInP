-- Ported verbatim (modulo toolchain fixes) from the openai_math repository, Apache-2.0. See LICENSE, NOTICE, PORTED_FILES.md.
module

public import OAI.Optimization.LinearProgramming.PriceGame.ControlEndpoint
public import OAI.Optimization.LinearProgramming.PriceGame.ControlDispatchMachine

@[expose] public section

/-! # The anchored hidden-sign oracle algorithm (Theorem 1.3). -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame

/-- One fixed finite bit program recovers the hidden sign on every valid adaptive
transcript and obeys the same polynomial internal bit clock for every possible reply. -/
theorem extremalSignRecovery : OracleSpec.ExtremalSignRecovery :=
  Control.extremalSignRecovery_of_campaignProcedure Control.Native.dispatchProcedure

end PriceGame
end LinearProgramming
end Optimization
end OAI
