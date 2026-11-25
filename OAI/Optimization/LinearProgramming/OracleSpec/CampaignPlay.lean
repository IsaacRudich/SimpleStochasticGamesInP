-- Ported verbatim (modulo toolchain fixes) from the openai_math repository, Apache-2.0. See LICENSE, NOTICE, PORTED_FILES.md.
module

public import OAI.Optimization.LinearProgramming.OracleSpec.PriceRealization
public import OAI.Optimization.LinearProgramming.PriceGame.ControlExchanges

@[expose] public section

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec

variable {N : ℕ} {α : Type*}
open PriceGame

/-- The independently specified interleaving of public replies and the source
algorithm emit the same words, in the same order, against every adaptive oracle. -/
theorem serializedPlay_eq_wirePlay (reply : Transcript → Word → Bool)
    (p : Computation N α) (hist : Transcript) :
    serializedPlay reply p hist = Control.wirePlay reply p hist := by
  induction p generalizing hist with
  | pure => rfl
  | ask q next ih => exact ih _ _

end OracleSpec
end LinearProgramming
end Optimization
end OAI
