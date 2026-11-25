module

public import SSGinP.Search.Decision

@[expose] public section

/-!
# SSGinP.Bridge.Corr: `corrGe` / `corrGt`

The two correctness statements of the price machine with the SSG reply as oracle, used by `SSGinP.Main`.
-/

namespace SSGinP

open SSG SSG28Reply SSG28Search SSG28Decode
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.ExactQuantumFactoring.BitStackProgram

open Classical in
theorem corrGe (n : ℕ) (G : Game n) (h : OAI.Optimization.LinearProgramming.OracleSpec.Transcript) (out : Word)
    (hpost : pricePost (N := 2 * n + 1) (rR n) (dummy n) h out)
    (hans : ∀ e ∈ h, e.2 = [ssgReply G (thetaGe n) (rDelta n) e.1]) : out = [decide (SSGDecision G)] := by
  obtain ⟨b, rfl, hb⟩ := machine_output G (thetaGe n) (ValueAtLeastHalf G)
    (fun hs => ⟨(gapGe G hs).1, by rw [(gapGe G hs).2, valueAtLeastHalf_iff G hs (val G hs) (val_fix G hs)]⟩)
    h out hpost hans
  congr 1
  rw [Bool.eq_iff_iff, hb, decide_eq_true_iff]; rfl

open Classical in
theorem corrGt (n : ℕ) (G : Game n) (h : OAI.Optimization.LinearProgramming.OracleSpec.Transcript) (out : Word)
    (hpost : pricePost (N := 2 * n + 1) (rR n) (dummy n) h out)
    (hans : ∀ e ∈ h, e.2 = [ssgReply G (thetaGt n) (rDelta n) e.1]) : out = [decide (SSGDecisionStrict G)] := by
  obtain ⟨b, rfl, hb⟩ := machine_output G (thetaGt n) (ValueGreaterHalf G)
    (fun hs => ⟨(gapGt G hs).1, by rw [(gapGt G hs).2, valueGreaterHalf_iff G hs (val G hs) (val_fix G hs)]⟩)
    h out hpost hans
  congr 1
  rw [Bool.eq_iff_iff, hb, decide_eq_true_iff]; rfl

end SSGinP
