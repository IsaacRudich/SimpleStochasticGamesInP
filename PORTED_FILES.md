# PORTED_FILES

The files under `OAI/` are taken from the `lean/` directory of the openai/math repository
(https://github.com/openai/math, Apache-2.0, authors: OpenAI; written for Lean 4.34.1), same relative paths, module
names unchanged (`OAI.*`). They are the import closure of `OAI/Optimization/LinearProgramming/PriceGame/ExtremalSign.lean`
(398 files). `OAI/PortCompat.lean` is not from that repository (see below). Every ported file starts with a one-line
attribution comment. Licence and attribution: `LICENSE`, `NOTICE`.

The port was done in two stages: first to Lean 4.33 / Mathlib v4.33 (stage 1), then to Lean 4.35.0 / Mathlib v4.35.0
with Lean's module system (stage 2, this repository). No statement of a ported theorem and no ported definition was
changed in either stage, with the one renaming noted in stage 2.

## Stage 1 modifications (Lean 4.34.1 -> Lean 4.33 / Mathlib v4.33, carried over unchanged)

This is the log of the first port, kept as written. The helper lists it names (`tools_D2/…`, `round28/…`) are
working files of that port and are not part of this repository.

- import Mathlib.Basic.Real.Basic -> Mathlib.Data.Real.Basic: PriceGame/LearningPaths.lean, PriceGame/PhasesSegment.lean
- import Mathlib.Tactic -> 14 tactic modules (disk: full Mathlib.Tactic needs ~1000 extra Mathlib modules): files in round28/tools_D2/tactic_bundle_files.txt
- PriceGame/MomentLocal.lean: lemma sub_sq_le_log_one_add reproved without Complex.LogBounds (statement unchanged).
- New file OAIPort/OAI/PortCompat.lean (ours): ite_eq_left / ite_eq_right shims.

### Further fixes (log, in order)
- LearningExperts.lean += import Mathlib.Data.Finset.Sort; MomentTrial.lean convert->refine
- - import Mathlib (39 files, list tools_D2/mathlib_full_files.txt) -> OAI.PortCompat + 51-module bundle (tools_D2/bigbundle.txt)
- Optimization/LinearProgramming/PriceGame/LearningBits.lean Optimization/LinearProgramming/PriceGame/LearningOrderingReference.lean Optimization/LinearProgramming/PriceGame/MarketAugmentReal.lean += EXTRA2 imports; BitStackLists convert length goals; PortCompat += List.nodup_iff_length_dedup_eq
- BitStackQuotation: convert length goals (5 sites); MarketAugmentReal += import Mathlib.Data.Rat.BigOperators
- Computability/*: after each 'convert h using k' line: all_goals try (simp only [length lemmas]; omega)
- BitStackNaturals += import Mathlib.Data.Nat.SuccPred
- Optimization/*: same convert side-goal line; LearningPathMachine, MarketInputsMachine += import Mathlib.Algebra.BigOperators.Fin
- PriceUniform += import Mathlib.Algebra.Polynomial.Degree.Definitions
- PriceUniform: import Mathlib.Algebra.Polynomial.Degree.Support (instead of Degree.Definitions)
- Rule used for `convert h using k` (Computability/ and Optimization/): the next line closes leftover Nat length side goals with `all_goals try (first | omega | (simp only [length lemmas]; omega))`, marked PORT NOTE (D2).

## Stage 2 modifications (Lean 4.33 -> Lean 4.35.0 / Mathlib v4.35.0, module system)

Mechanical, applied by script to all 399 files:
- `module` header inserted after the attribution comment; every `import X` became `public import X`; the line
  `@[expose] public section` inserted after the imports.
- The attribution comment now points to `LICENSE, NOTICE, PORTED_FILES.md`.
- Mathlib modules that moved: `Mathlib.Computability.TMComputable` -> `Mathlib.Computability.TuringMachine.Computable`
  (37 files), `Mathlib.Data.Real.Basic` -> `Mathlib.Basic.Real.Basic` (5 files; in two of them, `LearningPaths.lean` and
  `PhasesSegment.lean`, this restores the original import), `Mathlib.Data.Nat.SuccPred` -> `Mathlib.Order.SuccPred.Nat`, `Mathlib.Data.Prod.Lex` ->
  `Mathlib.Order.Prod.Lex.Basic`, `Mathlib.Data.Rat.Star` -> `Mathlib.Algebra.Order.Star.Rat`,
  `Mathlib.Logic.Basic` -> `Mathlib.Basic.Logic.Basic` (PortCompat only).
- The modifier `private` was removed from every declaration (763 declarations in 182 files: 460 theorems, 205 defs,
  94 abbrevs, 3 structures, 1 opaque). Reason: with the module system a private declaration cannot be used in the
  body of an exposed definition or in a public statement of the same file. Names and bodies are unchanged, with one
  exception (next section).

By hand:
- `OAI/Optimization/LinearProgramming/PriceGame/ControlScanMachine.lean`: the formerly private `leftP` is renamed
  `scanLeftP` (2 occurrences, both in that file), because `ControlCampaignFields.lean` has a public `leftP` in the
  same namespace.
- `OAI/Optimization/LinearProgramming/PriceGame/ChargingState.lean`, proof of `charge_state_node`: the argument `x`
  of `fails_iff_exists_miss` is written out instead of `_` (on Lean 4.35 the unifier ran out of heartbeats). Statement
  unchanged.
- `OAI/Computability/QuantumFactoring/BitStackListIndex.lean`, definition `Procedure.listDrop`: the local `step` no
  longer ends with `.congrFun (by intro x;rfl)` (an identity step; on Lean 4.35 the tactic block was stuck on a
  metavariable). The type of `listDrop` is unchanged.
- `OAI/PortCompat.lean` (ours, not from openai/math): the six stage 1 shims (`ite_eq_left`, `ite_eq_right`,
  `dite_eq_left`, `dite_eq_right`, `Finset.prod_le_prod₀`, `List.nodup_iff_length_dedup_eq`) are removed, because
  Lean 4.35 / Mathlib v4.35.0 have these names; the file now only carries its three imports.

Left as they are: the stage 1 changes (the `PORT NOTE (D2)` lines after `convert`, the reproved lemma in
`MomentLocal.lean`, the explicit Mathlib import lists replacing `import Mathlib`). They compile on 4.35.

Comparison with upstream (25 November 2026): the 398 files were compared, by script, with `lean/` at openai/math
commit `3344da59991ed94f9ba711217b29c1d760badfa6`. Ignoring blank lines, import lines, the `module` / section
header lines, `PORT NOTE` lines and the word `private`, the only differences are the attribution comment (every
file), the three hand changes above, the lemma in `MomentLocal.lean`, the `convert` -> `refine` line in
`MomentTrial.lean`, and, not logged earlier, `prod_le_prod` -> `prod_le_prod'` in one proof each of
`LearningCells.lean` and `LearningExperts.lean`.

## Files (398 = closure of PriceGame/ExtremalSign.lean)
OAI/Computability/QuantumFactoring/BitStackAdder.lean
OAI/Computability/QuantumFactoring/BitStackBasicProcedures.lean
OAI/Computability/QuantumFactoring/BitStackBinaryBasics.lean
OAI/Computability/QuantumFactoring/BitStackBooleans.lean
OAI/Computability/QuantumFactoring/BitStackChoice.lean
OAI/Computability/QuantumFactoring/BitStackComposition.lean
OAI/Computability/QuantumFactoring/BitStackConstants.lean
OAI/Computability/QuantumFactoring/BitStackDivision.lean
OAI/Computability/QuantumFactoring/BitStackFold.lean
OAI/Computability/QuantumFactoring/BitStackFrames.lean
OAI/Computability/QuantumFactoring/BitStackGCD.lean
OAI/Computability/QuantumFactoring/BitStackIncrement.lean
OAI/Computability/QuantumFactoring/BitStackIntegers.lean
OAI/Computability/QuantumFactoring/BitStackIteration.lean
OAI/Computability/QuantumFactoring/BitStackListCode.lean
OAI/Computability/QuantumFactoring/BitStackListFold.lean
OAI/Computability/QuantumFactoring/BitStackListIndex.lean
OAI/Computability/QuantumFactoring/BitStackListLength.lean
OAI/Computability/QuantumFactoring/BitStackListOps.lean
OAI/Computability/QuantumFactoring/BitStackLists.lean
OAI/Computability/QuantumFactoring/BitStackMultiplier.lean
OAI/Computability/QuantumFactoring/BitStackNaturals.lean
OAI/Computability/QuantumFactoring/BitStackProcedures.lean
OAI/Computability/QuantumFactoring/BitStackProducts.lean
OAI/Computability/QuantumFactoring/BitStackPrograms.lean
OAI/Computability/QuantumFactoring/BitStackQuotation.lean
OAI/Computability/QuantumFactoring/BitStackRationalDivision.lean
OAI/Computability/QuantumFactoring/BitStackRationalFloor.lean
OAI/Computability/QuantumFactoring/BitStackRationals.lean
OAI/Computability/QuantumFactoring/BitStackRelabel.lean
OAI/Computability/QuantumFactoring/BitStackSubtractor.lean
OAI/Computability/QuantumFactoring/BitStackSums.lean
OAI/Computability/QuantumFactoring/BitStackTabulate.lean
OAI/Computability/QuantumFactoring/BitStackUnary.lean
OAI/Computability/QuantumFactoring/BitStackWords.lean
OAI/Computability/QuantumFactoring/Procedure.lean
OAI/Computability/QuantumFactoring/ProcedureFurther.lean
OAI/Optimization/LinearProgramming/OracleSpec/Arithmetic.lean
OAI/Optimization/LinearProgramming/OracleSpec/ArithmeticEncoding.lean
OAI/Optimization/LinearProgramming/OracleSpec/BitStack.lean
OAI/Optimization/LinearProgramming/OracleSpec/BitStackDeployment.lean
OAI/Optimization/LinearProgramming/OracleSpec/CampaignPlay.lean
OAI/Optimization/LinearProgramming/OracleSpec/Compiler.lean
OAI/Optimization/LinearProgramming/OracleSpec/CompilerIO.lean
OAI/Optimization/LinearProgramming/OracleSpec/CompilerProof.lean
OAI/Optimization/LinearProgramming/OracleSpec/Dialogue.lean
OAI/Optimization/LinearProgramming/OracleSpec/DialogueDeployment.lean
OAI/Optimization/LinearProgramming/OracleSpec/DialogueProof.lean
OAI/Optimization/LinearProgramming/OracleSpec/GuardedIteration.lean
OAI/Optimization/LinearProgramming/OracleSpec/Machine.lean
OAI/Optimization/LinearProgramming/OracleSpec/PaddedDialogue.lean
OAI/Optimization/LinearProgramming/OracleSpec/PolynomialFuel.lean
OAI/Optimization/LinearProgramming/OracleSpec/PriceEncoding.lean
OAI/Optimization/LinearProgramming/OracleSpec/PriceGame.lean
OAI/Optimization/LinearProgramming/OracleSpec/PriceRealization.lean
OAI/Optimization/LinearProgramming/OracleSpec/PriceUniform.lean
OAI/Optimization/LinearProgramming/OracleSpec/SessionBound.lean
OAI/Optimization/LinearProgramming/OracleSpec/UnaryBootstrap.lean
OAI/Optimization/LinearProgramming/PriceGame/Campaign.lean
OAI/Optimization/LinearProgramming/PriceGame/CampaignRecovery.lean
OAI/Optimization/LinearProgramming/PriceGame/CampaignRounds.lean
OAI/Optimization/LinearProgramming/PriceGame/CampaignWeightCost.lean
OAI/Optimization/LinearProgramming/PriceGame/CatalogueGrid.lean
OAI/Optimization/LinearProgramming/PriceGame/Charging.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingActualProbe.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingColdLists.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingColdOrder.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingColdRanges.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingColdSkeletons.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingDeep.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingExpertsAllocation.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingFeedback.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingInduction.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingProbe.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingQuantile.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingRecordedAllocation.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingSampling.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingSamplingBand.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingSkeleton.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingState.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingTransfer.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingTransferScores.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingTransferSplit.lean
OAI/Optimization/LinearProgramming/PriceGame/ChargingTrial.lean
OAI/Optimization/LinearProgramming/PriceGame/Complexity.lean
OAI/Optimization/LinearProgramming/PriceGame/Computation.lean
OAI/Optimization/LinearProgramming/PriceGame/ComputationIO.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlAssemblyDeploy.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlAssemblyLoops.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlAssemblyMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlAssemblySpec.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlAssemblyValue.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlAssemblyWire.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlBoundedFeedback.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaign.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignArrayBounds.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignCommon.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignData.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignDriver.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignFields.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignGuardIntersection.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignGuarded.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignInit.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignInner.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignInnerRoot.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignInnerType.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignMarked.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignMarkedSource.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignNative.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignPhysical.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignPhysicalComplete.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignPower.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignReplay.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignSafe.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignScoreGuard.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignSourceRuns.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignTrace.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignTransition.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignTrialMarks.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignVotes.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignWeights.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignWireBounds.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignWireCursor.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignWireGuard.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignWireHistory.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCampaignWirePolynomial.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCollapseMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlCollapseRefines.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlData.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlDispatchMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlEncoding.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlEncodingBounds.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlEncodingGuard.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlEncodingPackets.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlEncodingPad.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlEncodingPopulation.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlEncodingShape.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlEncodingState.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlEndpoint.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlEntryMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlExchanges.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlFeedback.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlFeedbackMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlFeedbackOrder.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlFeedbackRefines.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlGuardDeterminism.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlLeafAddresses.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlLeafMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlLeafTags.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlListMedian.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlListMedianOrder.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlPhaseMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlPhysicalPhase.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlPrefix.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlPrepareBids.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlPrepareBudget.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlPrepareConcrete.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlPrepareFrame.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlPrepareProgram.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlPrepareReadout.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlPrepareSemantics.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlPrepareTableSpec.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlPrepareTables.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlPrepareWeightsMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlRatListSum.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlReplayBound.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlReplayBox.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlReplayLoop.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlReplayMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlReplaySource.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlReplaySourceWidth.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlReplayWidth.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlScalarMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlScanMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlScoreQuantize.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlSession.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlSign.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialArrayTree.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialAssemble.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialCore.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialCost.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialEnvelope.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialFinish.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialFinishCorrect.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialFinishMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialGainMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialGainWire.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialGuarded.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialLiveKernel.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialLiveParts.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialMarked.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialMarkedSchedule.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialNative.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialNativeBase.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialNativeCorrect.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialPackets.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialPrepare.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialRefinement.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialRefinementBase.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialResultWire.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialRoundWidth.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialScan.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialSchedule.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialSchedulePrefix.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialSourceCaps.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialSourceGuarded.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialSourceMarks.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialSourceNode.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialSourceWeight.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialSourceWire.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialStepData.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialStepFeedback.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialStepMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialStepPhases.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialStepWire.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialUniform.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlTrialWeightWire.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlWeightFolds.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlWire.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlWireCampaign.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlWireCombined.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlWireFormula.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlWireState.lean
OAI/Optimization/LinearProgramming/PriceGame/ControlWireTrial.lean
OAI/Optimization/LinearProgramming/PriceGame/Experts.lean
OAI/Optimization/LinearProgramming/PriceGame/ExtremalSign.lean
OAI/Optimization/LinearProgramming/PriceGame/FixedShare.lean
OAI/Optimization/LinearProgramming/PriceGame/FixedShareActualAllReplies.lean
OAI/Optimization/LinearProgramming/PriceGame/FixedShareActualBounds.lean
OAI/Optimization/LinearProgramming/PriceGame/FixedShareCombinedWire.lean
OAI/Optimization/LinearProgramming/PriceGame/FixedShareCursorWire.lean
OAI/Optimization/LinearProgramming/PriceGame/FixedSharePopulationWire.lean
OAI/Optimization/LinearProgramming/PriceGame/FixedShareScore.lean
OAI/Optimization/LinearProgramming/PriceGame/Learning.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningAdaptive.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningAddressMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningArityMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningBatchMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningBits.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningCatalog.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningCellMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningCells.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningConstraints.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningCount.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningCutCode.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningCutMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningExperts.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningFoldMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningGenerationCost.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningGenerationCostComplete.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningGenerationCostHistorical.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningGenerationCostObservations.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningGenerationCostOrdering.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningGenerationCostSolver.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningGenerationCostSource.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningGeneratorWire.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningGroupingIndex.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningGroupingList.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningGroupingRows.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningGroupingSort.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningGroupingSupport.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningOrderingReference.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningPackedNormalize.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningPackedTestMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningPackedTests.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningPathCost.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningPathMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningPaths.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningPolynomial.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningPool.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningRawMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningRepresentatives.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningReset.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningSelections.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningSkeleton.lean
OAI/Optimization/LinearProgramming/PriceGame/LearningVecMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/Majority.lean
OAI/Optimization/LinearProgramming/PriceGame/Market.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketActionsMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketAugmentBits.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketAugmentMachineAmplitude.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketAugmentMachineBridge.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketAugmentMachineCodec.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketAugmentMachineEncoding.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketAugmentMachineRun.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketAugmentMachineSolution.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketAugmentMachineStep.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketAugmentMachineTerminal.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketAugmentPath.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketAugmentReal.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketAugmentRoutes.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketAugmentSolver.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketAugmentUnit.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketBid.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketBinary.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketBitStack.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketBitStackBridge.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketBitStackCanonical.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketBitStackCanonicalCore.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketBitStackInput.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketBitStackReadout.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketBitStackTable.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketClearMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketCompute.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketContextMap.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketDenominator.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketExecutablePrices.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketExistence.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketFlowMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketFlowMachineAllocation.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketFlowMachineAllocationSpec.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketFlowMachineCanonicalOutput.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketFlowMachineGraph.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketFlowMachineModel.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketFlowMachineOutput.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketFlowMachineOutputProgram.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketFlowMachineOutputSpec.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketFlowMachinePaths.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketFlowMachineRows.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketGraph.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketGrid.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketInitializeBridge.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketInitializeMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketInputSize.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketInputsMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketLCMMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketNumberBounds.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketOptimum.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketOptimumDual.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketOutputsMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketPotentials.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketPotentialsCost.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketScheduleMachine.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketSchedulePadding.lean
OAI/Optimization/LinearProgramming/PriceGame/MarketSolverBounds.lean
OAI/Optimization/LinearProgramming/PriceGame/Model.lean
OAI/Optimization/LinearProgramming/PriceGame/Moment.lean
OAI/Optimization/LinearProgramming/PriceGame/MomentConstants.lean
OAI/Optimization/LinearProgramming/PriceGame/MomentGroups.lean
OAI/Optimization/LinearProgramming/PriceGame/MomentLocal.lean
OAI/Optimization/LinearProgramming/PriceGame/MomentLocalCost.lean
OAI/Optimization/LinearProgramming/PriceGame/MomentRational.lean
OAI/Optimization/LinearProgramming/PriceGame/MomentScoreBound.lean
OAI/Optimization/LinearProgramming/PriceGame/MomentThreshold.lean
OAI/Optimization/LinearProgramming/PriceGame/MomentTrial.lean
OAI/Optimization/LinearProgramming/PriceGame/OracleTrialCount.lean
OAI/Optimization/LinearProgramming/PriceGame/Phases.lean
OAI/Optimization/LinearProgramming/PriceGame/PhasesIds.lean
OAI/Optimization/LinearProgramming/PriceGame/PhasesOrder.lean
OAI/Optimization/LinearProgramming/PriceGame/PhasesSegment.lean
OAI/Optimization/LinearProgramming/PriceGame/PhasesTrace.lean
OAI/Optimization/LinearProgramming/PriceGame/QueryWire.lean
OAI/Optimization/LinearProgramming/PriceGame/RecursiveRecovery.lean
OAI/Optimization/LinearProgramming/PriceGame/Schedule.lean
OAI/Optimization/LinearProgramming/PriceGame/Skeletons.lean
OAI/Optimization/LinearProgramming/PriceGame/States.lean
OAI/Optimization/LinearProgramming/PriceGame/StatesChargingScores.lean
OAI/Optimization/LinearProgramming/PriceGame/StatesCommunication.lean
OAI/Optimization/LinearProgramming/PriceGame/StatesCost.lean
OAI/Optimization/LinearProgramming/PriceGame/StatesFeedback.lean
OAI/Optimization/LinearProgramming/PriceGame/StatesMass.lean
OAI/Optimization/LinearProgramming/PriceGame/StatesOracle.lean
OAI/Optimization/LinearProgramming/PriceGame/StatesReachable.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialCachedGrid.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialComparisons.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecution.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionAssemble.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionAssembleFacts.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionCharge.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionChargeView.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionChildren.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionComplexity.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionInduction.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionMarket.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionMarketBounds.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionPackets.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionReaches.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionSchedule.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionSize.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionStep.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionTypes.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionWeightCost.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionWeightSize.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialExecutionWeights.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialLogDepth.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialMarketDataBounds.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialMarketFractionSize.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialPathGrid.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialQueryArithmetic.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialQueryGrid.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialQueryTraces.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialRecursiveWeightBounds.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialWeightArithmetic.lean
OAI/Optimization/LinearProgramming/PriceGame/TrialWireBound.lean
OAI/Optimization/LinearProgramming/PriceGame/VertexEncoding.lean
OAI/Optimization/LinearProgramming/PriceGame/WeightCapPolynomial.lean
OAI/Optimization/LinearProgramming/RAM/Basic.lean
