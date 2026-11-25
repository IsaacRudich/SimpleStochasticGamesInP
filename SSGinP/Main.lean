/- SSGinP.Main: assembly of the two decision statements. -/
module

public import SSGinP.Bridge.EncodeDecode
public import SSGinP.Bridge.Corr
public import SSGinP.Machine.Machine
public import SSGinP.Machine.MachineProcD2Driver
public import SSGinP.Machine.MachineReplyInst
public import Mathlib.Computability.TuringMachine.Computable
public import SSGinP.Bridge.Simulate

@[expose] public section

namespace SSGinP

open SSG SSG28Reply
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.ExactQuantumFactoring.BitStackProgram

/-- the simulation theorem (`SSGinP.Simulate.toProcedure`), as a type. -/
abbrev ToProcedure : Type 1 :=
  ∀ (M : BitProgram) (_ : SSG28Closed.Closed M) (d : ℕ) (g : Word → Bool)
    (_ : ∀ x, SSG28Closed.DecidesWithin M x ((x.length + 2) ^ d) (g x)),
    Procedure (id : Word → Word) Procedure.boolCode g

/-- the word reversal as a procedure on encoded games: `x ↦ (encode x).reverse`. -/
noncomputable def encodeReverse :
    Procedure SSG.encode (id : Word → Word) (fun x => (SSG.encode x).reverse) where
  K := Procedure.reverse.K
  finiteK := Procedure.reverse.finiteK
  decideK := Procedure.reverse.decideK
  input := Procedure.reverse.input
  output := Procedure.reverse.output
  program := Procedure.reverse.program
  bound := Procedure.reverse.bound
  runs := fun x => Procedure.reverse.runs (SSG.encode x)

/-- the generic assembly: a closed machine deciding `∃ n G, decode w = some ⟨n, G⟩ ∧ P G` gives a polynomial-time
Turing machine (Mathlib `TM2ComputableInPolyTime`, all alphabets finite) for `P` on encoded games. -/
theorem inP_of_machine (toProc : ToProcedure) (P : ∀ {n : ℕ}, Game n → Prop)
    (hmach : ∃ (M : BitProgram) (d : ℕ), SSG28Closed.Closed M ∧ ∀ x : Word,
      SSG28Closed.DecidesWithin M x ((x.length + 2) ^ d)
        (@decide (∃ n G, SSG28Decode.decode x = some ⟨n, G⟩ ∧ P G) (Classical.propDecidable _))) :
    ∃ f : (Σ n, Game n) → Bool, (∀ x, f x = true ↔ P x.2) ∧
      ∃ M : Turing.TM2ComputableInPolyTime SSG.encode Computability.encodeBool f, ∀ k, Finite (M.tm.Γ k) := by
  classical
  obtain ⟨M, d, hM, hw⟩ := hmach
  have P1 := toProc M hM d _ hw
  have hf : ∀ x : Σ n, Game n,
      ((fun w : Word => decide (∃ n G, SSG28Decode.decode w = some ⟨n, G⟩ ∧ P G)) ∘
        (fun x => (SSG.encode x).reverse)) x = decide (P x.2) := by
    intro x
    simp only [Function.comp_apply, decode_encode, Option.some.injEq]
    congr 1
    apply propext
    constructor
    · rintro ⟨n, G, h, hP⟩; subst h; exact hP
    · intro hP; exact ⟨x.1, x.2, rfl, hP⟩
  have Pfin : Procedure SSG.encode Procedure.boolCode (fun x : Σ n, Game n => decide (P x.2)) :=
    (P1.comp encodeReverse).congrFun hf
  exact ⟨_, fun x => decide_eq_true_iff, Pfin.toTM2, Pfin.toTM2_finite⟩

/-- **The SSG decision problem is in P** (given `toProc`). -/
theorem ssg_in_P_of (toProc : ToProcedure) :
    ∃ f : (Σ n, Game n) → Bool, (∀ x, f x = true ↔ SSGDecision x.2) ∧
      ∃ M : Turing.TM2ComputableInPolyTime SSG.encode Computability.encodeBool f, ∀ k, Finite (M.tm.Γ k) :=
  inP_of_machine toProc SSGDecision
    (SSG28Machine.machine thetaGe SSGDecision OAI.Optimization.LinearProgramming.PriceGame.extremalSignRecovery
      corrGe SSG28MachineProcD2.driverP SSG28MachineReplyInst.replyGe)

/-- **the strict variant** (given `toProc`). -/
theorem ssgStrict_in_P_of (toProc : ToProcedure) :
    ∃ f : (Σ n, Game n) → Bool, (∀ x, f x = true ↔ SSGDecisionStrict x.2) ∧
      ∃ M : Turing.TM2ComputableInPolyTime SSG.encode Computability.encodeBool f, ∀ k, Finite (M.tm.Γ k) :=
  inP_of_machine toProc SSGDecisionStrict
    (SSG28Machine.machine thetaGt SSGDecisionStrict OAI.Optimization.LinearProgramming.PriceGame.extremalSignRecovery
      corrGt SSG28MachineProcD2.driverP SSG28MachineReplyInst.replyGt)

/-- **The SSG decision problem is in P.** -/
theorem ssg_in_P_proved :
    ∃ f : (Σ n, Game n) → Bool, (∀ x, f x = true ↔ SSGDecision x.2) ∧
      ∃ M : Turing.TM2ComputableInPolyTime SSG.encode Computability.encodeBool f, ∀ k, Finite (M.tm.Γ k) :=
  ssg_in_P_of (fun M hM d g h => Simulate.toProcedure M hM d g h)

/-- **The strict variant (Condon: greater than 1/2) is in P.** -/
theorem ssgStrict_in_P_proved :
    ∃ f : (Σ n, Game n) → Bool, (∀ x, f x = true ↔ SSGDecisionStrict x.2) ∧
      ∃ M : Turing.TM2ComputableInPolyTime SSG.encode Computability.encodeBool f, ∀ k, Finite (M.tm.Γ k) :=
  ssgStrict_in_P_of (fun M hM d g h => Simulate.toProcedure M hM d g h)

end SSGinP


namespace SSG

/-- **The SSG decision problem is in P** (the Challenge statement). -/
theorem ssg_in_P_proved : ∃ f, SolvesSSG f ∧ PTime f := SSGinP.ssg_in_P_proved

/-- **The strict SSG decision problem is in P** (the Challenge statement). -/
theorem ssgStrict_in_P_proved : ∃ f, SolvesSSGStrict f ∧ PTime f := SSGinP.ssgStrict_in_P_proved

end SSG
