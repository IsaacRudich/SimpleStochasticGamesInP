-- Ported verbatim (modulo toolchain fixes) from the openai_math repository, Apache-2.0. See LICENSE, NOTICE, PORTED_FILES.md.
module

public import OAI.PortCompat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Tauto
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.ByContra
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.SimpRw
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Use
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Zify
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NthRewrite
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Lift
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Int.Order.Lemmas
public import Mathlib.Order.Interval.Finset.Nat
public import OAI.Computability.QuantumFactoring.BitStackDivision
public import OAI.Computability.QuantumFactoring.BitStackGCD

@[expose] public section

namespace OAI

section
namespace ExactQuantumFactoring.BitStackProgram

namespace Procedure
noncomputable def gcdStepP : Procedure (prodCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits) gcdStep :=
  (conditional (binaryZero.comp (second Nat.bits Nat.bits))
    (identity (prodCode Nat.bits Nat.bits)) ((second Nat.bits Nat.bits).pair binaryMod)).congrFun
      (by intro x;simp only [gcdStep,Function.comp_apply,id_eq,decide_eq_true_eq])

noncomputable def binaryGcd : Procedure (prodCode Nat.bits Nat.bits) Nat.bits (fun x=>x.1.gcd x.2) := by
  let p:=(gcdStepP.comp gcdStepP).congrFun (g:=gcdRound) (by intro x;rfl)
  let rep:=p.iterate (Polynomial.C 2*Polynomial.X+1) (by
    intro n x i _
    have hh:=gcdRound_iterate_sizeSum i x
    simp only [prodCode,pairBits_length,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one]
    omega)
  let len:=(length.precompose Nat.bits).comp (second Nat.bits Nat.bits)
  exact ((first Nat.bits Nat.bits).comp (rep.comp (len.pair (identity (prodCode Nat.bits Nat.bits))))).congrFun
    (by intro x;exact gcdRound_result x)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
