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
public import OAI.Computability.QuantumFactoring.BitStackChoice
public import OAI.Computability.QuantumFactoring.BitStackNaturals
public import OAI.Computability.QuantumFactoring.BitStackWords

@[expose] public section

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def addCounter (x : ℕ×ℕ) := (x.1,x.1+x.2)
lemma addCounter_iterate (i : ℕ) (x : ℕ×ℕ) :
    addCounter^[i] x=(x.1,i*x.1+x.2) := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply',ih]
    simp only [addCounter,Prod.mk.injEq,true_and,Nat.succ_mul]
    omega

lemma pred_iterate_word (i n : ℕ) : (fun k=>k-1)^[i] n=n-i := by
  induction i with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply',ih,Nat.sub_sub]

namespace Procedure
noncomputable def unaryAdd : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x=>x.1+x.2) :=
  (unarySuccessor.iterate Polynomial.X (by
    intro n a i hi
    simp only [Nat.succ_iterate,unaryCode,List.length_replicate,Polynomial.eval_X]
    omega)).congrFun (by intro x;simp [Nat.succ_iterate,Nat.add_comm])

noncomputable def unaryMul : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x=>x.1*x.2) := by
  let step : Procedure (prodCode unaryCode unaryCode) (prodCode unaryCode unaryCode) addCounter:=
    ((first unaryCode unaryCode).pair unaryAdd).congrFun (by intro x;rfl)
  let rep:=step.iterate (Polynomial.X^2+Polynomial.X) (by
    intro n x i hi
    rw [addCounter_iterate]
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate,
      Polynomial.eval_add,Polynomial.eval_pow,Polynomial.eval_X]
    have hm : x.1≤n+(2*x.1+1+x.2):=by omega
    have hii : i≤n+(2*x.1+1+x.2):=by omega
    have hh:=Nat.mul_le_mul hii hm
    nlinarith)
  let fst:=first unaryCode unaryCode
  let snd:=second unaryCode unaryCode
  let start:=fst.pair (snd.pair (constant (prodCode unaryCode unaryCode) unaryCode 0))
  exact ((second unaryCode unaryCode).comp (rep.comp start)).congrFun (by
    intro x
    change (addCounter^[x.1] (x.2,0)).2=x.1*x.2
    simp [addCounter_iterate])

noncomputable def unaryPred : Procedure unaryCode unaryCode (fun n=>n-1) :=
  (tail.precompose unaryCode).result (by intro n;simp [unaryCode])

noncomputable def unarySub : Procedure (prodCode unaryCode unaryCode) unaryCode
    (fun x=>x.1-x.2) := by
  let p:=unaryPred.iterate Polynomial.X (by
    intro n a i _
    simp only [pred_iterate_word,unaryCode,List.length_replicate,Polynomial.eval_X]
    omega)
  exact (p.comp (swap unaryCode unaryCode)).congrFun (by intro x;simp [pred_iterate_word])

noncomputable def unaryZero : Procedure unaryCode boolCode (fun n=>decide (n=0)) :=
  (isEmpty.precompose unaryCode).congrFun (by intro n;simp [unaryCode])

noncomputable def unaryLe : Procedure (prodCode unaryCode unaryCode) boolCode
    (fun x=>decide (x.1≤x.2)) :=
  (unaryZero.comp unarySub).congrFun (by intro x;simp only [Function.comp_apply,decide_eq_decide];omega)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
