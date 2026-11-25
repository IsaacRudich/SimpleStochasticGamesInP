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
public import OAI.Computability.QuantumFactoring.BitStackIteration
public import OAI.Computability.QuantumFactoring.BitStackListOps
public import OAI.Computability.QuantumFactoring.BitStackNaturals

@[expose] public section

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}
def tabStep (f : α→ℕ→β) (s : ℕ×(α×List β)) : ℕ×(α×List β) :=
  (s.1+1,s.2.1,f s.2.1 s.1::s.2.2)
def tabCode (ea : α→List Bool) (eb : β→List Bool) := prodCode unaryCode (prodCode ea (listCode eb))
lemma tabStep_iterate (f : α→ℕ→β) (j i : ℕ) (a : α) (ys : List β) :
    (tabStep f)^[j] (i,a,ys)=(i+j,a,((List.range' i j).map (f a)).reverse++ys) := by
  induction j with
  | zero=>simp
  | succ j ih=>
    rw [Function.iterate_succ_apply',ih]
    simp only [tabStep,List.range'_1_concat,List.map_append,List.map_cons,List.map_nil,
      List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append]
    simp only [Nat.add_assoc]
namespace Procedure
variable {ea : α→List Bool} {eb : β→List Bool} {f : α→ℕ→β}
noncomputable def tabStepP (p : Procedure (prodCode unaryCode ea) eb (fun x=>f x.2 x.1)) :
    Procedure (tabCode ea eb) (tabCode ea eb) (tabStep f) := by
  let i:=first unaryCode (prodCode ea (listCode eb))
  let rest:=second unaryCode (prodCode ea (listCode eb))
  let a:=(first ea (listCode eb)).comp rest
  let ys:=(second ea (listCode eb)).comp rest
  exact ((unarySuccessor.comp i).pair
    (a.pair ((listCons eb).comp ((p.comp (i.pair a)).pair ys)))).congrFun (by intro s;rfl)
noncomputable def tabulate (d : β)
    (p : Procedure (prodCode unaryCode ea) eb (fun x=>f x.2 x.1)) :
    Procedure (prodCode unaryCode ea) (listCode eb)
      (fun x=>(List.range x.1).map (f x.2)) := by
  let q:=(Polynomial.X+p.bound).comp (Polynomial.C 2*Polynomial.X+1)
  have hval (a : α) (i : ℕ) : (eb (f a i)).length≤q.eval (i+(ea a).length) := by
    have ho:=p.output_length_le (i,a)
    have hm:=eval_nat_mono (Polynomial.X+p.bound)
      (show (prodCode unaryCode ea (i,a)).length≤2*(i+(ea a).length)+1 by
        simp only [prodCode,pairBits_length,unaryCode,List.length_replicate];omega)
    simp only [Polynomial.eval_add,Polynomial.eval_X] at hm
    simpa only [q,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one] using ho.trans hm
  let rep:=(tabStepP p).iterate (Polynomial.X*(Polynomial.C 2*q+Polynomial.C 5)) (by
    rintro n ⟨i,a,ys⟩ j hj
    rw [tabStep_iterate]
    have len0 : (tabCode ea eb (i,a,ys)).length=2*i+2*(ea a).length+(listCode eb ys).length+2 := by
      simp only [tabCode,prodCode,pairBits_length,unaryCode,List.length_replicate];omega
    have hv : ∀ k∈List.range' i j,(eb (f a k)).length≤q.eval (n+(tabCode ea eb (i,a,ys)).length) := by
      intro k hk
      have hk':=List.mem_range'.mp hk
      exact (hval a k).trans (eval_nat_mono q (by rw [len0];omega))
    have hmap:=listCode_length_map_bound eb (f a) (List.range' i j) _ hv
    have happ:=listCode_length_append eb (((List.range' i j).map (f a)).reverse) ys
    rw [listCode_length_rev] at happ
    simp only [List.length_range'] at hmap
    simp only [tabCode,prodCode,pairBits_length,unaryCode,List.length_replicate,
      Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X] at *
    nlinarith)
  let inputN:=first unaryCode ea
  let inputA:=second unaryCode ea
  let start:=(constant (prodCode unaryCode ea) unaryCode 0).pair
    (inputA.pair (constant (prodCode unaryCode ea) (listCode eb) []))
  let result:=((second ea (listCode eb)).comp
    (second unaryCode (prodCode ea (listCode eb)))).comp (rep.comp (inputN.pair start))
  exact ((listReverse eb d).comp result).congrFun (by
    rintro ⟨n,a⟩
    change (((tabStep f)^[n] (0,a,[])).2.2).reverse=(List.range n).map (f a)
    rw [tabStep_iterate,List.append_nil,List.reverse_reverse,List.range_eq_range'])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
