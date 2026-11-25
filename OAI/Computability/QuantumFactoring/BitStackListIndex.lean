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
public import OAI.Computability.QuantumFactoring.BitStackListFold
public import OAI.Computability.QuantumFactoring.BitStackDivision

@[expose] public section

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α : Type}
def dropStep : ℕ×List α→ℕ×List α
  | (n,xs)=>if n=0 then (n,xs) else (n-1,xs.tail)
lemma dropStep_iterate (i n : ℕ) (xs : List α) :
    dropStep^[i] (n,xs)=(n-i,xs.drop (min i n)) := by
  induction i generalizing n xs with
  | zero=>simp
  | succ i ih=>
    rw [Function.iterate_succ_apply]
    by_cases hn : n=0
    · subst n;simp [dropStep,ih]
    · obtain ⟨n,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hn
      simp only [dropStep,Nat.succ_ne_zero,ite_false,Nat.succ_sub_one,ih]
      rw [←List.drop_one,List.drop_drop]
      congr 1
      · omega
      · congr 1; omega

namespace Procedure
variable (ea : α→List Bool)
noncomputable def listDrop : Procedure (prodCode Nat.bits (listCode ea)) (listCode ea)
    (fun x=>x.2.drop x.1) := by
  let en:=prodCode Nat.bits (listCode ea)
  let n:=first Nat.bits (listCode ea)
  let xs:=second Nat.bits (listCode ea)
  let pred:=binarySub.comp (n.pair (constant en Nat.bits 1))
  let step:=(conditional (binaryZero.comp n) (identity en)
    (pred.pair ((listTail ea).comp xs)))
  -- PORT NOTE (Lean 4.35): the original ended the previous line with `.congrFun (by intro x;rfl)` (an identity
  -- step; on 4.35 its target function is an unassigned metavariable and the tactic block is stuck).
  have stepType : Procedure en en (dropStep (α:=α)):=
    step.congrFun (by intro x;simp only [Function.comp_apply,decide_eq_true_eq,id_eq,dropStep])
  let rep:=stepType.iterate Polynomial.X (by
    intro k x i _
    rw [dropStep_iterate]
    simp only [en,prodCode,pairBits_length,Polynomial.eval_X]
    have hn:=bits_length_mono (Nat.sub_le x.1 i)
    have hl:=listCode_length_drop_le ea (min i x.1) x.2
    omega)
  let times:=(length.precompose (listCode ea)).comp xs
  exact (xs.comp (rep.comp (times.pair (identity en)))).congrFun (by
    intro x
    change (dropStep^[(listCode ea x.2).length] x).2=x.2.drop x.1
    rw [dropStep_iterate]
    by_cases h:x.1≤(listCode ea x.2).length
    · rw [Nat.min_eq_right h]
    · have hlen:=list_length_le_code ea x.2
      rw [Nat.min_eq_left (by omega),List.drop_eq_nil_of_le (by omega),List.drop_eq_nil_of_le (by omega)])
noncomputable def listGet (d : α) : Procedure (prodCode Nat.bits (listCode ea)) ea
    (fun x=>(x.2.drop x.1).headD d) := (listHead ea d).comp (listDrop ea)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
