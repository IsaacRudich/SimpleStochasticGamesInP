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
public import OAI.Computability.QuantumFactoring.BitStackBasicProcedures
public import OAI.Computability.QuantumFactoring.BitStackSums
public import OAI.Computability.QuantumFactoring.BitStackWords

@[expose] public section

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}
def listCode (ea : α→List Bool) : List α→List Bool
  | []=>[false]
  | a::as=>true::pairBits (ea a) (listCode ea as)

def emptyCode (_ : Unit) : List Bool := []

def listView : List α→Unit⊕(α×List α)
  | []=>.inl ()
  | a::as=>.inr (a,as)

lemma listCode_length_cons (ea : α→List Bool) (a : α) (as : List α) :
    (listCode ea (a::as)).length=2*(ea a).length+2+(listCode ea as).length := by
  simp [listCode,pairBits_length];omega

lemma listCode_length_append (ea : α→List Bool) (xs ys : List α) :
    (listCode ea (xs++ys)).length+1=(listCode ea xs).length+(listCode ea ys).length := by
  induction xs with
  | nil=>simp [listCode,Nat.add_comm]
  | cons a as ih=>simp only [List.cons_append,listCode_length_cons];omega

lemma listCode_length_rev (ea : α→List Bool) (xs : List α) :
    (listCode ea xs.reverse).length=(listCode ea xs).length := by
  induction xs with
  | nil=>rfl
  | cons a as ih=>
    rw [List.reverse_cons]
    have hh:=listCode_length_append ea as.reverse [a]
    simp only [listCode_length_cons,ih] at hh ⊢
    have hz : (listCode ea []).length=1:=rfl
    omega

lemma listCode_length_pos (ea : α→List Bool) (xs : List α) : 0<(listCode ea xs).length := by
  cases xs <;> simp [listCode]

lemma list_length_le_code (ea : α→List Bool) (xs : List α) : xs.length≤(listCode ea xs).length := by
  induction xs with
  | nil=>simp
  | cons a as ih=>simp only [List.length_cons,listCode_length_cons];omega

lemma listCode_tail_le (ea : α→List Bool) (xs : List α) :
    (listCode ea xs.tail).length≤(listCode ea xs).length := by
  cases xs with
  | nil=>rfl
  | cons a as=>simp only [List.tail_cons,listCode_length_cons];omega

lemma code_le_of_mem (ea : α→List Bool) {a : α} {xs : List α} (h : a∈xs) :
    (ea a).length≤(listCode ea xs).length := by
  induction xs with
  | nil=>simp at h
  | cons b bs ih=>
    rw [List.mem_cons] at h
    rw [listCode_length_cons]
    rcases h with h|h
    · subst b;omega
    · have hh:=ih h;omega

namespace Procedure
variable (ea : α→List Bool)
noncomputable def listUncons : Procedure (listCode ea)
    (sumCode emptyCode (prodCode ea (listCode ea))) listView :=
  (identity (listCode ea)).result (by intro xs;cases xs <;> rfl)

noncomputable def listCons : Procedure (prodCode ea (listCode ea)) (listCode ea)
    (fun x=>x.1::x.2) :=
  (prepend (prodCode ea (listCode ea)) [true]).result (by intro x;rfl)

noncomputable def listHead (d : α) : Procedure (listCode ea) ea (fun xs=>xs.headD d) :=
  ((casesSum (constant emptyCode ea d) (first ea (listCode ea))).comp (listUncons ea)).congrFun
    (by intro xs;cases xs <;> rfl)

noncomputable def listTail : Procedure (listCode ea) (listCode ea) List.tail :=
  ((casesSum (constant emptyCode (listCode ea) []) (second ea (listCode ea))).comp
    (listUncons ea)).congrFun (by intro xs;cases xs <;> rfl)

noncomputable def listEmpty : Procedure (listCode ea) boolCode List.isEmpty :=
  ((casesSum (constant emptyCode boolCode true) (constant (prodCode ea (listCode ea)) boolCode false)).comp
    (listUncons ea)).congrFun (by intro xs;cases xs <;> rfl)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
