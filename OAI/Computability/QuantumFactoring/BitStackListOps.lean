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

@[expose] public section

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {α β : Type}

lemma fold_cons_append (xs ys : List α) : xs.foldl (fun ys a=>a::ys) ys=xs.reverse++ys := by
  induction xs generalizing ys with
  | nil=>rfl
  | cons a as ih=>simp only [List.foldl_cons,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

lemma fold_map_cons_append (f : α→β) (xs : List α) (ys : List β) :
    xs.foldl (fun ys a=>f a::ys) ys=(xs.map f).reverse++ys := by
  induction xs generalizing ys with
  | nil=>rfl
  | cons a as ih=>simp only [List.foldl_cons,ih,List.map_cons,List.reverse_cons,
      List.append_assoc,List.singleton_append]

lemma listCode_length_map_bound (eb : β→List Bool) (f : α→β) (xs : List α) (B : ℕ)
    (h : ∀ a∈xs,(eb (f a)).length≤B) :
    (listCode eb (xs.map f)).length≤xs.length*(2*B+2)+1 := by
  induction xs with
  | nil=>simp [listCode]
  | cons a as ih=>
    have ha:=h a (by simp)
    have hb:=ih (by intro b hb;exact h b (by simp [hb]))
    simp only [List.map_cons,listCode_length_cons,List.length_cons]
    nlinarith

namespace Procedure
variable (ea : α→List Bool)
noncomputable def listRevAppend (d : α) : Procedure (prodCode (listCode ea) (listCode ea))
    (listCode ea) (fun x=>x.1.reverse++x.2) :=
  (foldList d (listCons ea) Polynomial.X (by
    intro xs ys i
    rw [fold_cons_append]
    have hh:=listCode_length_append ea (xs.take i).reverse ys
    rw [listCode_length_rev] at hh
    have ht:=listCode_length_take_le ea i xs
    simp only [Polynomial.eval_X]
    omega)).congrFun (by intro x;exact fold_cons_append x.1 x.2)

noncomputable def listReverse (d : α) : Procedure (listCode ea) (listCode ea) List.reverse :=
  ((listRevAppend ea d).comp ((identity (listCode ea)).pair
    (constant (listCode ea) (listCode ea) []))).congrFun (by intro xs;exact List.append_nil _)

noncomputable def listAppend (d : α) : Procedure (prodCode (listCode ea) (listCode ea))
    (listCode ea) (fun x=>x.1++x.2) :=
  ((listRevAppend ea d).comp (((listReverse ea d).comp (first (listCode ea) (listCode ea))).pair
    (second (listCode ea) (listCode ea)))).congrFun (by intro x;exact congrArg (fun xs=>xs++x.2) (List.reverse_reverse x.1))

variable {ea} {eb : β→List Bool} {f : α→β}
noncomputable def listMap (d : α) (e : β) (p : Procedure ea eb f) :
    Procedure (listCode ea) (listCode eb) (List.map f) := by
  let step:=(listCons eb).comp ((p.comp (first ea (listCode eb))).pair (second ea (listCode eb)))
  let q:=Polynomial.X*(Polynomial.C 2*(Polynomial.X+p.bound)+Polynomial.C 2)+1+Polynomial.X
  let fold:=foldList d step q (by
    intro xs ys i
    change (listCode eb ((xs.take i).foldl (fun ys a=>f a::ys) ys)).length≤_
    rw [fold_map_cons_append]
    let L:=(listCode ea xs).length+(listCode eb ys).length
    have hh:=listCode_length_append eb ((xs.take i).map f).reverse ys
    rw [listCode_length_rev] at hh
    have hm:(listCode eb ((xs.take i).map f)).length≤(xs.take i).length*(2*(L+p.bound.eval L)+2)+1:=by
      apply listCode_length_map_bound
      intro a ha
      have hc:=(code_le_of_mem ea (List.mem_of_mem_take ha)).trans (Nat.le_add_right _ (listCode eb ys).length)
      have ho:=p.output_length_le a
      have hp:=eval_nat_mono p.bound hc
      dsimp only [L] at *
      omega
    have ht : (xs.take i).length≤L:=by
      have h1:=list_length_le_code ea xs
      simp only [List.length_take]
      dsimp [L];omega
    have hm':=(Nat.mul_le_mul_right (2*(L+p.bound.eval L)+2) ht)
    simp only [q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_one]
    change (listCode eb (((xs.take i).map f).reverse++ys)).length≤L*(2*(L+p.bound.eval L)+2)+1+L
    dsimp only [L] at *
    omega)
  let start:=(identity (listCode ea)).pair (constant (listCode ea) (listCode eb) [])
  exact ((listReverse eb e).comp (fold.comp start)).congrFun (by
    intro xs
    change (xs.foldl (fun ys a=>f a::ys) []).reverse=xs.map f
    rw [fold_map_cons_append,List.append_nil,List.reverse_reverse])
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
