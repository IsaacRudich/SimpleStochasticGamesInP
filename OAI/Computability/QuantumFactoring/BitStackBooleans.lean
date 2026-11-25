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
public import OAI.Computability.QuantumFactoring.BitStackWords

@[expose] public section

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
variable {β : Type}

/-- A truth table on one Boolean has two literal finite output words. This
performs no run-time computation in its Boolean branch labels. -/
noncomputable def ofBool (eb : β→List Bool) (f : Bool→β) :
    Procedure boolCode eb f := by
  let p:=constant (fun _ : Unit=>[]) eb (f false)
  let q:=constant (fun _ : Unit=>[]) eb (f true)
  exact ((chooseBit p q).precompose (fun b=>(b,()))).congrFun
    (by intro b;cases b <;> rfl)

noncomputable def ofBool₂ (eb : β→List Bool) (f : Bool→Bool→β) :
    Procedure (prodCode boolCode boolCode) eb (fun x=>f x.1 x.2) :=
  (choose (ofBool eb (f false)) (ofBool eb (f true))).congrFun
    (by rintro ⟨b,c⟩;cases b <;> rfl)

noncomputable def ofBool₃ (eb : β→List Bool) (f : Bool→Bool→Bool→β) :
    Procedure (prodCode boolCode (prodCode boolCode boolCode)) eb
      (fun x=>f x.1 x.2.1 x.2.2) :=
  (choose (ofBool₂ eb (f false)) (ofBool₂ eb (f true))).congrFun
    (by rintro ⟨b,c,d⟩;cases b <;> rfl)

noncomputable def boolNot : Procedure boolCode boolCode not := ofBool boolCode not
noncomputable def boolAnd : Procedure (prodCode boolCode boolCode) boolCode
    (fun x=>x.1 && x.2) := ofBool₂ boolCode and
noncomputable def boolOr : Procedure (prodCode boolCode boolCode) boolCode
    (fun x=>x.1 || x.2) := ofBool₂ boolCode or
noncomputable def boolXor : Procedure (prodCode boolCode boolCode) boolCode
    (fun x=>xor x.1 x.2) := ofBool₂ boolCode xor

noncomputable def cons : Procedure (prodCode boolCode (id : List Bool→List Bool)) id
    (fun x=>x.1::x.2) := by
  let pp : Procedure (id : List Bool→List Bool) id (fun xs=>false::xs):=
    (prepend id [false]).result (by intro xs;rfl)
  let qq : Procedure (id : List Bool→List Bool) id (fun xs=>true::xs):=
    (prepend id [true]).result (by intro xs;rfl)
  exact (choose pp qq).congrFun (by rintro ⟨b,xs⟩;cases b <;> rfl)
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
