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
public import OAI.Computability.QuantumFactoring.BitStackRationals

@[expose] public section

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
noncomputable def ratInv : Procedure ratCode ratCode (fun q=>q⁻¹):=by
  let num:=signedInt.comp ((intSign.comp ratNum).pair ratDen)
  let den:=intAbs.comp ratNum
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro q
    change mkRat (intOfSign (decide (q.num<0),q.den)) q.num.natAbs=q⁻¹
    rw [Rat.mkRat_eq_div]
    by_cases h:q.num<0
    · have hz:=Int.eq_neg_natAbs_of_nonpos h.le
      simp only [h,decide_true,intOfSign,ite_true,Int.cast_neg,Int.cast_natCast]
      conv_rhs=>rw [←Rat.num_div_den q,hz]
      simp only [Int.cast_neg,Int.cast_natCast,neg_div,inv_neg,inv_div]
    · have hz:=Int.natAbs_of_nonneg (le_of_not_gt h)
      simp only [h,decide_false,intOfSign,Bool.false_eq_true,ite_false,Int.cast_natCast]
      conv_rhs=>rw [←Rat.num_div_den q,←hz]
      simp only [inv_div,Int.cast_natCast])
noncomputable def ratDiv : Procedure (prodCode ratCode ratCode) ratCode (fun x=>x.1/x.2):=
  (ratMul.comp ((first ratCode ratCode).pair (ratInv.comp (second ratCode ratCode)))).congrFun
    (by intro x;exact (div_eq_mul_inv _ _).symm)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
