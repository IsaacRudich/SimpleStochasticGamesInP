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
public import OAI.Computability.QuantumFactoring.BitStackIntegers
public import OAI.Computability.QuantumFactoring.ProcedureFurther

@[expose] public section

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

def ratCode (q : ℚ) : List Bool := prodCode intCode Nat.bits (q.num,q.den)

def ratData (x : ℤ×ℕ) : ℤ×ℕ :=
  if x.2=0 then (0,1) else
    (intOfSign (decide (x.1<0),x.1.natAbs/(x.2.gcd x.1.natAbs)),
      x.2/(x.2.gcd x.1.natAbs))

lemma intOfSign_div (z : ℤ) (d : ℕ) (hd : d∣z.natAbs) :
    intOfSign (decide (z<0),z.natAbs/d)=z/(d : ℤ) := by
  by_cases h : z<0
  · have hz := Int.eq_neg_natAbs_of_nonpos (le_of_lt h)
    have hdiv : (d : ℤ) ∣ (z.natAbs : ℤ) := Int.ofNat_dvd.mpr hd
    simp only [h,decide_true,intOfSign,ite_true]
    conv_rhs => rw [hz,Int.neg_ediv_of_dvd hdiv]
    rw [Int.natCast_ediv]
  · simp only [h,decide_false,intOfSign,Bool.false_eq_true,ite_false]
    conv_rhs => rw [←Int.natAbs_of_nonneg (le_of_not_gt h)]
    rw [Int.natCast_ediv]

lemma ratData_spec (x : ℤ×ℕ) : ratData x=((mkRat x.1 x.2).num,(mkRat x.1 x.2).den) := by
  rw [Rat.num_mkRat,Rat.den_mkRat]
  unfold ratData
  split
  · rfl
  · rw [intOfSign_div _ _ (Nat.gcd_dvd_right _ _)]

namespace Procedure
noncomputable def ratNum : Procedure ratCode intCode Rat.num :=
  (first intCode Nat.bits).precompose (fun q : ℚ=>(q.num,q.den))
noncomputable def ratDen : Procedure ratCode Nat.bits Rat.den :=
  (second intCode Nat.bits).precompose (fun q : ℚ=>(q.num,q.den))

noncomputable def makeRat : Procedure (prodCode intCode Nat.bits) ratCode
    (fun x=>mkRat x.1 x.2) := by
  let n:=first intCode Nat.bits
  let d:=second intCode Nat.bits
  let a:=intAbs.comp n
  let g:=binaryGcd.comp (d.pair a)
  let num:=signedInt.comp ((intSign.comp n).pair (binaryDiv.comp (a.pair g)))
  let den:=binaryDiv.comp (d.pair g)
  let zero:=constant (prodCode intCode Nat.bits) (prodCode intCode Nat.bits) (0,1)
  let p:=conditional (binaryZero.comp d) zero (num.pair den)
  exact p.result (by
    intro x
    simp only [Function.comp_apply,decide_eq_true_eq]
    change prodCode intCode Nat.bits (ratData x)=ratCode (mkRat x.1 x.2)
    rw [ratData_spec];rfl)

noncomputable def intToRat : Procedure intCode ratCode (fun z=>(z : ℚ)) :=
  (makeRat.comp ((identity intCode).pair (constant intCode Nat.bits 1))).congrFun (by
    intro z; simp [Rat.mkRat_eq_div])
noncomputable def natToRat : Procedure Nat.bits ratCode (fun n=>(n : ℚ)) :=
  (intToRat.comp natToInt).congrFun (by intro n;simp)

noncomputable def ratNeg : Procedure ratCode ratCode Neg.neg :=
  (makeRat.comp ((intNeg.comp ratNum).pair ratDen)).congrFun (by
    intro q
    change mkRat (-q.num) q.den = -q
    rw [Rat.mkRat_eq_div,Int.cast_neg,neg_div,Rat.num_div_den])

noncomputable def ratAdd : Procedure (prodCode ratCode ratCode) ratCode
    (fun x=>x.1+x.2) := by
  let a:=first ratCode ratCode
  let b:=second ratCode ratCode
  let an:=ratNum.comp a
  let bn:=ratNum.comp b
  let ad:=ratDen.comp a
  let bd:=ratDen.comp b
  let num:=intAdd.comp ((intMul.comp (an.pair (natToInt.comp bd))).pair
    (intMul.comp (bn.pair (natToInt.comp ad))))
  let den:=binaryMul.comp (ad.pair bd)
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro x
    change mkRat (x.1.num * (x.2.den : ℤ) + x.2.num * (x.1.den : ℤ))
      (x.1.den*x.2.den) = x.1+x.2
    rw [←Rat.mkRat_add_mkRat _ _ x.1.den_nz x.2.den_nz]
    simp)

noncomputable def ratMul : Procedure (prodCode ratCode ratCode) ratCode
    (fun x=>x.1*x.2) := by
  let a:=first ratCode ratCode
  let b:=second ratCode ratCode
  let num:=intMul.comp ((ratNum.comp a).pair (ratNum.comp b))
  let den:=binaryMul.comp ((ratDen.comp a).pair (ratDen.comp b))
  exact (makeRat.comp (num.pair den)).congrFun (by
    intro x
    change mkRat (x.1.num*x.2.num) (x.1.den*x.2.den)=x.1*x.2
    rw [←Rat.mkRat_mul_mkRat];simp)

noncomputable def ratSub : Procedure (prodCode ratCode ratCode) ratCode
    (fun x=>x.1-x.2) :=
  (ratAdd.comp ((first ratCode ratCode).pair (ratNeg.comp (second ratCode ratCode)))).congrFun
    (by intro x;exact (sub_eq_add_neg _ _).symm)
end Procedure
end ExactQuantumFactoring.BitStackProgram

end


end OAI
