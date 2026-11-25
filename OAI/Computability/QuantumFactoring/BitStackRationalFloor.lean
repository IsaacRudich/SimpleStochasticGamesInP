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

namespace ExactQuantumFactoring.BitStackProgram.Procedure
noncomputable def ratFloor : Procedure ratCode intCode (fun q=>⌊q⌋):=by
  let num:=ratNum
  let den:=ratDen
  let mag:=intAbs.comp num
  let negmag:=binaryAdd.comp ((binaryDiv.comp
    ((binarySub.comp (mag.pair (constant ratCode Nat.bits 1))).pair den)).pair
    (constant ratCode Nat.bits 1))
  let pos:=natToInt.comp (binaryDiv.comp (mag.pair den))
  let neg:=intNeg.comp (natToInt.comp negmag)
  exact (conditional (intSign.comp num) neg pos).congrFun (by
    intro q
    change (if decide (q.num<0) then -((((q.num.natAbs-1)/q.den+1):ℕ):ℤ)
      else ((q.num.natAbs/q.den):ℤ))=⌊q⌋
    rw [Rat.floor_def']
    obtain ⟨d,hd⟩:=Nat.exists_eq_succ_of_ne_zero q.den_nz
    rw [hd]
    cases q.num with
    | ofNat a=>simp
    | negSucc a=>
      simp only [Int.negSucc_lt_zero, decide_true, ite_true, Int.natAbs_negSucc,
        Int.negSucc_ediv_ofNat_succ]
      change -((((a+1-1)/(d+1)+1):ℕ):ℤ)=Int.negSucc (a/(d+1))
      simp only [Nat.add_sub_cancel]
      rfl)
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
