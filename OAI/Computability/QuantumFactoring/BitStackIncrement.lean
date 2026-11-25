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
public import OAI.Computability.QuantumFactoring.BitStackLists

@[expose] public section

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram

/-- Little-endian evaluation; leading zeroes at the high end are allowed. -/
def binaryValue : List Bool → ℕ
  | [] => 0
  | b::xs => b.toNat+2*binaryValue xs

def incrementWord : List Bool → List Bool
  | [] => [true]
  | false::xs => true::xs
  | true::xs => false::incrementWord xs

def carryTail : List Bool → List Bool
  | [] => [true]
  | false::xs => true::xs
  | true::xs => carryTail xs

def carryCount : List Bool → ℕ
  | [] => 0
  | false::_ => 0
  | true::xs => carryCount xs+1

lemma incrementWord_value (xs : List Bool) : binaryValue (incrementWord xs)=binaryValue xs+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [incrementWord,binaryValue,ih] <;> omega
lemma carryCount_le_length (xs : List Bool) : carryCount xs≤xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [carryCount,List.length_cons]; omega
lemma incrementWord_eq (xs : List Bool) :
    incrementWord xs=List.replicate (carryCount xs) false++carryTail xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [incrementWord,carryCount,carryTail,ih,List.replicate_succ]
lemma incrementWord_length (xs : List Bool) : (incrementWord xs).length≤xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [incrementWord,List.length_cons]; omega

variable {K : Type} [DecidableEq K]
def rippleBody (a t c : K) : Program K :=
  .cases a (.push a true) (.push a true) (.seq (.push t false) (.push c true))
def ripple (a t c : K) : Program K := .loop c (rippleBody a t c) (rippleBody a t c)
def increment (a t c : K) : Program K :=
  .seq (.push c true) (.seq (ripple a t c) (reverseMove t a))

lemma ripple_runs (a t c : K) (hat : a≠t) (hac : a≠c) (htc : t≠c)
    (s : Store K) (hc : s c=[true]) :
    Runs (ripple a t c) s
      (Function.update (Function.update (Function.update s c []) a (carryTail (s a)))
        t (List.replicate (carryCount (s a)) false++s t))
      (4*(carryCount (s a)+1)) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    let u := Function.update s c []
    let v := Function.update u a [true]
    have hua : u a=[] := by simp [u,hac,hs]
    have hvc : v c=[] := by simp [v,u,hac.symm]
    have body : Runs (rippleBody a t c) u v 2 :=
      Runs.cases_nil hua (by simpa only [hua] using Runs.push u a true)
    have hh := Runs.loop_true (p:=rippleBody a t c) (a:=2) (b:=1) hc body (Runs.loop_nil hvc)
    change Runs (.loop _ _ _) _ _ _
    convert hh using 1
    all_goals try (first | omega | (simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate, List.length_reverse]; omega))  -- PORT NOTE (D2): arithmetic side goal left by convert on 4.33
    · simp only [carryCount,carryTail,List.replicate_zero,List.nil_append]
      change Function.update v t (s t)=v
      rw [← show v t=s t by simp [v,u,hat.symm,htc],Function.update_eq_self]
    · rfl
  | cons x xs ih =>
    cases x
    · let u := Function.update s c []
      let w := Function.update u a xs
      let v := Function.update w a (true::xs)
      have hua : u a=false::xs := by simp [u,hac,hs]
      have hvc : v c=[] := by simp [v,w,u,hac.symm]
      have body : Runs (rippleBody a t c) u v 2 :=
        Runs.cases_false hua (by simpa only [w,Function.update_self] using Runs.push w a true)
      have hh := Runs.loop_true (p:=rippleBody a t c) (a:=2) (b:=1) hc body (Runs.loop_nil hvc)
      change Runs (.loop _ _ _) _ _ _
      convert hh using 1
      all_goals try (first | omega | (simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate, List.length_reverse]; omega))  -- PORT NOTE (D2): arithmetic side goal left by convert on 4.33
      · funext k
        by_cases ha : k=a <;> by_cases ht : k=t <;> by_cases hcc : k=c <;>
          simp_all [v,w,u,Function.update,carryCount,carryTail]
      · rfl
    · let u := Function.update s c []
      let w := Function.update u a xs
      let z := Function.update w t (false::w t)
      let v := Function.update z c (true::z c)
      have hua : u a=true::xs := by simp [u,hac,hs]
      have hva : v a=xs := by simp [v,z,w,hac,hat]
      have hvc : v c=[true] := by simp [v,z,w,u,htc.symm,hac.symm]
      have body : Runs (rippleBody a t c) u v 3 :=
        Runs.cases_true (a:=2) hua (Runs.seq (Runs.push w t false) (Runs.push z c true))
      have hh := Runs.loop_true (p:=rippleBody a t c) (a:=3) (b:=4*(carryCount xs+1)) hc body (ih v hvc hva)
      change Runs (.loop _ _ _) _ _ _
      convert hh using 1
      all_goals try (first | omega | (simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate, List.length_reverse]; omega))  -- PORT NOTE (D2): arithmetic side goal left by convert on 4.33
      · funext k
        by_cases ha : k=a <;> by_cases ht : k=t <;> by_cases hcc : k=c <;>
          simp_all [v,z,w,u,Function.update,carryCount,carryTail,List.replicate_succ]
        rw [← List.cons_append, ← List.replicate_succ, List.replicate_succ',List.append_assoc]
        rfl
      · simp only [carryCount]; omega

lemma increment_runs (a t c : K) (hat : a≠t) (hac : a≠c) (htc : t≠c)
    (s : Store K) (ht : s t=[]) (hc : s c=[]) :
    Runs (increment a t c) s (Function.update s a (incrementWord (s a)))
      (6*carryCount (s a)+6) := by
  let u := Function.update s c [true]
  have hua : u a=s a := by simp [u,hac]
  have hut : u t=[] := by simp [u,ht,htc]
  have huc : u c=[true] := by simp [u]
  let v := Function.update (Function.update (Function.update u c []) a (carryTail (u a)))
    t (List.replicate (carryCount (u a)) false++u t)
  have hp : Runs (.push c true) s u 1 := by simpa only [hc] using Runs.push s c true
  have hh := Runs.seq hp
    (Runs.seq (ripple_runs a t c hat hac htc u huc) (reverseMove_runs t a hat.symm v))
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  all_goals try (first | omega | (simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate, List.length_reverse]; omega))  -- PORT NOTE (D2): arithmetic side goal left by convert on 4.33
  · funext k
    by_cases ha : k=a <;> by_cases htk : k=t <;> by_cases hck : k=c <;>
      simp_all [v,u,Function.update,incrementWord_eq]
  · simp only [v,Function.update_self,hut,List.append_nil,List.length_replicate,hua]
    omega

end ExactQuantumFactoring.BitStackProgram

end



end OAI
