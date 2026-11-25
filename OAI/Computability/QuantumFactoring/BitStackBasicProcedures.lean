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
public import OAI.Computability.QuantumFactoring.BitStackProducts

@[expose] public section

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
  {f : α→β} {g : α→γ}

/-- Duplicate the input word and quote the first copy to represent a pair. -/
noncomputable def duplicate (ea : α→List Bool) :
    Procedure ea (prodCode ea ea) (fun a=>(a,a)) where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=3
  program:=.seq (duplicateReverse 0 1 2) (.seq (reverseMove 1 3) (quoteMove 0 3 1))
  bound:=Polynomial.C 14*Polynomial.X+Polynomial.C 8
  runs a:=by
    let s : Store (Fin 4):=singletonStore 0 (ea a)
    let u : Store (Fin 4):=Function.update s 1 (ea a).reverse
    let v : Store (Fin 4):=Function.update s 3 (ea a)
    have h1 : Runs (duplicateReverse 0 1 2) s u (5*(ea a).length+2) := by
      have hh:=duplicateReverse_runs (0 : Fin 4) 1 2 (by decide) (by decide) (by decide)
        s (by simp [s,singletonStore])
      simpa only [u,s,singletonStore,Function.update_self,
        Function.update_of_ne (by decide : (1 : Fin 4)≠0),List.append_nil] using hh
    have h2 : Runs (reverseMove 1 3) u v (2*(ea a).length+1) := by
      have hh:=reverseMove_runs (1 : Fin 4) 3 (by decide) u
      convert hh using 1
      all_goals try (first | omega | (simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate, List.length_reverse]; omega))  -- PORT NOTE (D2): arithmetic side goal left by convert on 4.33
      · funext k; fin_cases k <;> simp [u,v,s,singletonStore,Function.update]
      · simp [u]
    have h3 : Runs (quoteMove 0 3 1) v
        (singletonStore 3 (prodCode ea ea (a,a))) (7*(ea a).length+5) := by
      have hh:=quoteMove_runs (0 : Fin 4) 3 1 (by decide) (by decide) (by decide) v
        (by simp [v,s,singletonStore])
      convert hh using 1
      all_goals try (first | omega | (simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate, List.length_reverse]; omega))  -- PORT NOTE (D2): arithmetic side goal left by convert on 4.33
      · funext k; fin_cases k <;> simp [v,s,singletonStore,Function.update,prodCode,pairBits]
      · simp [v,s,singletonStore]
    refine ⟨(7*(ea a).length+5)+(2*(ea a).length+1)+(5*(ea a).length+2),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    omega

noncomputable def pair (p : Procedure ea eb f) (q : Procedure ea ec g) :
    Procedure ea (prodCode eb ec) (fun a=>(f a,g a)) :=
  (p.parallel q).comp (duplicate ea)

/-- Projection parses the actual prefix code and explicitly clears its tail. -/
noncomputable def first (ea : α→List Bool) (eb : β→List Bool) :
    Procedure (prodCode ea eb) ea Prod.fst where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=.seq (unquoteMove 0 1 2 3) (clear 0)
  bound:=Polynomial.C 7*Polynomial.X+Polynomial.C 7
  runs x:=by
    let s : Store (Fin 4):=singletonStore 0 (prodCode ea eb x)
    let u : Store (Fin 4):=Function.update (singletonStore 0 (eb x.2)) 1 (ea x.1)
    have h1 : Runs (unquoteMove 0 1 2 3) s u (7*(ea x.1).length+6) := by
      have hh:=unquoteMove_runs (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (ea x.1) (eb x.2) s
        (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      all_goals try (first | omega | (simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate, List.length_reverse]; omega))  -- PORT NOTE (D2): arithmetic side goal left by convert on 4.33
      funext k; fin_cases k <;> simp [s,u,singletonStore,Function.update]
    have h2 : Runs (clear 0) u (singletonStore 1 (ea x.1)) (2*(eb x.2).length+1) := by
      have hh:=clear_runs (0 : Fin 4) u
      convert hh using 1
      all_goals try (first | omega | (simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate, List.length_reverse]; omega))  -- PORT NOTE (D2): arithmetic side goal left by convert on 4.33
      · funext k; fin_cases k <;> simp [u,singletonStore,Function.update]
      · simp [u,singletonStore]
    refine ⟨(2*(eb x.2).length+1)+(7*(ea x.1).length+6),?_,Runs.seq h1 h2⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      prodCode,pairBits_length]
    omega

noncomputable def second (ea : α→List Bool) (eb : β→List Bool) :
    Procedure (prodCode ea eb) eb Prod.snd :=
  ((first eb ea).comp (swap ea eb)).congrFun (by intro x; rfl)

end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
