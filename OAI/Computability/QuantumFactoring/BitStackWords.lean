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
public import OAI.Computability.QuantumFactoring.BitStackChoice

@[expose] public section

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
namespace Procedure
variable {α : Type}
noncomputable def prepend (ea : α→List Bool) (xs : List Bool) :
    Procedure ea (fun a=>xs++ea a) id where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=pushWord () xs
  bound:=Polynomial.C (xs.length+1)
  runs a:=by
    refine ⟨xs.length+1,by simp,?_⟩
    simpa [singletonStore] using pushWord_runs () xs (singletonStore () (ea a))

noncomputable def reverse : Procedure (id : List Bool→List Bool) id List.reverse where
  K:=Fin 2
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=1
  program:=reverseMove 0 1
  bound:=Polynomial.C 2*Polynomial.X+1
  runs xs:=by
    have hh:=reverseMove_runs (0 : Fin 2) 1 (by decide) (singletonStore 0 xs)
    refine ⟨2*xs.length+1,by simp,?_⟩
    convert hh using 1
    all_goals try (first | omega | (simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate, List.length_reverse]; omega))  -- PORT NOTE (D2): arithmetic side goal left by convert on 4.33
    · funext k;fin_cases k <;> simp [singletonStore,Function.update]
    · simp [singletonStore]
    · simp [singletonStore]

noncomputable def tail : Procedure (id : List Bool→List Bool) id List.tail where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () .skip .skip .skip
  bound:=Polynomial.C 2
  runs xs:=by
    refine ⟨2,by simp,?_⟩
    cases xs with
    | nil=>exact Runs.cases_nil (by simp [singletonStore]) (Runs.skip _)
    | cons b bs=>
      have hu : Function.update (singletonStore () (b::bs)) () bs=singletonStore () bs:=by
        simp [singletonStore]
      cases b
      · exact hu ▸ Runs.cases_false (by simp [singletonStore]) (Runs.skip _)
      · exact hu ▸ Runs.cases_true (by simp [singletonStore]) (Runs.skip _)

noncomputable def isEmpty : Procedure (id : List Bool→List Bool) boolCode List.isEmpty where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () (.push () true)
    (.seq (clear ()) (.push () false)) (.seq (clear ()) (.push () false))
  bound:=Polynomial.C 2*Polynomial.X+Polynomial.C 3
  runs xs:=by
    cases xs with
    | nil=>
      refine ⟨2,by simp,?_⟩
      exact Runs.cases_nil (by simp [singletonStore]) (by
        simpa [singletonStore,boolCode] using Runs.push (singletonStore () []) () true)
    | cons b bs=>
      let s:=singletonStore () bs
      let u:=Function.update s () []
      have hc:=clear_runs () s
      have hp:=Runs.push u () false
      have hh:=Runs.seq hc hp
      have hu : Function.update (singletonStore () (b::bs)) () bs=s:=by simp [s,singletonStore]
      have hv : Function.update u () (false::u ())=singletonStore () [false]:=by
        funext k;cases k;simp [u,s,singletonStore]
      rw [hv] at hh
      have ht : 1+(2*(s ()).length+1)=2*bs.length+2:=by simp [s,singletonStore];omega
      rw [ht] at hh
      refine ⟨2*bs.length+3,by simp,?_⟩
      cases b
      · exact Runs.cases_false (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)
      · exact Runs.cases_true (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)

noncomputable def head : Procedure (id : List Bool→List Bool) boolCode (fun xs=>xs.headD false) where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.cases () (.push () false)
    (.seq (clear ()) (.push () false)) (.seq (clear ()) (.push () true))
  bound:=Polynomial.C 2*Polynomial.X+Polynomial.C 3
  runs xs:=by
    cases xs with
    | nil=>
      refine ⟨2,by simp,?_⟩
      exact Runs.cases_nil (by simp [singletonStore]) (by
        simpa [singletonStore,boolCode] using Runs.push (singletonStore () []) () false)
    | cons b bs=>
      let s:=singletonStore () bs
      let u:=Function.update s () []
      have hc:=clear_runs () s
      have hp:=Runs.push u () b
      have hh:=Runs.seq hc hp
      have hu : Function.update (singletonStore () (b::bs)) () bs=s:=by simp [s,singletonStore]
      have hv : Function.update u () (b::u ())=singletonStore () [b]:=by
        funext k;cases k;simp [u,s,singletonStore]
      rw [hv] at hh
      have ht : 1+(2*(s ()).length+1)=2*bs.length+2:=by simp [s,singletonStore];omega
      rw [ht] at hh
      refine ⟨2*bs.length+3,by simp,?_⟩
      cases b
      · exact Runs.cases_false (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)
      · exact Runs.cases_true (xs:=bs) (by simp [singletonStore]) (by simpa only [id_eq,hu,boolCode,List.isEmpty_cons,List.headD_cons] using hh)

noncomputable def append : Procedure (prodCode (id : List Bool→List Bool) id) id
    (fun x=>x.1++x.2) where
  K:=Fin 4
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=0
  output:=0
  program:=.seq (unquoteMove 0 1 2 3) (.seq (reverseMove 1 2) (reverseMove 2 0))
  bound:=Polynomial.C 11*Polynomial.X+Polynomial.C 8
  runs x:=by
    let s : Store (Fin 4):=singletonStore 0 (prodCode id id x)
    let u : Store (Fin 4):=Function.update (singletonStore 0 x.2) 1 x.1
    let v : Store (Fin 4):=Function.update (singletonStore 0 x.2) 2 x.1.reverse
    have h1 : Runs (unquoteMove 0 1 2 3) s u (7*x.1.length+6):=by
      have hh:=unquoteMove_runs (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) x.1 x.2 s
        (by simp [s,singletonStore,prodCode,pairBits])
        (by simp [s,singletonStore]) (by simp [s,singletonStore])
      convert hh using 1
      all_goals try (first | omega | (simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate, List.length_reverse]; omega))  -- PORT NOTE (D2): arithmetic side goal left by convert on 4.33
      funext k;fin_cases k <;> simp [s,u,singletonStore,Function.update]
    have h2 : Runs (reverseMove 1 2) u v (2*x.1.length+1):=by
      have hh:=reverseMove_runs (1 : Fin 4) 2 (by decide) u
      convert hh using 1
      all_goals try (first | omega | (simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate, List.length_reverse]; omega))  -- PORT NOTE (D2): arithmetic side goal left by convert on 4.33
      · funext k;fin_cases k <;> simp [u,v,singletonStore,Function.update]
      · simp [u]
    have h3 : Runs (reverseMove 2 0) v (singletonStore 0 (x.1++x.2)) (2*x.1.length+1):=by
      have hh:=reverseMove_runs (2 : Fin 4) 0 (by decide) v
      convert hh using 1
      all_goals try (first | omega | (simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate, List.length_reverse]; omega))  -- PORT NOTE (D2): arithmetic side goal left by convert on 4.33
      · funext k;fin_cases k <;> simp [v,singletonStore,Function.update]
      · simp [v]
    refine ⟨(2*x.1.length+1)+(2*x.1.length+1)+(7*x.1.length+6),?_,
      Runs.seq h1 (Runs.seq h2 h3)⟩
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
      prodCode,pairBits_length,id_eq]
    omega
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
