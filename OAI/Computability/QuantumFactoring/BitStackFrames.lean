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
public import OAI.Computability.QuantumFactoring.BitStackRelabel
public import OAI.Computability.QuantumFactoring.BitStackProcedures

@[expose] public section

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K L : Type}
def sumStore (s : Store K) (t : Store L) : Store (K ⊕ L) := Sum.elim s t
@[simp] lemma sumStore_left (s : Store K) (t : Store L) (k : K) :
    sumStore s t (Sum.inl k)=s k := rfl
@[simp] lemma sumStore_right (s : Store K) (t : Store L) (l : L) :
    sumStore s t (Sum.inr l)=t l := rfl
lemma sumStore_empty : sumStore (fun _ : K=>[]) (fun _ : L=>[])=fun _=>[] := by
  funext j; cases j <;> rfl

def leftEmbed (K L : Type) : K ↪ K ⊕ L := ⟨Sum.inl,Sum.inl_injective⟩
lemma overlay_left (s : Store K) (t : Store L) :
    overlay (leftEmbed K L) (sumStore (fun _=>[]) t) s=sumStore s t := by
  funext j
  cases j with
  | inl j => exact overlay_at _ _ _ j
  | inr j => exact overlay_outside _ _ _ _ (by intro i; simp [leftEmbed])

variable [DecidableEq K] [DecidableEq L]
@[simp] lemma sumStore_update_left (s : Store K) (t : Store L) (k : K) (xs : List Bool) :
    Function.update (sumStore s t) (Sum.inl k) xs=sumStore (Function.update s k xs) t := by
  funext j; cases j <;> simp [Function.update,sumStore]
@[simp] lemma sumStore_update_right (s : Store K) (t : Store L) (k : L) (xs : List Bool) :
    Function.update (sumStore s t) (Sum.inr k) xs=sumStore s (Function.update t k xs) := by
  funext j; cases j <;> simp [Function.update,sumStore]
lemma sumStore_singleton_left (k : K) (xs : List Bool) :
    singletonStore (Sum.inl k) xs=sumStore (singletonStore k xs) (fun _ : L=>[]) := by
  rw [singletonStore,←sumStore_empty,sumStore_update_left]; rfl
lemma sumStore_singleton_right (k : L) (xs : List Bool) :
    singletonStore (Sum.inr k) xs=sumStore (fun _ : K=>[]) (singletonStore k xs) := by
  rw [singletonStore,←sumStore_empty,sumStore_update_right]; rfl
lemma Runs.left {p : Program K} {s u : Store K} {c : ℕ} (h : Runs p s u c) (t : Store L) :
    Runs (p.relabel Sum.inl) (sumStore s t) (sumStore u t) c := by
  have hh := h.relabel (leftEmbed K L) (sumStore (fun _=>[]) t)
  rw [overlay_left,overlay_left] at hh
  exact hh

namespace Procedure
variable {α β : Type} {ea : α→List Bool} {eb : β→List Bool} {f g : α→β}
def congrFun (p : Procedure ea eb f) (h : ∀ a,f a=g a) : Procedure ea eb g where
  K:=p.K
  finiteK:=p.finiteK
  decideK:=p.decideK
  input:=p.input
  output:=p.output
  program:=p.program
  bound:=p.bound
  runs a:=by simpa only [h a] using p.runs a

noncomputable def identity (ea : α→List Bool) : Procedure ea ea id where
  K:=Unit
  finiteK:=inferInstance
  decideK:=inferInstance
  input:=()
  output:=()
  program:=.skip
  bound:=1
  runs a:=⟨1,by simp,Runs.skip _⟩
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
