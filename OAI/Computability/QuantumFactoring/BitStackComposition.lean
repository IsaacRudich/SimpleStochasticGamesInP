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
public import OAI.Computability.QuantumFactoring.BitStackLists
public import OAI.Computability.QuantumFactoring.BitStackProcedures

@[expose] public section

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K L : Type} [DecidableEq K] [DecidableEq L]

omit [DecidableEq K] [DecidableEq L] in
lemma overlay_empty (f : K ↪ L) : overlay f (fun _=>[]) (fun _=>[])=fun _=>[] := by
  funext j
  by_cases h : ∃ i,f i=j
  · rcases h with ⟨i,rfl⟩; exact overlay_at f _ _ i
  · exact overlay_outside f _ _ j (by simpa only [not_exists] using h)
lemma overlay_singleton (f : K ↪ L) (k : K) (xs : List Bool) :
    overlay f (fun _=>[]) (singletonStore k xs)=singletonStore (f k) xs := by
  rw [singletonStore,overlay_update,overlay_empty]
  rfl

/-- Move an entire word without reversing its order. Each symbol is pushed
and popped twice; this is not an atomic bulk-copy instruction. -/
def moveWord (a b t : K) : Program K := .seq (reverseMove a t) (reverseMove t b)
lemma moveWord_runs (a b t : K) (hab : a≠b) (hat : a≠t) (hbt : b≠t) (xs : List Bool) :
    Runs (moveWord a b t) (singletonStore a xs) (singletonStore b xs) (4*xs.length+2) := by
  let s := singletonStore a xs
  let u := Function.update (Function.update s a []) t ((s a).reverse++s t)
  have hh := Runs.seq (reverseMove_runs a t hat s) (reverseMove_runs t b hbt.symm u)
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  all_goals try (first | omega | (simp only [List.length_cons, List.length_nil, List.length_append, List.length_replicate, List.length_reverse]; omega))  -- PORT NOTE (D2): arithmetic side goal left by convert on 4.33
  · funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht : k=t <;>
      simp_all [u,s,singletonStore,Function.update,Ne.symm hat,Ne.symm hab,Ne.symm hbt]
  · simp only [u,Function.update_self,s,singletonStore,Function.update_self]
    simp only [Function.update_of_ne hat.symm,List.append_nil,List.length_reverse]
    omega

namespace Procedure
variable {α β γ : Type} {ea : α→List Bool} {eb : β→List Bool} {ec : γ→List Bool}
  {f : α→β} {g : β→γ}

def joinLeft (A B : Type) : A ↪ A ⊕ (B ⊕ Unit) := ⟨Sum.inl,Sum.inl_injective⟩
def joinRight (A B : Type) : B ↪ A ⊕ (B ⊕ Unit) :=
  ⟨Sum.inr ∘ Sum.inl,Sum.inr_injective.comp Sum.inl_injective⟩

lemma eval_nat_mono (p : Polynomial ℕ) : Monotone p.eval := by
  intro a b hab
  change p.eval a ≤ p.eval b
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

/-- Checked composition for actual finite Boolean-stack procedures. This
constructs the combined program and accounts for the intermediate-word copy;
it does NOT invoke Mathlib's unproved TM2 polytime-composition declaration. -/
noncomputable def comp (q : Procedure eb ec g) (p : Procedure ea eb f) :
    Procedure ea ec (g ∘ f) where
  K := p.K ⊕ (q.K ⊕ Unit)
  finiteK := inferInstance
  decideK := inferInstance
  input := Sum.inl p.input
  output := Sum.inr (Sum.inl q.output)
  program := .seq (p.program.relabel (joinLeft p.K q.K))
    (.seq (moveWord (Sum.inl p.output) (Sum.inr (Sum.inl q.input)) (Sum.inr (Sum.inr ())))
      (q.program.relabel (joinRight p.K q.K)))
  bound := p.bound+(Polynomial.C 4*(Polynomial.X+p.bound)+Polynomial.C 2)+
    q.bound.comp (Polynomial.X+p.bound)
  runs a := by
    obtain ⟨cp,hcp,hp⟩ := p.runs a
    obtain ⟨cq,hcq,hq⟩ := q.runs (f a)
    have hleft := hp.relabel (joinLeft p.K q.K) (fun _=>[])
    have hright := hq.relabel (joinRight p.K q.K) (fun _=>[])
    simp only [overlay_singleton] at hleft hright
    have hmove := moveWord_runs (K:=p.K ⊕ (q.K ⊕ Unit)) (Sum.inl p.output)
      (Sum.inr (Sum.inl q.input)) (Sum.inr (Sum.inr ()))
      (by simp) (by simp) (by simp) (eb (f a))
    refine ⟨cq+(4*(eb (f a)).length+2)+cp,?_,Runs.seq hleft (Runs.seq hmove hright)⟩
    have hlen := p.output_length_le a
    have hmono := eval_nat_mono q.bound hlen
    dsimp only at hmono
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
      Polynomial.eval_X,Polynomial.eval_comp]
    omega
end Procedure
end ExactQuantumFactoring.BitStackProgram

end



end OAI
