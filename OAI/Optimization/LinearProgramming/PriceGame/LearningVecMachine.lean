-- Ported verbatim (modulo toolchain fixes) from the openai_math repository, Apache-2.0. See LICENSE, NOTICE, PORTED_FILES.md.
module

public import OAI.PortCompat
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import OAI.Computability.QuantumFactoring.BitStackGCD
public import OAI.Computability.QuantumFactoring.BitStackListIndex
public import OAI.Computability.QuantumFactoring.BitStackListLength
public import OAI.Computability.QuantumFactoring.BitStackTabulate
public import Mathlib.Data.List.OfFn
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

@[expose] public section

/-! # Fixed finite arrays on the binary-stack machine

A column is represented by the ordinary bit-stack list encoding in `Fin` order. These
procedures operate on the encoded words. The arity is a compile-time parameter; the
learning routine uses only the 66 possible arities of compact skeletons.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram

variable {α β : Type}

/-- The decoded type records the arity. The wire format is an ordinary encoded list. -/
def vecCode (e : β → List Bool) (n : ℕ) (v : Fin n → β) : List Bool :=
  listCode e (List.ofFn v)

def matrixCode (e : β → List Bool) (n : ℕ) (d : Fin n → Fin n → β) : List Bool :=
  vecCode (vecCode e n) n d

/-- Read a fixed coordinate by walking the encoded list. -/
noncomputable def coordinate (e : β → List Bool) (d : β) {n : ℕ} (i : Fin n) :
    Procedure (vecCode e n) e (fun v => v i) := by
  let input : Procedure (vecCode e n) (listCode e) (fun v : Fin n → β => List.ofFn v) :=
    (Procedure.identity (listCode e)).precompose List.ofFn
  let index := Procedure.constant (vecCode e n) Nat.bits i.val
  apply ((Procedure.listGet e d).comp (index.pair input)).congrFun
  intro v
  change ((List.ofFn v).drop i.val).headD d = v i
  simp [List.head?_drop]

/-- Build a fixed-arity encoded list from truly computed component words. -/
noncomputable def assemble (ea : α → List Bool) (eb : β → List Bool) :
    (n : ℕ) → (f : α → Fin n → β) → (∀ i, Procedure ea eb (fun a => f a i)) →
      Procedure ea (vecCode eb n) f
  | 0, f, _ => (Procedure.constant ea (listCode eb) ([] : List β)).result (by
      intro a; simp [vecCode])
  | n+1, f, p => by
    let tail := assemble ea eb n (fun a i => f a i.succ) (fun i => p i.succ)
    let listTail : Procedure ea (listCode eb) (fun a => List.ofFn fun i : Fin n => f a i.succ) :=
      tail.result (fun _ => rfl)
    exact ((Procedure.listCons eb).comp ((p 0).pair listTail)).result (by
      intro a; change listCode eb (_ :: _) = listCode eb (List.ofFn (f a)); rw [List.ofFn_succ])

/-- Build a square matrix in its ordinary row-list encoding. -/
noncomputable def assembleMatrix (ea : α → List Bool) (eb : β → List Bool) (n : ℕ)
    (f : α → Fin n → Fin n → β) (p : ∀ i j, Procedure ea eb (fun a => f a i j)) :
    Procedure ea (matrixCode eb n) f :=
  assemble ea (vecCode eb n) n f (fun i => assemble ea eb n (fun a => f a i) (p i))

/-- Read a cell using two charged list walks. -/
noncomputable def readMatrix (eb : β → List Bool) (default : β) {n : ℕ} (i j : Fin n) :
    Procedure (matrixCode eb n) eb (fun m => m i j) :=
  (coordinate eb default j).comp (coordinate (vecCode eb n) (fun _ => default) i)

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
