module

public import SSGinP.GameFacts
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# SSGinP.Machine.Decode: the decoder of the input layout

The input word is `enc A = (layout A).reverse`; the layout `l` has `10 n^2` bits, bit `(i*n + j)*10 + k` being
field `k` of the node pair `(a_i, a_j)`:
`0 isMax u, 1 isMin u, 2 isAverage u, 3 isTerminalZero u, 4 isTerminalOne u, 5 startNode u, 6 childA u v,
 7 childB u v, 8 [u = v], 9 [v = a_{n-1}]`.

`decode w` reads `l = w.reverse`; `n` is determined by the length (`10 n^2`, `n ≥ 1`). The node type of node `i`
is read from the block `(i, 0)` (fields 0-4, exactly one set), childJ / childK from fields 6 / 7 of the row `i`
(exactly one set each), the start node from field 5 of the blocks `(i, 0)` (exactly one set). Fields 8, 9 are not
read. Any other word decodes to `none`.
-/

namespace SSG28Decode

open SSG

/-- the number of nodes, read from the length `10 n^2`. -/
def nOf (l : List Bool) : ℕ := Nat.sqrt (l.length / 10)

/-- field `k` of the node pair `(i, j)`. -/
def bit (l : List Bool) (i j k : ℕ) : Bool := l.getD ((i * nOf l + j) * 10 + k) false

def typeBits (l : List Bool) (i : ℕ) : List Bool := (List.range 5).map (fun k => bit l i 0 k)
def childRow (l : List Bool) (i : ℕ) (b : Bool) : List Bool :=
  (List.range (nOf l)).map (fun j => bit l i j (if b then 7 else 6))
def startCol (l : List Bool) : List Bool := (List.range (nOf l)).map (fun i => bit l i 0 5)

/-- a one-hot word: exactly one `true`. -/
def OneHot (l : List Bool) : Prop := l.count true = 1

instance (l : List Bool) : Decidable (OneHot l) := by unfold OneHot; infer_instance

/-- the shape conditions on the layout. -/
def ValidL (l : List Bool) : Prop :=
  1 ≤ nOf l ∧ l.length = nOf l * nOf l * 10 ∧
  (∀ i < nOf l, OneHot (typeBits l i) ∧ OneHot (childRow l i false) ∧ OneHot (childRow l i true)) ∧
  OneHot (startCol l)

instance (l : List Bool) : Decidable (ValidL l) := by unfold ValidL; infer_instance

/-- position of the first `true`. -/
def pos (l : List Bool) : ℕ := l.idxOf true

theorem pos_lt (l : List Bool) (h : OneHot l) : pos l < l.length := by
  unfold pos; apply List.idxOf_lt_length_of_mem
  unfold OneHot at h; exact List.count_pos_iff.mp (by omega)

def typeOf : ℕ → NodeType
  | 0 => .max
  | 1 => .min
  | 2 => .average
  | 3 => .terminal0
  | _ => .terminal1

/-- the decoded game. -/
def gameOf (l : List Bool) (h : ValidL l) : Game (nOf l) where
  nodeType i := typeOf (pos (typeBits l i))
  childJ i := ⟨pos (childRow l i false), by
    have := pos_lt (childRow l i false) (h.2.2.1 i i.2).2.1
    simpa [childRow] using this⟩
  childK i := ⟨pos (childRow l i true), by
    have := pos_lt (childRow l i true) (h.2.2.1 i i.2).2.2
    simpa [childRow] using this⟩
  startNode := ⟨pos (startCol l), by
    have := pos_lt _ h.2.2.2
    simpa [startCol] using this⟩

/-- **the decoder** of machine inputs. -/
def decode (w : List Bool) : Option (Σ n, Game n) :=
  if h : ValidL w.reverse then some ⟨nOf w.reverse, gameOf w.reverse h⟩ else none

/-- the decision predicate on words (the paper's problem, at least 1/2). -/
def Accept (w : List Bool) : Prop :=
  ∃ n G, decode w = some ⟨n, G⟩ ∧ SSGDecision G

/-- the strict variant (greater than 1/2). -/
def AcceptStrict (w : List Bool) : Prop :=
  ∃ n G, decode w = some ⟨n, G⟩ ∧ SSGDecisionStrict G

end SSG28Decode
