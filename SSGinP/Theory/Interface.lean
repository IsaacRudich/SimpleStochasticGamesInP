module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Rat.Defs

@[expose] public section

/-!
# SSGinP.Theory.Interface: the price-search interface (the paper's Theorem 2, mathematical form)

This file is the meeting point between the game side and the proof of the search theorem.  It has no machine model and no game notions.

Paper (OpenAI, "Strongly polynomial linear programming", Thm 2 "Extremal prices"):
coordinates `1..N`, slots `(i,h)` with `h ∈ {-1,+1}`.  A deterministic algorithm adaptively queries price vectors
`p ∈ ℚ^N`, receives a label vector `z ∈ {-1,+1}^N` per query, and returns `x ∈ ℚ^N`.  A hypothesis is a nonempty set
`S` of slots with integer demands `a_s ∈ [-R,R]`; its surplus at `s = (i,h)` is `d_s(p) = a_s - h p_i`; it is
consistent if at every query `(p,z)`: `s = (i,h) ∈ S`, `d_s(p) = max_{u∈S} d_u(p) ≥ 0` ⟹ `z_i = h`.
Guarantee: for every consistent hypothesis, `h x_i ≥ a_s` for every `s = (i,h) ∈ S`.

Encoding: a side `h` is a `Bool` (`true = +1`, `false = -1`, value `sideVal h`); a label vector is `Fin N → Bool`.
The oracle is an arbitrary function `O : (Fin N → ℚ) → (Fin N → Bool)` (the game side only ever needs function
oracles).  `run A O k T` runs the strategy `A` from transcript `T` with at most `k` further queries; a transcript is
the chronological list of (query, answer) pairs.

`PriceSearch N R` packages a strategy with a query budget `Q`, a bit budget `B` (every queried price and every
output coordinate has numerator and denominator of absolute value `≤ 2^B`, i.e. at most `B+1` bits each), halting
within `Q` queries against EVERY oracle, and the correctness guarantee of Theorem 2.  `PolyFamily` says the budgets
are polynomial in `N + log₂ R`.  The cost of computing the next query from a transcript (bit time) belongs to the machine
model and is not part of this interface.
-/

namespace SSG28

/-- the numeric value of a side: `true ↦ +1`, `false ↦ -1`. -/
def sideVal (h : Bool) : ℚ := if h then 1 else -1

/-- a slot `(i,h)`. -/
abbrev Slot (N : ℕ) := Fin N × Bool
abbrev Prices (N : ℕ) := Fin N → ℚ
abbrev Labels (N : ℕ) := Fin N → Bool
/-- chronological list of (queried price vector, received label vector). -/
abbrev Transcript (N : ℕ) := List (Prices N × Labels N)

/-- a hypothesis: a nonempty set of slots with integer demands in `[-R,R]`. -/
structure Hyp (N R : ℕ) where
  S : Finset (Slot N)
  nonempty : S.Nonempty
  a : Slot N → ℤ
  bound : ∀ s ∈ S, -(R : ℤ) ≤ a s ∧ a s ≤ R

variable {N R : ℕ}

/-- surplus `d_s(p) = a_s - h p_i` at `s = (i,h)`. -/
def Hyp.surplus (H : Hyp N R) (p : Prices N) (s : Slot N) : ℚ := (H.a s : ℚ) - sideVal s.2 * p s.1

/-- consistency with one answered query: every slot of `S` attaining the maximum surplus, when that maximum is
`≥ 0`, got the label equal to its side. -/
def Hyp.ConsistentAt (H : Hyp N R) (p : Prices N) (z : Labels N) : Prop :=
  ∀ s ∈ H.S, (∀ u ∈ H.S, H.surplus p u ≤ H.surplus p s) → 0 ≤ H.surplus p s → z s.1 = s.2

/-- consistency with a transcript. -/
def Hyp.Consistent (H : Hyp N R) (T : Transcript N) : Prop := ∀ q ∈ T, H.ConsistentAt q.1 q.2

/-- the output meets all demands: `h x_i ≥ a_s` for every `s = (i,h) ∈ S`. -/
def Hyp.Meets (H : Hyp N R) (x : Prices N) : Prop := ∀ s ∈ H.S, (H.a s : ℚ) ≤ sideVal s.2 * x s.1

/-- one move of a deterministic adaptive strategy. -/
inductive Move (N : ℕ)
  | query (p : Prices N)
  | output (x : Prices N)

/-- a deterministic adaptive query strategy: the next move as a function of the transcript so far. -/
def Strategy (N : ℕ) := Transcript N → Move N

/-- run `A` against the oracle `O` from transcript `T`, allowing at most `k` further queries.
`some (x, T')`: output `x` with final transcript `T'`;  `none`: budget exhausted. -/
def run (A : Strategy N) (O : Prices N → Labels N) : ℕ → Transcript N → Option (Prices N × Transcript N)
  | 0, T => match A T with
    | .output x => some (x, T)
    | .query _ => none
  | k + 1, T => match A T with
    | .output x => some (x, T)
    | .query p => run A O k (T ++ [(p, O p)])

/-- a rational with numerator and denominator of absolute value `≤ 2^B` (so at most `B+1` bits each). -/
def BitBdd (B : ℕ) (q : ℚ) : Prop := q.num.natAbs ≤ 2 ^ B ∧ q.den ≤ 2 ^ B

/-- **the search theorem as an object** (paper, Theorem 2): a deterministic adaptive strategy, its query budget
`Q`, its bit budget `B`, halting within `Q` queries against every oracle, all queried prices and all output
coordinates `B`-bounded, and the guarantee: the output meets every hypothesis consistent with the transcript. -/
structure PriceSearch (N R : ℕ) where
  strat : Strategy N
  Q : ℕ
  B : ℕ
  halts : ∀ O, ∃ x T, run strat O Q [] = some (x, T)
  priceBits : ∀ O x T, run strat O Q [] = some (x, T) → ∀ q ∈ T, ∀ i, BitBdd B (q.1 i)
  outBits : ∀ O x T, run strat O Q [] = some (x, T) → ∀ i, BitBdd B (x i)
  correct : ∀ O x T, run strat O Q [] = some (x, T) → ∀ H : Hyp N R, H.Consistent T → H.Meets x

/-- a family of searches whose budgets are polynomial in `N + log₂ R`. -/
def PolyFamily (P : ∀ N R : ℕ, PriceSearch N R) : Prop :=
  ∃ c k : ℕ, ∀ N R, (P N R).Q ≤ c * (N + Nat.log2 R + 2) ^ k ∧ (P N R).B ≤ c * (N + Nat.log2 R + 2) ^ k

/-! ## basic facts about `run` -/

/-- the transcript only grows, by at most `k` entries. -/
theorem run_len (A : Strategy N) (O : Prices N → Labels N) :
    ∀ (k : ℕ) (T : Transcript N) x T', run A O k T = some (x, T') → T'.length ≤ T.length + k ∧ ∃ U, T' = T ++ U
  | 0, T, x, T', h => by
    unfold run at h
    split at h
    · cases h; exact ⟨by omega, [], by simp⟩
    · cases h
  | k + 1, T, x, T', h => by
    unfold run at h
    split at h
    · cases h; exact ⟨by omega, [], by simp⟩
    · obtain ⟨h1, U, hU⟩ := run_len A O k _ x T' h
      exact ⟨by simp at h1; omega, _, by rw [hU, List.append_assoc]⟩

/-- every entry of the final transcript is a genuine oracle answer: `q.2 = O q.1`. -/
theorem run_answers (A : Strategy N) (O : Prices N → Labels N) :
    ∀ (k : ℕ) (T : Transcript N) x T', run A O k T = some (x, T') → (∀ q ∈ T, q.2 = O q.1) →
      ∀ q ∈ T', q.2 = O q.1
  | 0, T, x, T', h, hT => by
    unfold run at h
    split at h
    · cases h; exact hT
    · cases h
  | k + 1, T, x, T', h, hT => by
    unfold run at h
    split at h
    · cases h; exact hT
    · refine run_answers A O k _ x T' h ?_
      intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hT q hq
      · simp at hq; subst hq; rfl

/-- number of oracle calls of a halting run from the empty transcript is at most the budget. -/
theorem PriceSearch.queries_le (P : PriceSearch N R) (O : Prices N → Labels N) (x : Prices N) (T : Transcript N)
    (h : run P.strat O P.Q [] = some (x, T)) : T.length ≤ P.Q := by
  have := (run_len P.strat O P.Q [] x T h).1; simpa using this

end SSG28
