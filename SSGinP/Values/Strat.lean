module

public import SSGinP.Values.Loop

@[expose] public section

/-!
# SSGinP.Values.Strat: the greedy strategies of a list of values, as BitStack procedures
# (independent of the output format)

For the table `q = (layout, (n, n))` of a game word and a list of values `ys`:
* `gmaxF q ys i` : the arc to child `k` has the greater value than the arc to child `j` (greedy max choice);
* `gminF q ys i` : the arc to child `k` has the smaller value (greedy min choice);
* `gmaxP`, `gminP` : procedures on `(i, (q, ys))`, in the shape wanted by `tabulate`;
* `gmaxF_spec`, `gminF_spec` : on a decoded game `G` and `ys = List.ofFn v` these are the bits
  `decide (greedyMax G v i = .k)`, `decide (greedyMin G v i = .k)`.
-/

namespace SSGValuesStrat

open SSG SSGValues SSG28MachineProcD2
open OAI.ExactQuantumFactoring.BitStackProgram OAI.ExactQuantumFactoring.BitStackProgram.Procedure

abbrev Q := List Bool × (ℕ × ℕ)
abbrev qyC : Q × List ℚ → List Bool := prodCode qc (listCode ratCode)

def gmaxF (q : Q) (ys : List ℚ) (i : ℕ) : Bool := decide (evF q ys (chF q i 6) < evF q ys (chF q i 7))
def gminF (q : Q) (ys : List ℚ) (i : ℕ) : Bool := decide (evF q ys (chF q i 7) < evF q ys (chF q i 6))

/-- the value read at child `k` (6 = childJ, 7 = childK) of node `i`. -/
noncomputable def evChildP (k : ℕ) :
    Procedure (prodCode unaryCode qyC) ratCode (fun x => evF x.2.1 x.2.2 (chF x.2.1 x.1 k)) := by
  let iB := unaryToBits.comp (first unaryCode qyC)
  let qy := second unaryCode qyC
  let q := (first qc (listCode ratCode)).comp qy
  let ch := unaryToBits.comp ((chP k).comp (iB.pair q))
  exact (evP.comp (ch.pair qy)).congrFun (by intro x; rfl)

noncomputable def gmaxP : Procedure (prodCode unaryCode qyC) boolCode (fun x => gmaxF x.2.1 x.2.2 x.1) :=
  (ratLtP.comp ((evChildP 6).pair (evChildP 7))).congrFun (by intro x; rfl)

noncomputable def gminP : Procedure (prodCode unaryCode qyC) boolCode (fun x => gminF x.2.1 x.2.2 x.1) :=
  (ratLtP.comp ((evChildP 7).pair (evChildP 6))).congrFun (by intro x; rfl)

theorem decide_ofBool (b : Bool) : decide (ArcChoice.ofBool b = ArcChoice.k) = b := by cases b <;> rfl

theorem getD_ofFn {n : ℕ} (v : Fin n → ℚ) : (fun j : Fin n => (List.ofFn v).getD j.val 0) = v := by
  funext j; simp [List.getD_eq_getElem?_getD]

theorem evF_child (l : List Bool) (h : SSG28Decode.ValidL l) (v : Fin (SSG28Decode.nOf l) → ℚ)
    (i : Fin (SSG28Decode.nOf l)) :
    evF (qOf l) (List.ofFn v) (chF (qOf l) i 6) = ev (SSG28Decode.gameOf l h) v ((SSG28Decode.gameOf l h).child i false) ∧
    evF (qOf l) (List.ofFn v) (chF (qOf l) i 7) = ev (SSG28Decode.gameOf l h) v ((SSG28Decode.gameOf l h).child i true) := by
  have e1 := ev_eq l h (List.ofFn v) ((SSG28Decode.gameOf l h).child i false)
  have e2 := ev_eq l h (List.ofFn v) ((SSG28Decode.gameOf l h).child i true)
  rw [getD_ofFn] at e1 e2
  exact ⟨e1.symm, e2.symm⟩

theorem gmaxF_spec (w : List Bool) (n : ℕ) (G : Game n) (hd : SSG28Decode.decode w = some ⟨n, G⟩)
    (v : Fin n → ℚ) (i : Fin n) :
    gmaxF (w.reverse, (n, n)) (List.ofFn v) i.val = decide (greedyMax G v i = .k) := by
  unfold SSG28Decode.decode at hd
  split_ifs at hd with hv
  cases hd
  obtain ⟨e1, e2⟩ := evF_child w.reverse hv v i
  unfold greedyMax
  rw [decide_ofBool, ← e1, ← e2]
  rfl

theorem gminF_spec (w : List Bool) (n : ℕ) (G : Game n) (hd : SSG28Decode.decode w = some ⟨n, G⟩)
    (v : Fin n → ℚ) (i : Fin n) :
    gminF (w.reverse, (n, n)) (List.ofFn v) i.val = decide (greedyMin G v i = .k) := by
  unfold SSG28Decode.decode at hd
  split_ifs at hd with hv
  cases hd
  obtain ⟨e1, e2⟩ := evF_child w.reverse hv v i
  unfold greedyMin
  rw [decide_ofBool, ← e1, ← e2]
  rfl

/-- the `okGame` test on the table of a decoded game. -/
theorem okF_spec (w : List Bool) (n : ℕ) (G : Game n) (hd : SSG28Decode.decode w = some ⟨n, G⟩) :
    okF (w.reverse, (n, n)) = SSG28Reply.okGame G := by
  unfold SSG28Decode.decode at hd
  split_ifs at hd with hv
  cases hd
  exact okF_eq w.reverse hv

end SSGValuesStrat
