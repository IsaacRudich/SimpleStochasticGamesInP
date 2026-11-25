module

public import SSGinP.Machine.MachineProcD2Driver
public import SSGinP.Theory.Theory

@[expose] public section

/-!
# SSGinP.Machine.MachineProcD2Eval: reading the game off the layout and one exact
evaluation of the value operator `F` at a node, as BitStack procedures.

Parameters `q = (l, (n, m))` (code `qc`): the layout `l = w.reverse`, `n` in binary (row length used for
addressing) and `m` in unary (number of columns read); in use `n = m = nOf l`.
-/

namespace SSG28MachineProcD2

open OAI.ExactQuantumFactoring.BitStackProgram OAI.ExactQuantumFactoring.BitStackProgram.Procedure

/-! ### Index of the first `true` -/

def idxStep (x : Bool × (Bool × ℕ)) : Bool × ℕ :=
  if x.2.1 then x.2 else if x.1 then (true, x.2.2) else (false, x.2.2 + 1)

theorem fold_idxStep_true (xs : List Bool) (c : ℕ) :
    xs.foldl (fun s b => idxStep (b, s)) (true, c) = (true, c) := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.foldl_cons, idxStep, if_true]; exact ih

theorem fold_idxStep (xs : List Bool) (c : ℕ) :
    (xs.foldl (fun s b => idxStep (b, s)) (false, c)).2 = c + xs.idxOf true := by
  induction xs generalizing c with
  | nil => simp
  | cons b xs ih =>
    rw [List.foldl_cons]
    cases b
    · rw [show idxStep (false, (false, c)) = (false, c + 1) from rfl, ih, List.idxOf_cons]; simp; omega
    · rw [show idxStep (true, (false, c)) = (true, c) from rfl, fold_idxStep_true]; simp [List.idxOf_cons]

theorem fold_idxStep_le (xs : List Bool) (s : Bool × ℕ) :
    (xs.foldl (fun s b => idxStep (b, s)) s).2 ≤ s.2 + xs.length := by
  induction xs generalizing s with
  | nil => simp
  | cons b xs ih =>
    simp only [List.foldl_cons, List.length_cons]
    have := ih (idxStep (b, s))
    have h2 : (idxStep (b, s)).2 ≤ s.2 + 1 := by
      unfold idxStep; split_ifs <;> simp
    omega

noncomputable def idxStepP : Procedure (prodCode boolCode (prodCode boolCode unaryCode))
    (prodCode boolCode unaryCode) idxStep := by
  let s := second boolCode (prodCode boolCode unaryCode)
  let b := first boolCode (prodCode boolCode unaryCode)
  let f := (first boolCode unaryCode).comp s
  let c := (second boolCode unaryCode).comp s
  let found := (constant (prodCode boolCode (prodCode boolCode unaryCode)) boolCode true).pair c
  let notFound := (constant (prodCode boolCode (prodCode boolCode unaryCode)) boolCode false).pair
    (unarySuccessor.comp c)
  exact (conditional f s (conditional b found notFound)).congrFun (by intro x; rfl)

/-- `List.idxOf true`, in unary. -/
noncomputable def idxTrueP : Procedure (listCode boolCode) unaryCode (fun xs => xs.idxOf true) := by
  let rep := foldList false idxStepP (Polynomial.C 2 * Polynomial.X + 2) (by
    intro xs s i
    have h := fold_idxStep_le (xs.take i) s
    have h2 := list_length_le_code boolCode xs
    simp only [List.length_take] at h
    simp only [prodCode, pairBits_length, boolCode, unaryCode, List.length_replicate, List.length_cons,
      List.length_nil, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_ofNat] at *
    omega)
  exact ((second boolCode unaryCode).comp (rep.comp ((identity (listCode boolCode)).pair
    (constant (listCode boolCode) (prodCode boolCode unaryCode) (false, 0))))).congrFun
    (by intro xs; simp [fold_idxStep])


/-! ### Node type and children read from the layout -/

/-- the node-type index of node `i` (0 max, 1 min, 2 average, 3 terminal-0, ≥4 terminal-1). -/
def tyF (q : List Bool × (ℕ × ℕ)) (i : ℕ) : ℕ :=
  ((List.range 5).map (fun k => bitF q.1 q.2.1 i 0 k)).idxOf true

/-- the child of node `i` in field `k` (6 = childJ, 7 = childK). -/
def chF (q : List Bool × (ℕ × ℕ)) (i k : ℕ) : ℕ :=
  ((List.range q.2.2).map (fun j => bitF q.1 q.2.1 i j k)).idxOf true

abbrev iqbc : ℕ × (List Bool × (ℕ × ℕ)) → List Bool := prodCode Nat.bits qc

noncomputable def tyP : Procedure iqbc unaryCode (fun x => tyF x.2 x.1) := by
  let step : Procedure (prodCode unaryCode iqbc) boolCode (fun x => bitF x.2.2.1 x.2.2.2.1 x.2.1 0 x.1) :=
    bitWith ((first Nat.bits qc).comp (second unaryCode iqbc)) (constant (prodCode unaryCode iqbc) Nat.bits 0)
      (unaryToBits.comp (first unaryCode iqbc)) ((second Nat.bits qc).comp (second unaryCode iqbc))
  let tab := (tabulate (f := fun (y : ℕ × (List Bool × (ℕ × ℕ))) k => bitF y.2.1 y.2.2.1 y.1 0 k)
    false step).comp ((constant iqbc unaryCode 5).pair (identity iqbc))
  exact (idxTrueP.comp tab).congrFun (by intro x; rfl)

noncomputable def chP (k : ℕ) : Procedure iqbc unaryCode (fun x => chF x.2 x.1 k) := by
  let step : Procedure (prodCode unaryCode iqbc) boolCode (fun x => bitF x.2.2.1 x.2.2.2.1 x.2.1 x.1 k) :=
    bitWith ((first Nat.bits qc).comp (second unaryCode iqbc)) (unaryToBits.comp (first unaryCode iqbc))
      (constant (prodCode unaryCode iqbc) Nat.bits k) ((second Nat.bits qc).comp (second unaryCode iqbc))
  let mU := (nUOfQ.comp (second Nat.bits qc))
  let tab := (tabulate (f := fun (y : ℕ × (List Bool × (ℕ × ℕ))) j => bitF y.2.1 y.2.2.1 y.1 j k)
    false step).comp (mU.pair (identity iqbc))
  exact (idxTrueP.comp tab).congrFun (by intro x; rfl)

/-! ### Rational comparisons -/

noncomputable def ratLtP : Procedure (prodCode ratCode ratCode) boolCode (fun x => decide (x.1 < x.2)) :=
  ((intSign.comp ratNum).comp ratSub).congrFun (by
    intro x
    simp only [Function.comp_apply]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, Rat.num_neg, sub_neg])

noncomputable def ratMaxP : Procedure (prodCode ratCode ratCode) ratCode (fun x => max x.1 x.2) :=
  (conditional ratLtP (second ratCode ratCode) (first ratCode ratCode)).congrFun (by
    intro x
    by_cases h : x.1 < x.2
    · simp [h, max_eq_right h.le]
    · simp [h, max_eq_left (not_lt.mp h)])

noncomputable def ratMinP : Procedure (prodCode ratCode ratCode) ratCode (fun x => min x.1 x.2) :=
  (conditional ratLtP (first ratCode ratCode) (second ratCode ratCode)).congrFun (by
    intro x
    by_cases h : x.1 < x.2
    · simp [h, min_eq_left h.le]
    · simp [h, min_eq_right (not_lt.mp h)])

noncomputable def ratAvgP : Procedure (prodCode ratCode ratCode) ratCode (fun x => (x.1 + x.2) / 2) :=
  (ratDiv.comp (ratAdd.pair (constant (prodCode ratCode ratCode) ratCode 2))).congrFun (by intro x; rfl)

/-! ### The value read at a node, and one evaluation of `F` -/

/-- `ev`: terminals read their constant, other nodes read `xs`. -/
def evF (q : List Bool × (ℕ × ℕ)) (xs : List ℚ) (j : ℕ) : ℚ :=
  if tyF q j = 3 then 0 else if 4 ≤ tyF q j then 1 else xs.getD j 0

/-- `F` at node `i`. -/
def FF (q : List Bool × (ℕ × ℕ)) (xs : List ℚ) (i : ℕ) : ℚ :=
  if tyF q i = 0 then max (evF q xs (chF q i 6)) (evF q xs (chF q i 7))
  else if tyF q i = 1 then min (evF q xs (chF q i 6)) (evF q xs (chF q i 7))
  else if tyF q i = 2 then (evF q xs (chF q i 6) + evF q xs (chF q i 7)) / 2
  else if tyF q i = 3 then 0 else 1

/-- inputs `(i, (q, xs))`. -/
abbrev evc : ℕ × ((List Bool × (ℕ × ℕ)) × List ℚ) → List Bool :=
  prodCode Nat.bits (prodCode qc (listCode ratCode))

noncomputable def iOfE : Procedure evc Nat.bits (fun x => x.1) := first Nat.bits (prodCode qc (listCode ratCode))
noncomputable def qxOfE : Procedure evc (prodCode qc (listCode ratCode)) (fun x => x.2) :=
  second Nat.bits (prodCode qc (listCode ratCode))
noncomputable def qOfE : Procedure evc qc (fun x => x.2.1) := (first qc (listCode ratCode)).comp qxOfE
noncomputable def xsOfE : Procedure evc (listCode ratCode) (fun x => x.2.2) :=
  (second qc (listCode ratCode)).comp qxOfE

theorem headD_drop_q (l : List ℚ) (p : ℕ) : (l.drop p).headD 0 = l.getD p 0 := by
  induction l generalizing p with
  | nil => simp
  | cons b l ih => cases p with
    | zero => simp
    | succ p => simp [ih]

noncomputable def evP : Procedure evc ratCode (fun x => evF x.2.1 x.2.2 x.1) := by
  let t := unaryToBits.comp (tyP.comp (iOfE.pair qOfE))
  let is3 := eqP.comp (t.pair (constant evc Nat.bits 3))
  let ge4 := binaryLe.comp ((constant evc Nat.bits 4).pair t)
  let val := (listGet ratCode (0 : ℚ)).comp (iOfE.pair xsOfE)
  exact (conditional is3 (constant evc ratCode 0) (conditional ge4 (constant evc ratCode 1) val)).congrFun (by
    intro x
    simp only [evF, Function.comp_apply, id_eq, headD_drop_q]
    by_cases h3 : tyF x.2.1 x.1 = 3
    · simp [h3]
    · by_cases h4 : 4 ≤ tyF x.2.1 x.1 <;> simp [h3, h4])

/-- **(G) one exact evaluation of `F` at node `i`** from the layout parameters `q` and the values `xs`. -/
noncomputable def FP : Procedure evc ratCode (fun x => FF x.2.1 x.2.2 x.1) := by
  let t := unaryToBits.comp (tyP.comp (iOfE.pair qOfE))
  let cJ := unaryToBits.comp ((chP 6).comp (iOfE.pair qOfE))
  let cK := unaryToBits.comp ((chP 7).comp (iOfE.pair qOfE))
  let a := evP.comp (cJ.pair qxOfE)
  let b := evP.comp (cK.pair qxOfE)
  let ab := a.pair b
  let isK (c : ℕ) := eqP.comp (t.pair (constant evc Nat.bits c))
  exact (conditional (isK 0) (ratMaxP.comp ab) (conditional (isK 1) (ratMinP.comp ab)
    (conditional (isK 2) (ratAvgP.comp ab) (conditional (isK 3) (constant evc ratCode 0)
      (constant evc ratCode 1))))).congrFun (by
    intro x
    simp only [FF, Function.comp_apply]
    by_cases h0 : tyF x.2.1 x.1 = 0
    · simp [h0]
    by_cases h1 : tyF x.2.1 x.1 = 1
    · simp [h1]
    by_cases h2 : tyF x.2.1 x.1 = 2
    · simp [h2]
    by_cases h3 : tyF x.2.1 x.1 = 3 <;> simp [h0, h1, h2, h3])


/-! ### Agreement with the decoded game -/

section spec
open SSG SSG28Decode

variable (l : List Bool) (h : ValidL l)

/-- the parameters of a layout. -/
def qOf : List Bool × (ℕ × ℕ) := (l, (nOf l, nOf l))

theorem nodeType_eq (i : Fin (nOf l)) : (gameOf l h).nodeType i = typeOf (tyF (qOf l) i) := rfl

theorem childJ_eq (i : Fin (nOf l)) : ((gameOf l h).childJ i).val = chF (qOf l) i 6 := rfl
theorem childK_eq (i : Fin (nOf l)) : ((gameOf l h).childK i).val = chF (qOf l) i 7 := rfl

theorem ev_eq (xs : List ℚ) (j : Fin (nOf l)) :
    ev (gameOf l h) (fun j => xs.getD j.val 0) j = evF (qOf l) xs j := by
  unfold ev evF
  rw [nodeType_eq l h j]
  generalize tyF (qOf l) j = t
  rcases t with _ | _ | _ | _ | t <;> simp [typeOf]

/-- **spec of (G)**: on a valid layout, `FF` is the value operator `F` of the decoded game. -/
theorem FF_eq (xs : List ℚ) (i : Fin (nOf l)) :
    FF (qOf l) xs i = F (gameOf l h) (fun j => xs.getD j.val 0) i := by
  have eJ : ev (gameOf l h) (fun j => xs.getD j.val 0) ((gameOf l h).child i false) =
      evF (qOf l) xs (chF (qOf l) i 6) := by
    rw [ev_eq l h]; rfl
  have eK : ev (gameOf l h) (fun j => xs.getD j.val 0) ((gameOf l h).child i true) =
      evF (qOf l) xs (chF (qOf l) i 7) := by
    rw [ev_eq l h]; rfl
  unfold F
  rw [nodeType_eq l h i, eJ, eK]
  unfold FF
  generalize tyF (qOf l) i = t
  rcases t with _ | _ | _ | _ | t <;> simp [typeOf]

end spec

end SSG28MachineProcD2
