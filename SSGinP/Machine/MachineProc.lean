module

public import SSGinP.Machine.Machine
public import OAI.Computability.QuantumFactoring.ProcedureFurther
public import OAI.Computability.QuantumFactoring.BitStackRationalDivision
public import OAI.Computability.QuantumFactoring.BitStackRationalFloor
public import OAI.Computability.QuantumFactoring.BitStackTabulate
public import OAI.Computability.QuantumFactoring.BitStackListOps
public import OAI.Computability.QuantumFactoring.BitStackListIndex
public import OAI.Computability.QuantumFactoring.BitStackListLength

@[expose] public section

/-!
# SSGinP.Machine.MachineProc: procedures for total parsing of words

All procedures work on raw words (`id` encoding) and tuples of raw words, so that every word is a valid input
(BitStack `Procedure`s must be correct on EVERY encoded input).

* `unframeP`: `w ↦ (u, rest)` when `w = quoteBits u ++ rest` (= `frame u ++ rest`, the self-delimiting code of
  `encodeNat`); total on all words.
-/

set_option linter.unusedSimpArgs false

namespace SSG28MachineProc

open OAI.ExactQuantumFactoring.BitStackProgram OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec

abbrev W := List Bool
abbrev idW : W → W := id

/-! ## unframe -/

/-- state: remaining word, reversed contents so far, done flag. -/
abbrev UState := W × (W × Bool)
abbrev uCode : UState → W := prodCode idW (prodCode idW boolCode)

def ufStep (s : UState) : UState :=
  if s.2.2 then s
  else if s.1.isEmpty then (s.1, s.2.1, true)
  else if s.1.headD false then (s.1.tail.tail, s.1.tail.headD false :: s.2.1, false)
  else (s.1.tail, s.2.1, true)

theorem uCode_len (s : UState) : (uCode s).length = 2 * s.1.length + 2 * s.2.1.length + 3 := by
  simp [uCode, prodCode, pairBits_length]; omega

theorem ufStep_len (s : UState) : (uCode (ufStep s)).length ≤ (uCode s).length := by
  rw [uCode_len, uCode_len]
  unfold ufStep
  split_ifs with h1 h2 h3
  · omega
  · simp
  · rcases s with ⟨r, a, d⟩
    simp only at h2 h3 ⊢
    rcases r with _ | ⟨x, _ | ⟨y, r⟩⟩ <;> simp_all <;> omega
  · rcases s with ⟨r, a, d⟩
    simp only at h2 ⊢
    rcases r with _ | ⟨x, r⟩ <;> simp_all

theorem ufStep_iter_len (s : UState) : ∀ i, (uCode (ufStep^[i] s)).length ≤ (uCode s).length
  | 0 => le_rfl
  | i + 1 => by
    rw [Function.iterate_succ_apply']
    exact (ufStep_len _).trans (ufStep_iter_len s i)

noncomputable def remP : Procedure uCode idW (fun s => s.1) := first idW (prodCode idW boolCode)
noncomputable def accP : Procedure uCode idW (fun s => s.2.1) :=
  (first idW boolCode).comp (second idW (prodCode idW boolCode))
noncomputable def doneP : Procedure uCode boolCode (fun s => s.2.2) :=
  (second idW boolCode).comp (second idW (prodCode idW boolCode))

/-- build a state from three procedures. -/
noncomputable def mkState {α : Type} {ea : α → W} {f g : α → W} {h : α → Bool}
    (pf : Procedure ea idW f) (pg : Procedure ea idW g) (ph : Procedure ea boolCode h) :
    Procedure ea uCode (fun a => (f a, g a, h a)) :=
  pf.pair (pg.pair ph)

noncomputable def ufStepP : Procedure uCode uCode ufStep := by
  let stay := identity uCode
  let fin := mkState remP accP (constant uCode boolCode true)
  let two := mkState (tail.comp (tail.comp remP)) (cons.comp ((head.comp (tail.comp remP)).pair accP))
    (constant uCode boolCode false)
  let one := mkState (tail.comp remP) accP (constant uCode boolCode true)
  exact (conditional doneP stay (conditional (isEmpty.comp remP) fin
    (conditional (head.comp remP) two one))).congrFun (by
      intro s; rcases s with ⟨r, a, d⟩; simp [ufStep])

/-- iterate `ufStep` `k` times. -/
noncomputable def ufIterP : Procedure (prodCode unaryCode uCode) uCode (fun x => ufStep^[x.1] x.2) :=
  ufStepP.iterate (Polynomial.X) (by
    intro n a i _
    simp only [Polynomial.eval_X]
    have := ufStep_iter_len a i; omega)

/-- the total unframe function. -/
def unframe (w : W) : W × W :=
  let s := ufStep^[w.length] (w, [], false)
  (s.2.1.reverse, s.1)

theorem ufStep_iter_frame (u rest acc : W) :
    ufStep^[u.length + 1] (quoteBits u ++ rest, acc, false) = (rest, u.reverse ++ acc, true) := by
  induction u generalizing acc with
  | nil => simp [ufStep, quoteBits]
  | cons b u ih =>
    rw [show (b :: u).length + 1 = (u.length + 1) + 1 by simp, Function.iterate_succ_apply]
    have : ufStep (quoteBits (b :: u) ++ rest, acc, false) = (quoteBits u ++ rest, b :: acc, false) := by
      simp [ufStep, quoteBits]
    rw [this, ih]; simp

theorem ufStep_done (s : W × W) : ∀ k, ufStep^[k] (s.1, s.2, true) = (s.1, s.2, true)
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply]; simp only [ufStep, if_true]; exact ufStep_done s k

theorem unframe_frame (u rest : W) : unframe (quoteBits u ++ rest) = (u, rest) := by
  unfold unframe
  have hl : (quoteBits u ++ rest).length = (u.length + rest.length) + (u.length + 1) := by
    simp [quoteBits_length]; omega
  rw [hl, Function.iterate_add_apply, ufStep_iter_frame]
  have := ufStep_done (rest, u.reverse ++ []) (u.length + rest.length)
  simp only at this
  rw [this]; simp

noncomputable def unframeP : Procedure idW (prodCode idW idW) unframe := by
  let start : Procedure idW (prodCode unaryCode uCode) (fun w => (w.length, (w, [], false))) :=
    length.pair (mkState (identity idW) (constant idW idW []) (constant idW boolCode false))
  let fin : Procedure uCode (prodCode idW idW) (fun s => (s.2.1.reverse, s.1)) := (reverse.comp accP).pair remP
  exact ((fin.comp ufIterP).comp start).congrFun (by intro w; rfl)

theorem ufStep_inv (w : W) (s : UState)
    (h : 2 * s.2.1.length + s.1.length ≤ w.length + 1 ∧ (s.1 ≠ [] → 2 * s.2.1.length + s.1.length ≤ w.length)) :
    2 * (ufStep s).2.1.length + (ufStep s).1.length ≤ w.length + 1 ∧
      ((ufStep s).1 ≠ [] → 2 * (ufStep s).2.1.length + (ufStep s).1.length ≤ w.length) := by
  rcases s with ⟨r, a, d⟩
  unfold ufStep
  simp only at h ⊢
  split_ifs with h1 h2 h3
  · exact h
  · exact h
  · rcases r with _ | ⟨x, _ | ⟨y, r⟩⟩
    · simp at h2
    · simp at h ⊢; omega
    · simp at h ⊢; omega
  · rcases r with _ | ⟨x, r⟩
    · simp at h2
    · simp at h ⊢; exact ⟨by omega, fun _ => by omega⟩

theorem unframe_len (w : W) : 2 * (unframe w).1.length + (unframe w).2.length ≤ w.length + 1 := by
  have key : ∀ k, 2 * (ufStep^[k] (w, [], false)).2.1.length + (ufStep^[k] (w, [], false)).1.length ≤ w.length + 1 ∧
      ((ufStep^[k] (w, [], false)).1 ≠ [] →
        2 * (ufStep^[k] (w, [], false)).2.1.length + (ufStep^[k] (w, [], false)).1.length ≤ w.length) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply']; exact ufStep_inv w _ ih
  have := (key w.length).1
  simpa [unframe] using this

/-! ## rationals and lists of rationals -/

theorem frame_eq (bits : W) : frame bits = quoteBits bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [frame, quoteBits] at ih ⊢; exact ih

theorem encodeNat_eq (n : ℕ) : encodeNat n = quoteBits n.bits := frame_eq _

/-- the `ratCode` word from sign, magnitude and denominator words. -/
def ratWord (s : Bool) (A D : W) : W := quoteBits (quoteBits [s] ++ A) ++ D

theorem ratWord_eq (y : ℚ) : ratWord (decide (y.num < 0)) y.num.natAbs.bits y.den.bits = ratCode y := by
  simp [ratWord, ratCode, prodCode, pairBits, intCode, intData]

/-- one parse step: move the first rational of `rem` (in `encodeRat` form) to the `listCode ratCode` word `acc`. -/
def plStep (s : W × W) : W × W :=
  if s.1.isEmpty then s
  else
    let p1 := unframe s.1.tail
    let p2 := unframe p1.2
    (p2.2, true :: quoteBits (ratWord (s.1.headD false) p1.1 p2.1) ++ s.2)

theorem encodeRat_eq (y : ℚ) :
    encodeRat y = decide (y.num < 0) :: (quoteBits y.num.natAbs.bits ++ quoteBits y.den.bits) := by
  simp [encodeRat, encodeNat_eq]

theorem plStep_cons (y : ℚ) (r : W) (acc : List ℚ) :
    plStep (encodeRat y ++ r, listCode ratCode acc) = (r, listCode ratCode (y :: acc)) := by
  rw [encodeRat_eq]
  simp only [plStep, List.cons_append, List.isEmpty_cons, Bool.false_eq_true, if_false, List.tail_cons,
    List.headD_cons, List.append_assoc]
  rw [unframe_frame, unframe_frame, ratWord_eq]
  simp [listCode, pairBits]

theorem plStep_nil (acc : W) : plStep ([], acc) = ([], acc) := by simp [plStep]

def flatR (l : List ℚ) : W := l.flatMap encodeRat

theorem plStep_iter (l : List ℚ) (acc : List ℚ) :
    plStep^[l.length] (flatR l, listCode ratCode acc) = ([], listCode ratCode (l.reverse ++ acc)) := by
  induction l generalizing acc with
  | nil => simp [flatR]
  | cons y l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    simp only [flatR, List.flatMap_cons] at ih ⊢
    rw [plStep_cons, ih]; simp

theorem plStep_iter_nil (acc : W) : ∀ k, plStep^[k] ([], acc) = ([], acc)
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply, plStep_nil]; exact plStep_iter_nil acc k

theorem length_le_flatR (l : List ℚ) : l.length ≤ (flatR l).length := by
  induction l with
  | nil => simp
  | cons y l ih => simp [flatR, encodeRat] at ih ⊢; omega

theorem plStep_parse (l : List ℚ) :
    (plStep^[(flatR l).length] (flatR l, listCode ratCode [])).2 = listCode ratCode l.reverse := by
  have h := length_le_flatR l
  rw [show (flatR l).length = ((flatR l).length - l.length) + l.length by omega, Function.iterate_add_apply,
    plStep_iter, plStep_iter_nil]
  simp

abbrev pCode : W × W → W := prodCode idW idW

theorem plStep_len (s : W × W) : (pCode (plStep s)).length ≤ (pCode s).length + 18 := by
  simp only [pCode, prodCode, pairBits_length, id]
  unfold plStep
  split_ifs with h
  · omega
  · rcases s with ⟨_ | ⟨x, t⟩, acc⟩
    · simp at h
    · simp only [List.tail_cons, List.length_cons, List.length_append, quoteBits_length, ratWord,
        List.length_singleton]
      have h1 := unframe_len t
      have h2 := unframe_len (unframe t).2
      simp only [List.length_nil, List.length_cons, List.length_append, quoteBits_length] at *
      omega

theorem plStep_iter_len (s : W × W) : ∀ i, (pCode (plStep^[i] s)).length ≤ (pCode s).length + 18 * i
  | 0 => by simp
  | i + 1 => by
    rw [Function.iterate_succ_apply']
    have := plStep_len (plStep^[i] s); have := plStep_iter_len s i; omega

noncomputable def quoteW : Procedure idW idW quoteBits := (quote idW).result (h := quoteBits) (fun _ => rfl)

noncomputable def plStepP : Procedure pCode pCode plStep := by
  let rem := first idW idW
  let acc := second idW idW
  let p1 := unframeP.comp (tail.comp rem)
  let p2 := unframeP.comp ((second idW idW).comp p1)
  let sB : Procedure pCode idW (fun s => [s.1.headD false]) :=
    (cons.comp ((head.comp rem).pair (constant pCode idW []))).congrFun (by intro s; rfl)
  let A := (first idW idW).comp p1
  let D := (first idW idW).comp p2
  let r2 := (second idW idW).comp p2
  let inner := append.comp ((quoteW.comp sB).pair A)
  let rw' := append.comp ((quoteW.comp inner).pair D)
  let newAcc := cons.comp ((constant pCode boolCode true).pair (append.comp ((quoteW.comp rw').pair acc)))
  exact (conditional (isEmpty.comp rem) (identity pCode) (r2.pair newAcc)).congrFun
    (by intro s; by_cases h : s.1.isEmpty = true <;> simp [plStep, ratWord, h, Function.comp])

noncomputable def plIterP : Procedure (prodCode unaryCode pCode) pCode (fun x => plStep^[x.1] x.2) :=
  plStepP.iterate (Polynomial.C 19 * Polynomial.X) (by
    intro n a i hi
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    have := plStep_iter_len a i; nlinarith)

/-- **the price-list parser**: `flatR l ↦ listCode ratCode l`. -/
noncomputable def parseListP : Procedure flatR (listCode ratCode) id := by
  let raw : Procedure idW idW (fun w => (plStep^[w.length] (w, listCode ratCode [])).2) :=
    (second idW idW).comp (plIterP.comp (length.pair ((identity idW).pair (constant idW idW (listCode ratCode [])))))
  let onL : Procedure flatR idW (fun l => listCode ratCode l.reverse) :=
    ((raw.precompose flatR).congrEncoding (fun _ => rfl) (fun _ => rfl)).congrFun (fun l => plStep_parse l)
  exact ((listReverse ratCode 0).comp (onL.result (h := List.reverse) (fun _ => rfl))).congrFun
    (by intro l; simp)

/-- **the query parser**: `eqCode (i, l) ↦ (i, l)` in `prodCode Nat.bits (listCode ratCode)`. -/
noncomputable def parseQueryP :
    Procedure SSG28Machine.eqCode (prodCode Nat.bits (listCode ratCode)) id :=
  (((identity Nat.bits).parallel parseListP).congrEncoding
    (fun a => by simp [prodCode, pairBits, SSG28Machine.eqCode, encodeNat_eq, flatR]) (fun _ => rfl)).congrFun
    (by intro a; rfl)

/-! ## random access into a raw word -/

theorem tail_iter_len (l : W) : ∀ i, (List.tail^[i] l).length ≤ l.length
  | 0 => le_rfl
  | i + 1 => by
    rw [Function.iterate_succ_apply']
    exact (by simp : (List.tail^[i] l).tail.length ≤ (List.tail^[i] l).length).trans (tail_iter_len l i)

theorem tail_iter_eq_drop (l : W) : ∀ i, List.tail^[i] l = l.drop i
  | 0 => rfl
  | i + 1 => by rw [Function.iterate_succ_apply', tail_iter_eq_drop l i, List.tail_drop]

noncomputable def dropP : Procedure (prodCode unaryCode idW) idW (fun x => x.2.drop x.1) :=
  (tail.iterate Polynomial.X (by
    intro n a i _
    simp only [Polynomial.eval_X, id]
    have := tail_iter_len a i; omega)).congrFun (by intro x; exact tail_iter_eq_drop x.2 x.1)

/-- **bit access**: `(p, l) ↦ l.getD p false`. -/
noncomputable def getBitP : Procedure (prodCode unaryCode idW) boolCode (fun x => x.2.getD x.1 false) :=
  (head.comp dropP).congrFun (by
    intro x
    simp only [Function.comp, id]
    rcases x with ⟨p, l⟩
    simp only
    rw [List.getD_eq_getElem?_getD, ← List.head?_drop, List.headD_eq_head?_getD])

end SSG28MachineProc
