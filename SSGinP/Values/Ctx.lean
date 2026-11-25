module

public import SSGinP.Values.Exact
public import SSGinP.Values.Machine
public import SSGinP.Machine.Machine
public import SSGinP.Machine.MachineReplyInst

@[expose] public section

/-!
# SSGinP.Values.Ctx: the reply procedure of one engine call, with the node and the threshold
# taken from a context word

Context `c = (w, (k, (a, j)))`: the game word `w` (`SSG28Decode.decode w = some ⟨n, G⟩`), a node `k`, and the
bisection state `(a, j)`; the threshold is `thr a j = (2a+1)/2^(j+1)`.  It is written as the word
`ctxCode c = prodCode id (prodCode Nat.bits (prodCode Nat.bits unaryCode)) c`.

* `parse`, `parseP`, `parse_ctxCode` : reading a context back from a raw word (total on all words).
* `rV (x, query)`                    : the reply bit computed from the raw context word `x` and a query.
* `repV`                             : `rV` as a BitStack `Procedure`.
* `rT_spec`                          : on a context of a game `G`, the reply is
                                       `ssgReply (withStart G k) (thr a j) (rDelta n)` (the oracle of
                                       `SSGValues.callOracle`).
For queries at goods `≠ 0` the existing procedure `SSG28MachineReply.mainP` is reused unchanged (its threshold
and start node are not read there); only the good `0` (the threshold comparison at node `k`) is new.
-/

set_option linter.unusedSimpArgs false

namespace SSGValuesCtx

open SSG SSG28Reply SSG28Search SSGValues SSG28Machine SSG28MachineProc SSG28MachineReplyInst
open OAI.ExactQuantumFactoring.BitStackProgram OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec
open SSG28MachineReply (Blocks loElem hiElem bitF repF repF_eq getD_map_range getQ ltQ ctxC cT cN cNB cI cL loP mainF mainP inC)

variable {n : ℕ}

/-! ## moving the start node changes nothing but the start node -/

theorem prank_withStart (G : Game n) (k : Fin n) : prank (withStart G k) = prank G := by
  funext i; unfold prank; simp only [peel_withStart]

theorem wt_withStart (G : Game n) (k : Fin n) : wt (withStart G k) = wt G := by
  funext i; unfold wt; rw [prank_withStart]

theorem okGame_withStart (G : Game n) (k : Fin n) : okGame (withStart G k) = okGame G := by
  have h2 : peelAll (withStart G k) = peelAll G := by unfold peelAll; simp only [peel_withStart]
  unfold okGame; rw [h2]; rfl

theorem lo_withStart (G : Game n) (k : Fin n) : SSG28Reply.lo (withStart G k) = SSG28Reply.lo G := by
  funext δ q j; unfold SSG28Reply.lo; rw [wt_withStart]

theorem hi_withStart (G : Game n) (k : Fin n) : SSG28Reply.hi (withStart G k) = SSG28Reply.hi G := by
  funext δ q j; unfold SSG28Reply.hi; rw [wt_withStart]

theorem replyGood_withStart_ne (G : Game n) (k : Fin n) (θ θ' δ : ℚ) (g : Fin (2*n+1)) (q : Fin (2*n+1) → ℚ)
    (hg : g.val ≠ 0) : replyGood (withStart G k) θ δ g q = replyGood G θ' δ g q := by
  unfold replyGood
  rw [dif_neg hg, dif_neg hg, lo_withStart, hi_withStart]
  rfl

theorem replyGood_withStart_zero (G : Game n) (k : Fin n) (θ δ : ℚ) (g : Fin (2*n+1)) (q : Fin (2*n+1) → ℚ)
    (hg : g.val = 0) : replyGood (withStart G k) θ δ g q = decide (θ < SSG28Reply.lo G δ q k) := by
  unfold replyGood
  rw [dif_pos hg, lo_withStart]
  rfl

/-! ## the context word -/

abbrev Ctx := List Bool × (ℕ × (ℕ × ℕ))
abbrev ctxCode : Ctx → List Bool := prodCode idW (prodCode Nat.bits (prodCode Nat.bits unaryCode))

/-- reading a context from a raw word (total). -/
def parse (x : List Bool) : Ctx :=
  ((unframe x).1, (binaryValue (unframe (unframe x).2).1,
    (binaryValue (unframe (unframe (unframe x).2).2).1, (unframe (unframe (unframe x).2).2).2.length)))

theorem parse_ctxCode (c : Ctx) : parse (ctxCode c) = c := by
  obtain ⟨w, k, a, j⟩ := c
  simp only [parse, ctxCode, prodCode, OAI.ExactQuantumFactoring.BitStackProgram.pairBits, unframe_frame, binaryValue_bits, idW, id, unaryCode,
    List.length_replicate]

noncomputable def parseP : Procedure idW ctxCode parse := by
  let u1 := unframeP
  let r1 := (second idW idW).comp u1
  let u2 := unframeP.comp r1
  let r2 := (second idW idW).comp u2
  let u3 := unframeP.comp r2
  exact (((first idW idW).comp u1).pair ((normalize.comp ((first idW idW).comp u2)).pair
    ((normalize.comp ((first idW idW).comp u3)).pair (length.comp ((second idW idW).comp u3))))).congrFun
      (by intro x; rfl)

/-! ## the threshold -/

theorem iterate_double (i a : ℕ) : (fun n => 2 * n)^[i] a = 2 ^ i * a := by
  induction i generalizing a with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih]; ring

noncomputable def pow2P : Procedure (prodCode unaryCode Nat.bits) Nat.bits (fun x => 2 ^ x.1 * x.2) :=
  (double.iterateLinear 1 double_bits_length).congrFun (by intro x; exact iterate_double x.1 x.2)

/-- the threshold `thr a j` from procedures for `a` (binary) and `j` (unary). -/
noncomputable def thrP {α : Type} {ea : α → List Bool} {fa fj : α → ℕ} (pa : Procedure ea Nat.bits fa)
    (pj : Procedure ea unaryCode fj) : Procedure ea ratCode (fun x => thr (fa x) (fj x)) :=
  (ratDiv.comp ((natToRat.comp (doubleOne.comp pa)).pair
    (natToRat.comp (pow2P.comp ((unarySuccessor.comp pj).pair (constant ea Nat.bits 1)))))).congrFun (by
      intro x; simp only [Function.comp, thr, Nat.succ_eq_add_one]; push_cast; ring)

/-! ## the reply on `(table, n, query)` plus `(k, θ)` -/

abbrev Env := SSG28MachineReply.Ctx blocks × (ℕ × ℚ)
noncomputable abbrev envC : Env → List Bool := prodCode (ctxC blocks) (prodCode Nat.bits ratCode)

/-- the reply bit: at the good `0` the comparison of the threshold with `lo` at node `k`; at the other goods the
existing `mainF` (which does not read the threshold or the start node there). -/
noncomputable def mainV (e : Env) : Bool :=
  if e.1.2.2.1 = 0 then
    (decide (e.1.2.2.2.length = 2 * e.1.2.1 + 1) && blocks.okT e.1.1) &&
      decide (e.2.2 < ((List.range e.1.2.1).map
        (loElem (rDelta e.1.2.1, (blocks.wtT e.1.1, (e.1.2.2.2, e.1.2.1))))).getD e.2.1 0)
  else mainF blocks (θ := fun _ => 0) e.1

noncomputable def mainVP : Procedure envC boolCode mainV := by
  let c := first (ctxC blocks) (prodCode Nat.bits ratCode)
  let kP := (first Nat.bits ratCode).comp (second (ctxC blocks) (prodCode Nat.bits ratCode))
  let thP := (second Nat.bits ratCode).comp (second (ctxC blocks) (prodCode Nat.bits ratCode))
  let twoN1 := successor.comp (binaryMul.comp ((constant envC Nat.bits 2).pair ((cNB blocks).comp c)))
  let d2 := SSG28MachineProcD2.eqP.comp (((listLength ratCode 0).comp ((cL blocks).comp c)).pair twoN1)
  let ok := blocks.okP.comp ((cT blocks).comp c)
  let b0 := ltQ.comp (thP.pair (getQ.comp (kP.pair ((loP blocks).comp c))))
  exact (conditional (binaryZero.comp ((cI blocks).comp c)) (boolAnd.comp ((boolAnd.comp (d2.pair ok)).pair b0))
    ((mainP blocks (constant unaryCode ratCode (0 : ℚ))).comp c)).congrFun (by
      intro e
      simp only [mainV, Function.comp, Nat.succ_eq_add_one]
      by_cases h0 : e.1.2.2.1 = 0
      · simp [h0]
      · simp [h0])

/-- the reply from a typed context and a query. -/
noncomputable def rT (x : Ctx × (ℕ × List ℚ)) : Bool :=
  if SSG28MachineProcD2.validF x.1.1 then
    mainV ((blocks.tab x.1.1, (SSG28Decode.nOf x.1.1.reverse, x.2)), (x.1.2.1, thr x.1.2.2.1 x.1.2.2.2))
  else false

/-- **the reply from the raw context word and a query.** -/
noncomputable def rV (xa : List Bool × (ℕ × List ℚ)) : Bool := rT (parse xa.1, xa.2)

/-- **the reply procedure.** -/
noncomputable def repV : Procedure inC boolCode rV := by
  let xP := first idW eqCode
  let cP := parseP.comp xP
  let wP := (first idW (prodCode Nat.bits (prodCode Nat.bits unaryCode))).comp cP
  let rest := (second idW (prodCode Nat.bits (prodCode Nat.bits unaryCode))).comp cP
  let kP := (first Nat.bits (prodCode Nat.bits unaryCode)).comp rest
  let aj := (second Nat.bits (prodCode Nat.bits unaryCode)).comp rest
  let aP := (first Nat.bits unaryCode).comp aj
  let jP := (second Nat.bits unaryCode).comp aj
  let qP : Procedure inC (prodCode Nat.bits (listCode ratCode)) (fun xa => xa.2) :=
    (parseQueryP.comp (second idW eqCode)).congrFun (fun _ => rfl)
  let env := ((blocks.tabP.comp wP).pair ((SSG28MachineProcD2.nUP.comp wP).pair qP)).pair (kP.pair (thrP aP jP))
  exact (conditional (SSG28MachineProcD2.validFP.comp wP) (mainVP.comp env) (constant inC boolCode false)).congrFun
    (by intro xa; rfl)

/-! ## specification -/

/-- **the reply is the oracle of the call** for node `k` and threshold `thr a j`. -/
theorem rT_spec (w : List Bool) (n : ℕ) (G : Game n) (hd : SSG28Decode.decode w = some ⟨n, G⟩) (k : Fin n)
    (a j : ℕ) (qa : ℕ × List ℚ) :
    rT ((w, (k.val, (a, j))), qa) = ssgReply (withStart G k) (thr a j) (rDelta n) (eqCode qa) := by
  unfold SSG28Decode.decode at hd
  split_ifs at hd with hv
  cases hd
  have hdec : SSG28Decode.decode w = some ⟨SSG28Decode.nOf w.reverse, SSG28Decode.gameOf w.reverse hv⟩ := by
    simp [SSG28Decode.decode, hv]
  rw [ssgReply_eqCode]
  have hvalid : SSG28MachineProcD2.validF w = true := by
    rw [SSG28MachineProcD2.validF_eq]; exact decide_eq_true hv
  unfold rT
  simp only [hvalid, if_true]
  obtain ⟨i, l⟩ := qa
  by_cases hi0 : i = 0
  · subst hi0
    unfold mainV
    simp only [if_true]
    by_cases hlen : l.length = 2 * SSG28Decode.nOf w.reverse + 1
    · rw [dif_pos ⟨by omega, hlen⟩, replyGood_withStart_zero _ _ _ _ _ _ rfl, okGame_withStart,
        blocks.ok_spec w hv]
      simp only [hlen, decide_true, Bool.true_and]
      congr 2
      rw [getD_map_range _ _ _ k.2]
      unfold loElem SSG28Reply.lo
      rw [blocks.wt_spec w hv k]
      have hql : ∀ m (hm : m < 2 * SSG28Decode.nOf w.reverse + 1), l.getD m 0 = l.get ⟨m, by omega⟩ := by
        intro m hm; simp [List.getD_eq_getElem?_getD, hlen ▸ hm]
      simp only
      rw [hql (1 + k.val) (by omega), hql 0 (by omega)]
      rfl
    · rw [dif_neg (fun h => hlen h.2)]
      simp [hlen]
  · unfold mainV
    rw [if_neg hi0]
    have h := repF_eq blocks (fun _ => 0) (w, (i, l))
    unfold repF at h
    simp only [hvalid, if_true] at h
    have e1 : mainF blocks (θ := fun _ => 0) (blocks.tab w, (SSG28Decode.nOf w.reverse, (i, l))) =
        replyL (fun _ => 0) (w, (i, l)) := h
    rw [e1]
    unfold replyL
    rw [hdec]
    simp only
    by_cases hdim : i < 2 * SSG28Decode.nOf w.reverse + 1 ∧ l.length = 2 * SSG28Decode.nOf w.reverse + 1
    · rw [dif_pos hdim, dif_pos hdim, okGame_withStart, replyGood_withStart_ne _ _ _ 0 _ _ _ hi0]
    · rw [dif_neg hdim, dif_neg hdim]

end SSGValuesCtx
