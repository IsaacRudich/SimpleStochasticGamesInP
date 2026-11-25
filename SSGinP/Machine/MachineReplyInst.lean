module

public import SSGinP.Machine.MachineReply
public import SSGinP.Machine.MachineProcD2Eval
public import SSGinP.Machine.MachineProcD2Peel

@[expose] public section

/-!
# SSGinP.Machine.MachineReplyInst: instantiating `Blocks` with the table procedures

The table is the `qc`-parameter record `(x.reverse, (n, n))` (`SSG28MachineProcD2.qP`).
Provided here: the start node `startP2` and the evaluation adapter around `FP`.
`blocksOf` takes the two remaining blocks (weights, `okGame`) with their specifications.
-/

set_option linter.unusedSimpArgs false

namespace SSG28MachineReplyInst

open SSG SSG28Reply SSG28MachineReply SSG28MachineProcD2
open OAI.ExactQuantumFactoring.BitStackProgram OAI.ExactQuantumFactoring.BitStackProgram.Procedure

abbrev Q := List Bool × (ℕ × ℕ)

def startT2 (q : Q) : ℕ := ((List.range q.2.2).map (fun i => bitF q.1 q.2.1 i 0 5)).idxOf true

noncomputable def startP2 : Procedure qc Nat.bits startT2 := by
  let step : Procedure iqc boolCode (fun x => bitF x.2.1 x.2.2.1 x.1 0 5) :=
    bitWith iOfIQ (constant iqc Nat.bits 0) (constant iqc Nat.bits 5) qOfIQ
  let tab := (tabulate (f := fun (q : Q) i => bitF q.1 q.2.1 i 0 5) false step).comp (nUOfQ.pair (identity qc))
  exact (unaryToBits.comp (idxTrueP.comp tab)).congrFun (by intro q; rfl)

def evalT2 (x : Q × (List ℚ × ℕ)) : ℚ := FF x.1 x.2.1 x.2.2

noncomputable def evalP2 : Procedure (prodCode qc (prodCode (listCode ratCode) Nat.bits)) ratCode evalT2 := by
  let jP := (second (listCode ratCode) Nat.bits).comp (second qc (prodCode (listCode ratCode) Nat.bits))
  let qP' := first qc (prodCode (listCode ratCode) Nat.bits)
  let vP := (first (listCode ratCode) Nat.bits).comp (second qc (prodCode (listCode ratCode) Nat.bits))
  exact (FP.comp (jP.pair (qP'.pair vP))).congrFun (by intro x; rfl)

theorem start_spec2 (x : List Bool) (h : SSG28Decode.ValidL x.reverse) :
    startT2 (x.reverse, (SSG28Decode.nOf x.reverse, SSG28Decode.nOf x.reverse)) =
      (SSG28Decode.gameOf x.reverse h).startNode.val := rfl

theorem eval_spec2 (x : List Bool) (h : SSG28Decode.ValidL x.reverse) (v : List ℚ)
    (j : Fin (SSG28Decode.nOf x.reverse)) :
    evalT2 ((x.reverse, (SSG28Decode.nOf x.reverse, SSG28Decode.nOf x.reverse)), (v, j.val)) =
      F (SSG28Decode.gameOf x.reverse h) (fun k => v.getD k.val 0) j :=
  FF_eq x.reverse h v j

/-- `Blocks` from the weight and `okGame` procedures on the table `qc`. -/
noncomputable def blocksOf (wtT : Q → List ℚ) (wtP : Procedure qc (listCode ratCode) wtT)
    (wt_spec : ∀ (x : List Bool) (h : SSG28Decode.ValidL x.reverse) (j : Fin (SSG28Decode.nOf x.reverse)),
      (wtT (x.reverse, (SSG28Decode.nOf x.reverse, SSG28Decode.nOf x.reverse))).getD j.val 0 =
        wt (SSG28Decode.gameOf x.reverse h) j)
    (okT : Q → Bool) (okP : Procedure qc boolCode okT)
    (ok_spec : ∀ (x : List Bool) (h : SSG28Decode.ValidL x.reverse),
      okT (x.reverse, (SSG28Decode.nOf x.reverse, SSG28Decode.nOf x.reverse)) =
        okGame (SSG28Decode.gameOf x.reverse h)) : Blocks where
  T := Q
  tc := qc
  tab := fun w => (w.reverse, (SSG28Decode.nOf w.reverse, SSG28Decode.nOf w.reverse))
  tabP := qP
  okT := okT
  okP := okP
  wtT := wtT
  wtP := wtP
  startT := startT2
  startP := startP2
  evalT := evalT2
  evalP := evalP2
  ok_spec := ok_spec
  wt_spec := wt_spec
  start_spec := start_spec2
  eval_spec := fun x h v _ j => eval_spec2 x h v j

/-- **the blocks, instantiated with the table procedures.** -/
noncomputable def blocks : Blocks :=
  blocksOf (fun q => (finalF q).2.2.map (fun c => 2 - 1 / (3 ^ c : ℚ))) wtsP
    (fun x h j => wts_get x.reverse h j) okF okP (fun x h => okF_eq x.reverse h)

/-- **The reply procedure**, the paper's problem (threshold `thetaGe`). -/
noncomputable def replyGe : Procedure (prodCode (id : List Bool → List Bool) SSG28Machine.eqCode) boolCode
    (SSG28Machine.replyL thetaGe) := replyGeP blocks

/-- **The reply procedure**, Condon's strict variant (threshold `thetaGt`). -/
noncomputable def replyGt : Procedure (prodCode (id : List Bool → List Bool) SSG28Machine.eqCode) boolCode
    (SSG28Machine.replyL thetaGt) := replyGtP blocks

end SSG28MachineReplyInst
