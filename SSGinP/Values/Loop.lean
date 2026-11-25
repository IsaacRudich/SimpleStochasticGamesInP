module

public import SSGinP.Values.Call
public import SSGinP.Values.Euclid

@[expose] public section

/-!
# SSGinP.Values.Loop: the bisection loop and the exact values of all nodes as a `Procedure`

* `cStep`, `cStepP`  : one bisection step on the context `(w, (k, (a, j)))`: one engine call `callG` on the context
                       word itself, then `a ↦ 2a+1` or `2a`, `j ↦ j+1`. The context word grows by at most 3 bits.
* `bisP`             : the loop (`Procedure.iterateLinear`).
* `nodeVal (w, n) k` : `4n+1` steps from `(w, (k, (0, 0)))`, then the reconstruction `exactOf n`.
* `valuesF w`, `valuesP` : the list of the values of all nodes, by `tabulate`.
* `valuesF_spec`     : on the word of a well-formed Stopping Game with stable assignment `v`,
                       `valuesF ((encode ⟨n, G⟩).reverse) = List.ofFn v`.
-/

set_option linter.unusedSimpArgs false

namespace SSGValuesLoop

open SSG SSG28Reply SSGValues SSGValuesCtx SSGValuesCall SSGValuesEuclid SSG28MachineProc
open OAI.ExactQuantumFactoring.BitStackProgram OAI.ExactQuantumFactoring.BitStackProgram.Procedure

/-! ## the bisection loop -/

/-- one bisection step; the state is the context of the engine call. -/
noncomputable def cStep (c : Ctx) : Ctx :=
  (c.1, (c.2.1, (if callG (ctxCode c) then 2 * c.2.2.1 + 1 else 2 * c.2.2.1, c.2.2.2 + 1)))

noncomputable def callC : Procedure ctxCode boolCode (fun c => callG (ctxCode c)) :=
  (callP.precompose ctxCode).congrEncoding (fun _ => rfl) (fun _ => rfl)

noncomputable def cStepP : Procedure ctxCode ctxCode cStep := by
  let wP := first idW (prodCode Nat.bits (prodCode Nat.bits unaryCode))
  let rest := second idW (prodCode Nat.bits (prodCode Nat.bits unaryCode))
  let kP := (first Nat.bits (prodCode Nat.bits unaryCode)).comp rest
  let aj := (second Nat.bits (prodCode Nat.bits unaryCode)).comp rest
  let aP := (first Nat.bits unaryCode).comp aj
  let jP := (second Nat.bits unaryCode).comp aj
  let newA := conditional callC (doubleOne.comp aP) (double.comp aP)
  exact (wP.pair (kP.pair (newA.pair (unarySuccessor.comp jP)))).congrFun (by intro c; rfl)

theorem bit_len (b : Bool) (a : ℕ) : (if b then 2 * a + 1 else 2 * a).bits.length ≤ a.bits.length + 1 := by
  cases b
  · simp [double_bits_length a]
  · simpa using doubleOne_bits_length a

theorem cStep_len (c : Ctx) : (ctxCode (cStep c)).length ≤ (ctxCode c).length + 3 := by
  obtain ⟨w, k, a, j⟩ := c
  have h3 := bit_len (callG (ctxCode (w, (k, (a, j))))) a
  simp only [ctxCode, cStep, prodCode, pairBits_length, unaryCode, List.length_replicate, idW, id] at h3 ⊢
  omega

noncomputable def bisP : Procedure (prodCode unaryCode ctxCode) ctxCode (fun x => cStep^[x.1] x.2) :=
  cStepP.iterateLinear 3 cStep_len

/-- the test asked for node `k` of the game word `w`. -/
noncomputable def testOf (w : List Bool) (k : ℕ) (a j : ℕ) : Bool := callG (ctxCode (w, (k, (a, j))))

theorem cStep_iter (w : List Bool) (k : ℕ) (s : ℕ × ℕ) :
    ∀ m, cStep^[m] (w, (k, s)) = (w, (k, (bStep (testOf w k))^[m] s))
  | 0 => rfl
  | m + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', cStep_iter w k s m]
    rfl

/-! ## the value of one node, and of all nodes -/

/-- the value computed for node `k` from the game word and `n`. -/
noncomputable def nodeVal (wn : List Bool × ℕ) (k : ℕ) : ℚ :=
  exactOf wn.2 (cStep^[4 * wn.2 + 1] (wn.1, (k, (0, 0)))).2.2.1

theorem nodeVal_eq (w : List Bool) (n k : ℕ) : nodeVal (w, n) k = valueBy (testOf w k) n := by
  unfold nodeVal valueBy stepsX
  rw [cStep_iter]

abbrev wnC : List Bool × ℕ → List Bool := prodCode idW unaryCode

noncomputable def nodeValP : Procedure (prodCode unaryCode wnC) ratCode (fun x => nodeVal x.2 x.1) := by
  let e := prodCode unaryCode wnC
  let kB := unaryToBits.comp (first unaryCode wnC)
  let wP := (first idW unaryCode).comp (second unaryCode wnC)
  let nU := (second idW unaryCode).comp (second unaryCode wnC)
  let m41 := unarySuccessor.comp (unaryMul.comp ((constant e unaryCode 4).pair nU))
  let c0 : Procedure e ctxCode (fun x => (x.2.1, (x.1, (0, 0)))) :=
    (wP.pair (kB.pair ((constant e Nat.bits 0).pair (constant e unaryCode 0)))).congrFun (by intro x; rfl)
  let fin := bisP.comp (m41.pair c0)
  let aP := (first Nat.bits unaryCode).comp ((second Nat.bits (prodCode Nat.bits unaryCode)).comp
    ((second idW (prodCode Nat.bits (prodCode Nat.bits unaryCode))).comp fin))
  exact (exactP.comp (nU.pair aP)).congrFun (by
    intro x; simp only [Function.comp, nodeVal, Nat.succ_eq_add_one, id])

/-- **the values of all nodes**, from the game word. -/
noncomputable def valuesF (w : List Bool) : List ℚ :=
  (List.range (SSG28Decode.nOf w.reverse)).map (nodeVal (w, SSG28Decode.nOf w.reverse))

noncomputable def valuesP : Procedure idW (listCode ratCode) valuesF :=
  ((tabulate (0 : ℚ) nodeValP).comp (SSG28MachineProcD2.nUP.pair ((identity idW).pair SSG28MachineProcD2.nUP))).congrFun
    (by intro w; rfl)

/-- **specification**: on a well-formed Stopping Game the values are exact. -/
theorem valuesF_spec (n : ℕ) (G : Game n) (hw : WellFormed G) (hs : StoppingGame G) (v : Fin n → ℚ)
    (hv : F G v = v) : valuesF (encode ⟨n, G⟩).reverse = List.ofFn v := by
  have hn : SSG28Decode.nOf ((encode ⟨n, G⟩).reverse).reverse = n := by
    rw [List.reverse_reverse]; exact SSGinP.nOf_encode G
  have hr := prank_ranked G (peelAll_of_stoppingGame G hs)
  have hb := fix_bounds G (prank G) hr v hv
  unfold valuesF
  rw [hn]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    rw [nodeVal_eq]
    apply valueBy_exact _ n (v ⟨i, hi⟩) _ (hb ⟨i, hi⟩) (value_den G hs v hv ⟨i, hi⟩)
    intro a j
    exact callG_spec _ n G ⟨i, hi⟩ a j rfl hw hs v hv

end SSGValuesLoop
