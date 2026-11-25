module

public import Mathlib.Data.Nat.Bitwise
public import SSGinP.Values.Strat
public import SSGinP.Values.Statement

@[expose] public section

/-!
# SSGinP.Values.Output: THE OUTPUT WORD as a BitStack `Procedure`

THE ONLY FILE OF THE MACHINE CONSTRUCTION THAT DEPENDS ON THE OUTPUT FORMAT (`SSG.natBits`, `SSG.encodeSolution`
of `SSGinP.Defs`).

* `flattenP`              : concatenation of a list of words.
* `natBitsP`              : `(w, m) ↦ natBits w m` (`w` in unary), by `tabulate` over the bit positions.
* `valWord n y`           : numerator and denominator of `y`, `2 n` bits each.
* `outF w`, `outP`        : the output word from the game word: empty if the `okGame` test fails, else the value
                            words of all nodes, then the max strategy bits, then the min strategy bits.
* `outF_accept`           : on a well-formed Stopping Game with stable assignment `v`,
                            `outF (encode ⟨n, G⟩).reverse = encodeSolution ⟨v, greedyMax G v, greedyMin G v⟩`.
* `outF_reject`           : on every other game, `outF (encode ⟨n, G⟩).reverse = []`.
-/

set_option linter.unusedSimpArgs false

namespace SSGValuesOutput

open SSG SSG28Reply SSGValues SSGValuesLoop SSGValuesStrat SSG28MachineProc SSG28MachineProcD2
open OAI.ExactQuantumFactoring.BitStackProgram OAI.ExactQuantumFactoring.BitStackProgram.Procedure

/-! ## list lemmas -/

theorem foldl_append_flatten (xs : List (List Bool)) (b : List Bool) :
    xs.foldl (fun b a => b ++ a) b = b ++ xs.flatten := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih => simp [ih]

theorem flatten_length_le (xs : List (List Bool)) : xs.flatten.length ≤ (listCode idW xs).length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have e : (idW a).length = a.length := rfl
    simp only [List.flatten_cons, List.length_append, listCode_length_cons]; omega

theorem flatten_singletons {α : Type} (l : List α) (g : α → Bool) : (l.map (fun i => [g i])).flatten = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem range_map_fin {β : Type} (n : ℕ) (g : ℕ → β) :
    (List.range n).map g = (List.finRange n).map (fun i => g i.val) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2; simp

theorem testBit_bits (m b : ℕ) : m.bits.getD b false = m.testBit b := by
  rw [Nat.testBit_eq_inth, List.getI_eq_getElem?_getD, List.getD_eq_getElem?_getD]; rfl

/-! ## concatenation -/

noncomputable def flattenP : Procedure (listCode idW) idW List.flatten := by
  let step : Procedure (prodCode idW idW) idW (fun x : List Bool × List Bool => x.2 ++ x.1) :=
    (append.comp (swap idW idW)).congrFun (by intro x; rfl)
  let fold := foldList ([] : List Bool) step Polynomial.X (by
    intro xs b i
    change ((xs.take i).foldl (fun b a => b ++ a) b).length ≤ _
    rw [foldl_append_flatten]
    have h1 := flatten_length_le (xs.take i)
    have h2 := listCode_length_take_le idW i xs
    simp only [List.length_append, Polynomial.eval_X, idW, id] at *
    omega)
  exact (fold.comp ((identity (listCode idW)).pair (constant (listCode idW) idW []))).congrFun (by
    intro xs
    simp only [Function.comp, id]
    exact (foldl_append_flatten xs []).trans (List.nil_append _))

/-! ## fixed-width binary -/

noncomputable def bitWordP : Procedure (prodCode unaryCode Nat.bits) idW (fun x => [x.2.testBit x.1]) :=
  ((getBitP.precompose (fun x : ℕ × ℕ => (x.1, x.2.bits))).congrEncoding (fun _ => rfl) (fun _ => rfl)).result
    (by intro x; simp only [boolCode, idW, id, testBit_bits])

noncomputable def natBitsP : Procedure (prodCode unaryCode Nat.bits) idW (fun x => natBits x.1 x.2) :=
  (flattenP.comp (tabulate (f := fun (m : ℕ) b => [m.testBit b]) [] bitWordP)).congrFun (by
    intro x; simp only [Function.comp, natBits]; exact flatten_singletons _ _)

/-- the word of one value: numerator and denominator, `2 n` bits each. -/
def valWord (n : ℕ) (y : ℚ) : List Bool := natBits (2 * n) y.num.natAbs ++ natBits (2 * n) y.den

noncomputable def valWordP : Procedure (prodCode unaryCode ratCode) idW (fun x => valWord x.1 x.2) := by
  let e := prodCode unaryCode ratCode
  let nU := first unaryCode ratCode
  let y := second unaryCode ratCode
  let w2 := unaryMul.comp ((constant e unaryCode 2).pair nU)
  exact (append.comp ((natBitsP.comp (w2.pair (intAbs.comp (ratNum.comp y)))).pair
    (natBitsP.comp (w2.pair (ratDen.comp y))))).congrFun (by intro x; rfl)

/-! ## the three parts of the output -/

abbrev nyC : ℕ × List ℚ → List Bool := prodCode unaryCode (listCode ratCode)

def valsWordF (n : ℕ) (ys : List ℚ) : List Bool :=
  ((List.range n).map (fun i => valWord n (ys.getD i 0))).flatten

noncomputable def valsWordP : Procedure nyC idW (fun x => valsWordF x.1 x.2) := by
  let e := prodCode unaryCode nyC
  let iB := unaryToBits.comp (first unaryCode nyC)
  let nU := (first unaryCode (listCode ratCode)).comp (second unaryCode nyC)
  let ys := (second unaryCode (listCode ratCode)).comp (second unaryCode nyC)
  let stepV : Procedure e idW (fun x => valWord x.2.1 (x.2.2.getD x.1 0)) :=
    (valWordP.comp (nU.pair (SSG28MachineReply.getQ.comp (iB.pair ys)))).congrFun (by intro x; rfl)
  exact (flattenP.comp ((tabulate (f := fun (c : ℕ × List ℚ) i => valWord c.1 (c.2.getD i 0)) [] stepV).comp
    ((first unaryCode (listCode ratCode)).pair (identity nyC)))).congrFun (by intro x; rfl)

def maxWordF (q : Q) (ys : List ℚ) : List Bool := ((List.range q.2.2).map (fun i => [gmaxF q ys i])).flatten
def minWordF (q : Q) (ys : List ℚ) : List Bool := ((List.range q.2.2).map (fun i => [gminF q ys i])).flatten

noncomputable def nOfQY : Procedure qyC unaryCode (fun x => x.1.2.2) := nUOfQ.comp (first qc (listCode ratCode))

noncomputable def maxWordP : Procedure qyC idW (fun x => maxWordF x.1 x.2) :=
  (flattenP.comp ((tabulate (f := fun (c : Q × List ℚ) i => [gmaxF c.1 c.2 i]) []
    (gmaxP.result (by intro x; rfl))).comp (nOfQY.pair (identity qyC)))).congrFun (by intro x; rfl)

noncomputable def minWordP : Procedure qyC idW (fun x => minWordF x.1 x.2) :=
  (flattenP.comp ((tabulate (f := fun (c : Q × List ℚ) i => [gminF c.1 c.2 i]) []
    (gminP.result (by intro x; rfl))).comp (nOfQY.pair (identity qyC)))).congrFun (by intro x; rfl)

/-! ## the output word -/

/-- **the output word**, from the game word `w`. -/
noncomputable def outF (w : List Bool) : List Bool :=
  if okF (w.reverse, (SSG28Decode.nOf w.reverse, SSG28Decode.nOf w.reverse)) then
    (valsWordF (SSG28Decode.nOf w.reverse) (valuesF w) ++
      maxWordF (w.reverse, (SSG28Decode.nOf w.reverse, SSG28Decode.nOf w.reverse)) (valuesF w)) ++
      minWordF (w.reverse, (SSG28Decode.nOf w.reverse, SSG28Decode.nOf w.reverse)) (valuesF w)
  else []

/-- **the output word as a procedure.** -/
noncomputable def outP : Procedure idW idW outF := by
  let qy : Procedure idW qyC (fun w => ((w.reverse, (SSG28Decode.nOf w.reverse, SSG28Decode.nOf w.reverse)),
      valuesF w)) := qP.pair valuesP
  let vw := valsWordP.comp (nUP.pair valuesP)
  let body := append.comp ((append.comp (vw.pair (maxWordP.comp qy))).pair (minWordP.comp qy))
  exact (conditional (okP.comp qP) body (constant idW idW [])).congrFun (by intro w; rfl)

/-! ## specification -/

theorem valsWordF_spec (n : ℕ) (v : Fin n → ℚ) (h0 : ∀ i, 0 ≤ v i) :
    valsWordF n (List.ofFn v) =
      (List.finRange n).flatMap fun i => natBits (2 * n) (v i).num.toNat ++ natBits (2 * n) (v i).den := by
  unfold valsWordF
  rw [range_map_fin, List.flatMap_def]
  congr 1
  apply List.map_congr_left
  intro i _
  have e : (List.ofFn v).getD i.val 0 = v i := by simp [List.getD_eq_getElem?_getD]
  have hn : 0 ≤ (v i).num := Rat.num_nonneg.mpr (h0 i)
  have e2 : (v i).num.natAbs = (v i).num.toNat := by omega
  rw [e]; unfold valWord; rw [e2]

/-- **acceptance**: on a well-formed Stopping Game the output word is the word of the exact values and their
greedy strategies. -/
theorem outF_accept (n : ℕ) (G : Game n) (hw : WellFormed G) (hs : StoppingGame G) (v : Fin n → ℚ)
    (hv : F G v = v) :
    outF (encode ⟨n, G⟩).reverse = encodeSolution ⟨v, greedyMax G v, greedyMin G v⟩ := by
  have hn : SSG28Decode.nOf ((encode ⟨n, G⟩).reverse).reverse = n := by
    rw [List.reverse_reverse]; exact SSGinP.nOf_encode G
  have hd := SSGinP.decode_encode ⟨n, G⟩
  have hr := prank_ranked G (peelAll_of_stoppingGame G hs)
  have hb := fix_bounds G (prank G) hr v hv
  unfold outF
  rw [hn, okF_spec _ n G hd, (okGame_iff G).mpr ⟨hw, hs⟩, if_pos rfl, valuesF_spec n G hw hs v hv,
    valsWordF_spec n v (fun i => (hb i).1)]
  unfold encodeSolution maxWordF minWordF
  simp only
  rw [flatten_singletons, flatten_singletons, range_map_fin, range_map_fin]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) rfl ?_) ?_
  · exact List.map_congr_left fun i _ => gmaxF_spec _ n G hd v i
  · exact List.map_congr_left fun i _ => gminF_spec _ n G hd v i

/-- **rejection**: on a game that is not a well-formed Stopping Game the output is the empty word. -/
theorem outF_reject (n : ℕ) (G : Game n) (h : ¬ (WellFormed G ∧ StoppingGame G)) :
    outF (encode ⟨n, G⟩).reverse = [] := by
  have hn : SSG28Decode.nOf ((encode ⟨n, G⟩).reverse).reverse = n := by
    rw [List.reverse_reverse]; exact SSGinP.nOf_encode G
  have hd := SSGinP.decode_encode ⟨n, G⟩
  have hok : okGame G = false := by
    rw [← Bool.not_eq_true]; exact fun h' => h ((okGame_iff G).mp h')
  unfold outF
  rw [hn, okF_spec _ n G hd, hok]
  rfl

end SSGValuesOutput
