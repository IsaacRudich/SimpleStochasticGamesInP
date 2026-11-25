module

public import OAI.Computability.QuantumFactoring.BitStackAdder
public import OAI.Computability.QuantumFactoring.BitStackBasicProcedures
public import OAI.Computability.QuantumFactoring.BitStackBinaryBasics
public import OAI.Computability.QuantumFactoring.BitStackBooleans
public import OAI.Computability.QuantumFactoring.BitStackChoice
public import OAI.Computability.QuantumFactoring.BitStackComposition
public import OAI.Computability.QuantumFactoring.BitStackConstants
public import OAI.Computability.QuantumFactoring.BitStackDivision
public import OAI.Computability.QuantumFactoring.BitStackFold
public import OAI.Computability.QuantumFactoring.BitStackFrames
public import OAI.Computability.QuantumFactoring.BitStackGCD
public import OAI.Computability.QuantumFactoring.BitStackIncrement
public import OAI.Computability.QuantumFactoring.BitStackIntegers
public import OAI.Computability.QuantumFactoring.BitStackIteration
public import OAI.Computability.QuantumFactoring.BitStackListCode
public import OAI.Computability.QuantumFactoring.BitStackListFold
public import OAI.Computability.QuantumFactoring.BitStackListIndex
public import OAI.Computability.QuantumFactoring.BitStackListLength
public import OAI.Computability.QuantumFactoring.BitStackListOps
public import OAI.Computability.QuantumFactoring.BitStackLists
public import OAI.Computability.QuantumFactoring.BitStackMultiplier
public import OAI.Computability.QuantumFactoring.BitStackNaturals
public import OAI.Computability.QuantumFactoring.BitStackProcedures
public import OAI.Computability.QuantumFactoring.BitStackProducts
public import OAI.Computability.QuantumFactoring.BitStackPrograms
public import OAI.Computability.QuantumFactoring.BitStackQuotation
public import OAI.Computability.QuantumFactoring.BitStackRationalDivision
public import OAI.Computability.QuantumFactoring.BitStackRationalFloor
public import OAI.Computability.QuantumFactoring.BitStackRationals
public import OAI.Computability.QuantumFactoring.BitStackRelabel
public import OAI.Computability.QuantumFactoring.BitStackSubtractor
public import OAI.Computability.QuantumFactoring.BitStackSums
public import OAI.Computability.QuantumFactoring.BitStackTabulate
public import OAI.Computability.QuantumFactoring.BitStackUnary
public import OAI.Computability.QuantumFactoring.BitStackWords
public import OAI.Computability.QuantumFactoring.Procedure
public import OAI.Computability.QuantumFactoring.ProcedureFurther
public import SSGinP.Machine.Reply
public import OAI.Optimization.LinearProgramming.OracleSpec.ArithmeticEncoding

@[expose] public section

/-!
# SSGinP.Machine.MachineProcD2Driver: the driver procedure, from the input word to the public
input of the sign-recovery machine, `SSG28Reply.driverW`.
-/

namespace SSG28MachineProcD2

open OAI.ExactQuantumFactoring.BitStackProgram OAI.ExactQuantumFactoring.BitStackProgram.Procedure

/-- prepend a fixed bit to a `listCode boolCode` list. -/
noncomputable def consBit (b : Bool) :
    Procedure (listCode boolCode) (listCode boolCode) (fun xs => b :: xs) :=
  ((listCons boolCode).comp ((constant (listCode boolCode) boolCode b).pair
    (identity (listCode boolCode)))).congrFun (by intro xs; rfl)

theorem foldl_cons_rev (w : List Bool) (acc : List Bool) :
    w.foldl (bitAction (fun xs => false :: xs) (fun xs => true :: xs)) acc = w.reverse ++ acc := by
  induction w generalizing acc with
  | nil => rfl
  | cons b w ih =>
    simp only [List.foldl_cons, ih, List.reverse_cons, List.append_assoc, List.singleton_append]
    cases b <;> rfl

/-- **the input word, reversed, as a list of bits** (`w.reverse` is the layout `l`). -/
noncomputable def toListP : Procedure (id : List Bool → List Bool) (listCode boolCode) List.reverse :=
  ((foldBitsLinear (consBit false) (consBit true) 4 (by intro a; simp [listCode_length_cons]; omega)
      (by intro a; simp [listCode_length_cons]; omega)).comp
    ((identity (id : List Bool → List Bool)).pair (constant id (listCode boolCode) []))).congrFun
    (by intro w; simp [foldl_cons_rev])


/-! ### Counting `true`s (unary) -/

theorem fold_countTrue (xs : List Bool) (c : ℕ) :
    xs.foldl (fun c b => if b then c + 1 else c) c = c + xs.count true := by
  induction xs generalizing c with
  | nil => simp
  | cons b xs ih =>
    simp only [List.foldl_cons, ih, List.count_cons]
    cases b <;> simp <;> omega

/-- the number of `true`s of a bit list, in unary. -/
noncomputable def countTrueP : Procedure (listCode boolCode) unaryCode (fun xs => xs.count true) := by
  let step : Procedure (prodCode boolCode unaryCode) unaryCode (fun x => if x.1 then x.2 + 1 else x.2) :=
    ((choose (identity unaryCode) unarySuccessor).congrFun (by intro x; rfl))
  let rep := foldList false step Polynomial.X (by
    intro xs c i
    change (unaryCode ((xs.take i).foldl (fun c b => if b then c + 1 else c) c)).length ≤ _
    rw [fold_countTrue]
    simp only [unaryCode, List.length_replicate, Polynomial.eval_X]
    have h1 := List.count_le_length (a := true) (l := xs.take i)
    have h2 := list_length_le_code boolCode xs
    simp only [List.length_take] at h1
    omega)
  exact (rep.comp ((identity (listCode boolCode)).pair (constant (listCode boolCode) unaryCode 0))).congrFun
    (by intro xs; simp [fold_countTrue])

/-! ### `n` from the input length -/

/-- the test `10 (k+1)^2 ≤ m` used to read off `n = ⌊√(m/10)⌋`. -/
def sqTest (m k : ℕ) : Bool := decide (10 * ((k + 1) * (k + 1)) ≤ m)

theorem sqTest_iff (m k : ℕ) : sqTest m k = true ↔ k < Nat.sqrt (m / 10) := by
  unfold sqTest
  rw [decide_eq_true_iff, ← Nat.succ_le_iff, Nat.le_sqrt, Nat.le_div_iff_mul_le (by norm_num)]
  constructor <;> intro h <;> linarith

theorem countP_range_lt (m s : ℕ) : ((List.range m).map (fun k => decide (k < s))).count true = min s m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.count_append, ih]
    by_cases h : m < s <;> simp [h] <;> omega

theorem sqrt_le_self_div (m : ℕ) : Nat.sqrt (m / 10) ≤ m := by
  have := Nat.sqrt_le_self (m / 10)
  have : m / 10 ≤ m := Nat.div_le_self m 10
  omega

theorem count_sqTest (m : ℕ) : ((List.range m).map (sqTest m)).count true = Nat.sqrt (m / 10) := by
  have h : (List.range m).map (sqTest m) = (List.range m).map (fun k => decide (k < Nat.sqrt (m / 10))) := by
    apply List.map_congr_left; intro k _
    rw [Bool.eq_iff_iff, sqTest_iff, decide_eq_true_iff]
  rw [h, countP_range_lt]; have := sqrt_le_self_div m; omega

/-- `sqTest` as a procedure on (k unary, m unary). -/
noncomputable def sqTestP : Procedure (prodCode unaryCode unaryCode) boolCode (fun x => sqTest x.2 x.1) := by
  let k := unaryToBits.comp (first unaryCode unaryCode)
  let m := unaryToBits.comp (second unaryCode unaryCode)
  let k1 := successor.comp k
  let sq := binaryMul.comp (k1.pair k1)
  let ten := binaryMul.comp ((constant (prodCode unaryCode unaryCode) Nat.bits 10).pair sq)
  exact (binaryLe.comp (ten.pair m)).congrFun (by intro x; rfl)

/-- **`n` of the input word**: `nOf w.reverse = ⌊√(|w|/10)⌋`, in binary. -/
noncomputable def nP : Procedure (id : List Bool → List Bool) Nat.bits
    (fun w => SSG28Decode.nOf w.reverse) := by
  let tab := (tabulate false sqTestP).comp ((length).pair (length))
  exact (unaryToBits.comp (countTrueP.comp tab)).congrFun (by
    intro w
    simp only [Function.comp_apply, id_eq, SSG28Decode.nOf, List.length_reverse]
    exact count_sqTest w.length)


/-- `n` of the input word in unary. -/
noncomputable def nUP : Procedure (id : List Bool → List Bool) unaryCode
    (fun w => SSG28Decode.nOf w.reverse) :=
  (countTrueP.comp ((tabulate false sqTestP).comp ((length).pair (length)))).congrFun (by
    intro w
    simp only [Function.comp_apply, id_eq, SSG28Decode.nOf, List.length_reverse]
    exact count_sqTest w.length)

/-! ### The numbers of the public input and their encoding -/

open OAI.Optimization.LinearProgramming.OracleSpec in
/-- `encodeNat`, as a procedure into raw words. -/
noncomputable def encP : Procedure Nat.bits (id : List Bool → List Bool) encodeNat :=
  (quote Nat.bits).result (by intro a; exact quoteBits_eq_frame a.bits)

/-- multiplication by 27. -/
noncomputable def mul27 : Procedure Nat.bits Nat.bits (fun x => 27 * x) :=
  (binaryMul.comp ((constant Nat.bits Nat.bits 27).pair (identity Nat.bits))).congrFun (by intro x; rfl)

theorem iterate_mul27 (i a : ℕ) : (fun x => 27 * x)^[i] a = 27 ^ i * a := by
  induction i generalizing a with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih]; ring

theorem bits_length_mul27 (i a : ℕ) : (Nat.bits (27 ^ i * a)).length ≤ 5 * i + (Nat.bits a).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len, Nat.size_le]
  have h1 : a < 2 ^ a.size := Nat.lt_size_self a
  have h2 : 27 ^ i ≤ 32 ^ i := Nat.pow_le_pow_left (by norm_num) i
  have h3 : (32 : ℕ) ^ i = 2 ^ (5 * i) := by rw [pow_mul]; norm_num
  rw [pow_add, ← h3]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · calc 27 ^ i * a ≤ 32 ^ i * a := Nat.mul_le_mul_right a h2
      _ < 32 ^ i * 2 ^ a.size := Nat.mul_lt_mul_of_pos_left h1 (by positivity)

/-- `27^n · a` from `n` in unary and `a` in binary. -/
noncomputable def pow27P : Procedure (prodCode unaryCode Nat.bits) Nat.bits (fun x => 27 ^ x.1 * x.2) :=
  (mul27.iterate (Polynomial.C 5 * Polynomial.X) (by
      intro n a i hi
      rw [iterate_mul27]
      have := bits_length_mul27 i a
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      nlinarith)).congrFun (by intro x; exact iterate_mul27 x.1 x.2)

open OAI.Optimization.LinearProgramming.OracleSpec in
/-- the public input for `n` nodes: `priceInput (rR n) (dummy n)`. -/
noncomputable def inputOfN : Procedure unaryCode (id : List Bool → List Bool)
    (fun n => priceInput (N := 2 * n + 1) (SSG28Reply.rR n) (SSG28Search.dummy n)) := by
  let nb := unaryToBits
  let bigN := successor.comp (binaryMul.comp ((constant unaryCode Nat.bits 2).pair nb))
  let bigR := pow27P.comp ((identity unaryCode).pair (constant unaryCode Nat.bits 128))
  let zero := constant unaryCode (id : List Bool → List Bool) (encodeNat 0)
  let tailW := append.comp ((encP.comp bigR).pair zero)
  exact (append.comp ((encP.comp bigN).pair tailW)).congrFun (by
    intro n
    simp only [Function.comp_apply, id_eq, priceInput, SSG28Reply.rR, SSG28Reply.rK, SSG28Search.dummy,
      List.append_assoc]
    congr 3 <;> ring)


/-! ### The validity check `ValidL w.reverse` -/

/-- equality of binary naturals. -/
noncomputable def eqP : Procedure (prodCode Nat.bits Nat.bits) boolCode (fun x => decide (x.1 = x.2)) :=
  (boolAnd.comp (binaryLe.pair (binaryLe.comp (swap Nat.bits Nat.bits)))).congrFun (by
    intro x
    simp only [Function.comp_apply, swap]
    by_cases h : x.1 = x.2
    · simp [h]
    · rcases Nat.lt_or_gt_of_ne h with h' | h' <;> simp [h, h'.le, not_le.mpr h'])

/-- the parameters `(l, (n, n))`: the layout, and `n` in binary and in unary. -/
abbrev qc : List Bool × (ℕ × ℕ) → List Bool := prodCode (listCode boolCode) (prodCode Nat.bits unaryCode)

/-- field `k` of the node pair `(i, j)` of the layout `l` with `n` nodes. -/
def bitF (l : List Bool) (n i j k : ℕ) : Bool := l.getD ((i * n + j) * 10 + k) false

theorem headD_drop (l : List Bool) (p : ℕ) : (l.drop p).headD false = l.getD p false := by
  induction l generalizing p with
  | nil => simp
  | cons b l ih => cases p with
    | zero => simp
    | succ p => simp [ih]

/-- the bit at `(i, j, k)` for parameters `q`. -/
noncomputable def bitP : Procedure (prodCode Nat.bits (prodCode Nat.bits (prodCode Nat.bits qc))) boolCode
    (fun x => bitF x.2.2.2.1 x.2.2.2.2.1 x.1 x.2.1 x.2.2.1) := by
  let e := prodCode Nat.bits (prodCode Nat.bits (prodCode Nat.bits qc))
  let i := first Nat.bits (prodCode Nat.bits (prodCode Nat.bits qc))
  let jkq := second Nat.bits (prodCode Nat.bits (prodCode Nat.bits qc))
  let j := (first Nat.bits (prodCode Nat.bits qc)).comp jkq
  let kq := (second Nat.bits (prodCode Nat.bits qc)).comp jkq
  let k := (first Nat.bits qc).comp kq
  let q := (second Nat.bits qc).comp kq
  let L := (first (listCode boolCode) (prodCode Nat.bits unaryCode)).comp q
  let nB := (first Nat.bits unaryCode).comp ((second (listCode boolCode) (prodCode Nat.bits unaryCode)).comp q)
  let pos := binaryAdd.comp ((binaryMul.comp ((binaryAdd.comp ((binaryMul.comp (i.pair nB)).pair j)).pair
    (constant e Nat.bits 10))).pair k)
  exact ((listGet boolCode false).comp (pos.pair L)).congrFun (by intro x; simp [bitF, headD_drop])

/-- `bitP` with `(i, j, k)` produced from an arbitrary input. -/
noncomputable def bitWith {α : Type} {ea : α → List Bool} {fi fj fk : α → ℕ} {fq : α → List Bool × (ℕ × ℕ)}
    (pi : Procedure ea Nat.bits fi) (pj : Procedure ea Nat.bits fj) (pk : Procedure ea Nat.bits fk)
    (pq : Procedure ea qc fq) :
    Procedure ea boolCode (fun a => bitF (fq a).1 (fq a).2.1 (fi a) (fj a) (fk a)) :=
  (bitP.comp (pi.pair (pj.pair (pk.pair pq)))).congrFun (by intro a; rfl)

/-- one-hot test of a bit list, as `count true = 1`. -/
noncomputable def oneHotP : Procedure (listCode boolCode) boolCode (fun xs => decide (xs.count true = 1)) :=
  (eqP.comp ((unaryToBits.comp countTrueP).pair (constant (listCode boolCode) Nat.bits 1))).congrFun
    (by intro xs; rfl)

-- inputs `(i, q)` (i unary) and `(j, (i, q))` (j unary)
abbrev iqc : ℕ × (List Bool × (ℕ × ℕ)) → List Bool := prodCode unaryCode qc
abbrev jiqc : ℕ × (ℕ × (List Bool × (ℕ × ℕ))) → List Bool := prodCode unaryCode iqc

noncomputable def qOfIQ : Procedure iqc qc (fun x => x.2) := second unaryCode qc
noncomputable def nUOfIQ : Procedure iqc unaryCode (fun x => x.2.2.2) :=
  (second Nat.bits unaryCode).comp ((second (listCode boolCode) (prodCode Nat.bits unaryCode)).comp qOfIQ)
noncomputable def iOfIQ : Procedure iqc Nat.bits (fun x => x.1) := unaryToBits.comp (first unaryCode qc)

/-- the child row `k` (6 = childJ, 7 = childK) of node `i` is one-hot. -/
noncomputable def rowOKP (k : ℕ) : Procedure iqc boolCode
    (fun x => decide (((List.range x.2.2.2).map (fun j => bitF x.2.1 x.2.2.1 x.1 j k)).count true = 1)) := by
  let step : Procedure jiqc boolCode (fun x => bitF x.2.2.1 x.2.2.2.1 x.2.1 x.1 k) :=
    bitWith (iOfIQ.comp (second unaryCode iqc)) (unaryToBits.comp (first unaryCode iqc))
      (constant jiqc Nat.bits k) (qOfIQ.comp (second unaryCode iqc))
  let tab := (tabulate (f := fun (y : ℕ × (List Bool × (ℕ × ℕ))) j => bitF y.2.1 y.2.2.1 y.1 j k)
    false step).comp (nUOfIQ.pair (identity iqc))
  exact (oneHotP.comp tab).congrFun (by intro x; rfl)

/-- the node-type bits of node `i` are one-hot. -/
noncomputable def typeOKP : Procedure iqc boolCode
    (fun x => decide (((List.range 5).map (fun k => bitF x.2.1 x.2.2.1 x.1 0 k)).count true = 1)) := by
  let step : Procedure (prodCode unaryCode iqc) boolCode (fun x => bitF x.2.2.1 x.2.2.2.1 x.2.1 0 x.1) :=
    bitWith (iOfIQ.comp (second unaryCode iqc)) (constant (prodCode unaryCode iqc) Nat.bits 0)
      (unaryToBits.comp (first unaryCode iqc)) (qOfIQ.comp (second unaryCode iqc))
  let tab := (tabulate (f := fun (y : ℕ × (List Bool × (ℕ × ℕ))) k => bitF y.2.1 y.2.2.1 y.1 0 k)
    false step).comp ((constant iqc unaryCode 5).pair (identity iqc))
  exact (oneHotP.comp tab).congrFun (by intro x; rfl)

/-- the per-node conditions (`n` = row length used for addressing, `m` = number of columns read). -/
def nodeOK (l : List Bool) (n m i : ℕ) : Bool :=
  decide (((List.range 5).map (fun k => bitF l n i 0 k)).count true = 1) &&
  (decide (((List.range m).map (fun j => bitF l n i j 6)).count true = 1) &&
   decide (((List.range m).map (fun j => bitF l n i j 7)).count true = 1))

noncomputable def nodeOKP : Procedure iqc boolCode (fun x => nodeOK x.2.1 x.2.2.1 x.2.2.2 x.1) :=
  (boolAnd.comp (typeOKP.pair (boolAnd.comp ((rowOKP 6).pair (rowOKP 7))))).congrFun (by intro x; rfl)

noncomputable def nUOfQ : Procedure qc unaryCode (fun q => q.2.2) :=
  (second Nat.bits unaryCode).comp (second (listCode boolCode) (prodCode Nat.bits unaryCode))
noncomputable def nBOfQ : Procedure qc Nat.bits (fun q => q.2.1) :=
  (first Nat.bits unaryCode).comp (second (listCode boolCode) (prodCode Nat.bits unaryCode))

/-- all nodes pass `nodeOK`: the number of passing nodes equals `n`. -/
noncomputable def allNodesP : Procedure qc boolCode
    (fun q => decide (((List.range q.2.2).map (nodeOK q.1 q.2.1 q.2.2)).count true = q.2.1)) := by
  let tab := (tabulate (f := fun (q : List Bool × (ℕ × ℕ)) i => nodeOK q.1 q.2.1 q.2.2 i) false nodeOKP).comp
    (nUOfQ.pair (identity qc))
  exact (eqP.comp ((unaryToBits.comp (countTrueP.comp tab)).pair nBOfQ)).congrFun (by intro q; rfl)

/-- the start column is one-hot. -/
noncomputable def startOKP : Procedure qc boolCode
    (fun q => decide (((List.range q.2.2).map (fun i => bitF q.1 q.2.1 i 0 5)).count true = 1)) := by
  let step : Procedure iqc boolCode (fun x => bitF x.2.1 x.2.2.1 x.1 0 5) :=
    bitWith iOfIQ (constant iqc Nat.bits 0) (constant iqc Nat.bits 5) qOfIQ
  let tab := (tabulate (f := fun (q : List Bool × (ℕ × ℕ)) i => bitF q.1 q.2.1 i 0 5) false step).comp
    (nUOfQ.pair (identity qc))
  exact (oneHotP.comp tab).congrFun (by intro q; rfl)


/-- the parameters `(l, (n, n))` of the input word. -/
noncomputable def qP : Procedure (id : List Bool → List Bool) qc
    (fun w => (w.reverse, (SSG28Decode.nOf w.reverse, SSG28Decode.nOf w.reverse))) :=
  (toListP.pair (nP.pair nUP)).congrFun (by intro w; rfl)

/-- the validity bit, as computed. -/
def validF (w : List Bool) : Bool :=
  decide (1 ≤ SSG28Decode.nOf w.reverse) &&
  (decide (w.length = SSG28Decode.nOf w.reverse * SSG28Decode.nOf w.reverse * 10) &&
   (decide (((List.range (SSG28Decode.nOf w.reverse)).map (nodeOK w.reverse (SSG28Decode.nOf w.reverse)
       (SSG28Decode.nOf w.reverse))).count true = SSG28Decode.nOf w.reverse) &&
    decide (((List.range (SSG28Decode.nOf w.reverse)).map
       (fun i => bitF w.reverse (SSG28Decode.nOf w.reverse) i 0 5)).count true = 1)))

noncomputable def validFP : Procedure (id : List Bool → List Bool) boolCode validF := by
  let c1 := binaryLe.comp ((constant (id : List Bool → List Bool) Nat.bits 1).pair nP)
  let len := unaryToBits.comp length
  let nn := binaryMul.comp ((binaryMul.comp (nP.pair nP)).pair (constant (id : List Bool → List Bool) Nat.bits 10))
  let c2 := eqP.comp (len.pair nn)
  let c3 := allNodesP.comp qP
  let c4 := startOKP.comp qP
  exact (boolAnd.comp (c1.pair (boolAnd.comp (c2.pair (boolAnd.comp (c3.pair c4)))))).congrFun
    (by intro w; rfl)

theorem count_map_eq_length_iff (m : ℕ) (f : ℕ → Bool) :
    ((List.range m).map f).count true = m ↔ ∀ i < m, f i = true := by
  have h := List.count_eq_length (a := true) (l := (List.range m).map f)
  simp only [List.length_map, List.length_range] at h
  rw [h]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp]
  constructor
  · intro H i hi; exact (H _ i hi rfl).symm
  · intro H b i hi hb; rw [← hb, H i hi]

theorem validF_eq (w : List Bool) : validF w = decide (SSG28Decode.ValidL w.reverse) := by
  unfold validF SSG28Decode.ValidL
  simp only [Bool.decide_and, List.length_reverse]
  congr 2
  · congr 1
    rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, count_map_eq_length_iff]
    apply forall_congr'; intro i; apply imp_congr_right; intro _
    simp only [nodeOK, Bool.and_eq_true, decide_eq_true_iff, SSG28Decode.OneHot, SSG28Decode.typeBits,
      SSG28Decode.childRow, SSG28Decode.bit, bitF]
    try simp
  all_goals try rfl

/-- **(A) the validity procedure.** -/
noncomputable def validP : Procedure (id : List Bool → List Bool) boolCode
    (fun w => decide (SSG28Decode.ValidL w.reverse)) :=
  validFP.congrFun validF_eq

open OAI.Optimization.LinearProgramming.OracleSpec in
/-- **the driver procedure.** -/
noncomputable def driverP : Procedure (id : List Bool → List Bool) (id : List Bool → List Bool)
    SSG28Reply.driverW :=
  (conditional validP (inputOfN.comp nUP)
    (constant (id : List Bool → List Bool) (id : List Bool → List Bool) (priceInput (N := 1) 1 0))).congrFun (by
    intro w
    unfold SSG28Reply.driverW SSG28Decode.decode
    by_cases h : SSG28Decode.ValidL w.reverse
    · simp [h]
    · simp [h])

end SSG28MachineProcD2
