module

public import SSGinP.Machine.MachineProc
public import SSGinP.Machine.MachineProcD2Driver

@[expose] public section

/-!
# SSGinP.Machine.MachineReply: the top-level reply procedure

`replyP B θ thP : Procedure (prodCode id eqCode) boolCode (replyL θ)`, generic in the threshold `θ` (given by a
procedure `thP` computing `θ n` from `n` in unary), built from:
* the query parser `parseQueryP`,
* `validP` (`ValidL`), `nUP` (number of nodes),
* the node-table blocks, abstracted in the structure `Blocks`
  (table, `okGame`, weights, start node, one evaluation of `F` at a node), with their specifications.
-/

set_option linter.unusedSimpArgs false

namespace SSG28MachineReply

open SSG SSG28Reply SSG28Search SSG28Machine SSG28MachineProc
open OAI.ExactQuantumFactoring.BitStackProgram OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec

abbrev W := List Bool

/-- the building blocks on the node table, with their specifications. -/
structure Blocks where
  T : Type
  tc : T → W
  tab : W → T
  tabP : Procedure (id : W → W) tc tab
  okT : T → Bool
  okP : Procedure tc boolCode okT
  wtT : T → List ℚ
  wtP : Procedure tc (listCode ratCode) wtT
  startT : T → ℕ
  startP : Procedure tc Nat.bits startT
  evalT : T × (List ℚ × ℕ) → ℚ
  evalP : Procedure (prodCode tc (prodCode (listCode ratCode) Nat.bits)) ratCode evalT
  ok_spec : ∀ x (h : SSG28Decode.ValidL x.reverse), okT (tab x) = okGame (SSG28Decode.gameOf x.reverse h)
  wt_spec : ∀ x (h : SSG28Decode.ValidL x.reverse) (j : Fin (SSG28Decode.nOf x.reverse)),
    (wtT (tab x)).getD j.val 0 = wt (SSG28Decode.gameOf x.reverse h) j
  start_spec : ∀ x (h : SSG28Decode.ValidL x.reverse),
    startT (tab x) = (SSG28Decode.gameOf x.reverse h).startNode.val
  eval_spec : ∀ x (h : SSG28Decode.ValidL x.reverse) (v : List ℚ), v.length = SSG28Decode.nOf x.reverse →
    ∀ j : Fin (SSG28Decode.nOf x.reverse),
      evalT (tab x, (v, j.val)) = F (SSG28Decode.gameOf x.reverse h) (fun k => v.getD k.val 0) j

/-! ## the reply at list level -/

/-- environment for the `lo`/`hi` vectors: `δ`, weights, prices, `n`. -/
abbrev Env := ℚ × (List ℚ × (List ℚ × ℕ))

def loElem (e : Env) (j : ℕ) : ℚ := e.1 * e.2.1.getD j 0 * (e.2.2.1.getD (1 + j) 0 - e.2.2.1.getD 0 0)
def hiElem (e : Env) (j : ℕ) : ℚ := -(e.1 * e.2.1.getD j 0 * (e.2.2.1.getD (1 + e.2.2.2 + j) 0 - e.2.2.1.getD 0 0))

/-- the reply bit from the table `t`, `n`, `θ n`, index `i`, prices `l`. -/
def bitF (B : Blocks) (t : B.T) (n : ℕ) (th : ℚ) (i : ℕ) (l : List ℚ) : Bool :=
  let e : Env := (rDelta n, (B.wtT t, (l, n)))
  let lo := (List.range n).map (loElem e)
  let hi := (List.range n).map (hiElem e)
  if i = 0 then decide (th < lo.getD (B.startT t) 0)
  else if i ≤ n then decide (lo.getD (i - 1) 0 < B.evalT (t, (lo, i - 1)))
  else decide (B.evalT (t, (hi, i - 1 - n)) < hi.getD (i - 1 - n) 0)

def repF (B : Blocks) (θ : ℕ → ℚ) (xa : W × (ℕ × List ℚ)) : Bool :=
  if SSG28MachineProcD2.validF xa.1 then
    let t := B.tab xa.1
    let n := SSG28Decode.nOf xa.1.reverse
    (decide (xa.2.1 < 2 * n + 1) && decide (xa.2.2.length = 2 * n + 1)) && B.okT t &&
      bitF B t n (θ n) xa.2.1 xa.2.2
  else false

theorem getD_map_range (f : ℕ → ℚ) (n j : ℕ) (hj : j < n) : ((List.range n).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, hj]

theorem repF_eq (B : Blocks) (θ : ℕ → ℚ) (xa : W × (ℕ × List ℚ)) : repF B θ xa = replyL θ xa := by
  rcases xa with ⟨x, i, l⟩
  unfold repF replyL
  rw [SSG28MachineProcD2.validF_eq]
  by_cases hv : SSG28Decode.ValidL x.reverse
  swap
  · simp only [hv, decide_false, Bool.false_eq_true, if_false]
    simp [SSG28Decode.decode, hv]
  simp only [hv, decide_true, if_true]
  have hd : SSG28Decode.decode x = some ⟨SSG28Decode.nOf x.reverse, SSG28Decode.gameOf x.reverse hv⟩ := by
    simp [SSG28Decode.decode, hv]
  rw [hd]
  simp only
  set n := SSG28Decode.nOf x.reverse with hn
  set G := SSG28Decode.gameOf x.reverse hv
  by_cases hdim : i < 2 * n + 1 ∧ l.length = 2 * n + 1
  swap
  · rw [dif_neg hdim]
    have e : (decide (i < 2 * SSG28Decode.nOf x.reverse + 1) &&
        decide (l.length = 2 * SSG28Decode.nOf x.reverse + 1)) = false := by
      rw [Bool.and_eq_false_iff]
      by_cases h1 : i < 2 * n + 1
      · right; exact decide_eq_false (fun h2 => hdim ⟨h1, h2⟩)
      · left; exact decide_eq_false h1
    rw [e]; simp
  rw [dif_pos hdim]
  have e : (decide (i < 2 * SSG28Decode.nOf x.reverse + 1) &&
      decide (l.length = 2 * SSG28Decode.nOf x.reverse + 1)) = true := by
    rw [Bool.and_eq_true]; exact ⟨decide_eq_true hdim.1, decide_eq_true hdim.2⟩
  rw [e, Bool.true_and]
  rw [B.ok_spec x hv]
  congr 1
  -- the reply bit
  set q : Fin (2 * n + 1) → ℚ := fun g => l.get ⟨g.val, by omega⟩ with hq
  have hql : ∀ k (hk : k < 2 * n + 1), l.getD k 0 = q ⟨k, hk⟩ := by
    intro k hk; simp [hq, List.getD_eq_getElem?_getD, hdim.2 ▸ hk]
  have hlo : ∀ j : Fin n, loElem (rDelta n, (B.wtT (B.tab x), (l, n))) j.val = SSG28Reply.lo G (rDelta n) q j := by
    intro j
    simp only [loElem, SSG28Reply.lo, B.wt_spec x hv j]
    rw [hql (1 + j.val) (by omega), hql 0 (by omega)]
    rfl
  have hhi : ∀ j : Fin n, hiElem (rDelta n, (B.wtT (B.tab x), (l, n))) j.val = SSG28Reply.hi G (rDelta n) q j := by
    intro j
    simp only [hiElem, SSG28Reply.hi, B.wt_spec x hv j]
    rw [hql (1 + n + j.val) (by omega), hql 0 (by omega)]
    rfl
  have hloF : (fun k : Fin n => ((List.range n).map (loElem (rDelta n, (B.wtT (B.tab x), (l, n))))).getD k.val 0) =
      SSG28Reply.lo G (rDelta n) q := by
    funext k; rw [getD_map_range _ _ _ k.2, hlo]
  have hhiF : (fun k : Fin n => ((List.range n).map (hiElem (rDelta n, (B.wtT (B.tab x), (l, n))))).getD k.val 0) =
      SSG28Reply.hi G (rDelta n) q := by
    funext k; rw [getD_map_range _ _ _ k.2, hhi]
  unfold bitF replyGood
  simp only
  by_cases hi0 : i = 0
  · rw [if_pos hi0, dif_pos hi0, B.start_spec x hv, getD_map_range _ _ _ G.startNode.2, hlo]
  · rw [if_neg hi0, dif_neg hi0]
    by_cases hin : i ≤ n
    · rw [if_pos hin, dif_pos hin]
      have hj : i - 1 < n := by omega
      rw [B.eval_spec x hv _ (by simp) ⟨i - 1, hj⟩, hloF, getD_map_range _ _ _ hj, hlo ⟨i - 1, hj⟩]
    · rw [if_neg hin, dif_neg hin]
      have hj : i - 1 - n < n := by omega
      rw [B.eval_spec x hv _ (by simp) ⟨i - 1 - n, hj⟩, hhiF, getD_map_range _ _ _ hj, hhi ⟨i - 1 - n, hj⟩]

/-! ## rational helpers -/

theorem getD_drop (l : List ℚ) (k : ℕ) : (l.drop k).headD 0 = l.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, ← List.head?_drop, List.headD_eq_head?_getD]

/-- `(k, l) ↦ l.getD k 0`. -/
noncomputable def getQ : Procedure (prodCode Nat.bits (listCode ratCode)) ratCode (fun x => x.2.getD x.1 0) :=
  (listGet ratCode 0).congrFun (fun x => getD_drop x.2 x.1)

/-- strict comparison of rationals. -/
noncomputable def ltQ : Procedure (prodCode ratCode ratCode) boolCode (fun x => decide (x.1 < x.2)) :=
  (intSign.comp (ratNum.comp ratSub)).congrFun (by
    intro x
    simp only [Function.comp]
    exact Bool.decide_congr (Rat.num_neg.trans sub_neg))

noncomputable def mul9 : Procedure Nat.bits Nat.bits (fun x => 9 * x) :=
  (binaryMul.comp ((constant Nat.bits Nat.bits 9).pair (identity Nat.bits))).congrFun (by intro x; rfl)

theorem iterate_mul9 (i a : ℕ) : (fun x => 9 * x)^[i] a = 9 ^ i * a := by
  induction i generalizing a with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih]; ring

theorem bits_length_mul9 (i a : ℕ) : (Nat.bits (9 ^ i * a)).length ≤ 4 * i + (Nat.bits a).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len, Nat.size_le]
  have h1 : a < 2 ^ a.size := Nat.lt_size_self a
  have h2 : 9 ^ i ≤ 16 ^ i := Nat.pow_le_pow_left (by norm_num) i
  have h3 : (16 : ℕ) ^ i = 2 ^ (4 * i) := by rw [pow_mul]; norm_num
  rw [pow_add, ← h3]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · calc 9 ^ i * a ≤ 16 ^ i * a := Nat.mul_le_mul_right a h2
      _ < 16 ^ i * 2 ^ a.size := Nat.mul_lt_mul_of_pos_left h1 (by positivity)

noncomputable def pow9P : Procedure (prodCode unaryCode Nat.bits) Nat.bits (fun x => 9 ^ x.1 * x.2) :=
  (mul9.iterate (Polynomial.C 4 * Polynomial.X) (by
      intro n a i hi
      rw [iterate_mul9]
      have := bits_length_mul9 i a
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      nlinarith)).congrFun (by intro x; exact iterate_mul9 x.1 x.2)

/-- `n ↦ 1/(c · 9^n)`. -/
noncomputable def invPow9P (c : ℕ) : Procedure unaryCode ratCode (fun n => 1 / ((c : ℚ) * 9 ^ n)) :=
  (ratInv.comp (natToRat.comp (pow9P.comp ((identity unaryCode).pair (constant unaryCode Nat.bits c))))).congrFun
    (by intro n; simp only [Function.comp, id]; push_cast; ring)

noncomputable def thetaGeP : Procedure unaryCode ratCode thetaGe :=
  (ratSub.comp ((constant unaryCode ratCode (1 / 2)).pair (invPow9P 4))).congrFun
    (by intro n; simp only [Function.comp, thetaGe, Delta]; norm_num)

noncomputable def thetaGtP : Procedure unaryCode ratCode thetaGt :=
  (ratAdd.comp ((constant unaryCode ratCode (1 / 2)).pair (invPow9P 4))).congrFun
    (by intro n; simp only [Function.comp, thetaGt, Delta]; norm_num)

noncomputable def deltaP : Procedure unaryCode ratCode rDelta :=
  (ratInv.comp (natToRat.comp (SSG28MachineProcD2.pow27P.comp
    ((identity unaryCode).pair (constant unaryCode Nat.bits 64))))).congrFun
    (by intro n; simp only [Function.comp, id, rDelta]; push_cast; ring)

/-! ## the lo / hi vectors -/

abbrev envC : Env → W := prodCode ratCode (prodCode (listCode ratCode) (prodCode (listCode ratCode) Nat.bits))

section Vec
abbrev jeC : ℕ × Env → W := prodCode unaryCode envC

noncomputable def eD : Procedure jeC ratCode (fun x => x.2.1) := (first ratCode _).comp (second unaryCode envC)
noncomputable def eW : Procedure jeC (listCode ratCode) (fun x => x.2.2.1) :=
  (first (listCode ratCode) _).comp ((second ratCode _).comp (second unaryCode envC))
noncomputable def eL : Procedure jeC (listCode ratCode) (fun x => x.2.2.2.1) :=
  (first (listCode ratCode) Nat.bits).comp ((second (listCode ratCode) _).comp ((second ratCode _).comp (second unaryCode envC)))
noncomputable def eN : Procedure jeC Nat.bits (fun x => x.2.2.2.2) :=
  (second (listCode ratCode) Nat.bits).comp ((second (listCode ratCode) _).comp ((second ratCode _).comp (second unaryCode envC)))
noncomputable def eJ : Procedure jeC Nat.bits (fun x => x.1) := unaryToBits.comp (first unaryCode envC)

noncomputable def loElemP : Procedure jeC ratCode (fun x => loElem x.2 x.1) :=
  (ratMul.comp ((ratMul.comp (eD.pair (getQ.comp (eJ.pair eW)))).pair
    (ratSub.comp ((getQ.comp ((successor.comp eJ).pair eL)).pair (getQ.comp ((constant jeC Nat.bits 0).pair eL))))
    )).congrFun (by intro x; simp only [Function.comp, loElem, Nat.succ_eq_add_one, add_comm x.1 1])

noncomputable def hiElemP : Procedure jeC ratCode (fun x => hiElem x.2 x.1) :=
  (ratNeg.comp (ratMul.comp ((ratMul.comp (eD.pair (getQ.comp (eJ.pair eW)))).pair
    (ratSub.comp ((getQ.comp ((successor.comp (binaryAdd.comp (eN.pair eJ))).pair eL)).pair
      (getQ.comp ((constant jeC Nat.bits 0).pair eL))))))).congrFun (by
        intro x; simp only [Function.comp, hiElem, Nat.succ_eq_add_one]; congr 4; ring)

noncomputable def loVecP : Procedure jeC (listCode ratCode) (fun x => (List.range x.1).map (loElem x.2)) :=
  tabulate 0 loElemP
noncomputable def hiVecP : Procedure jeC (listCode ratCode) (fun x => (List.range x.1).map (hiElem x.2)) :=
  tabulate 0 hiElemP
end Vec

/-! ## the reply on the context `(table, n, i, prices)` -/

section Main
variable (B : Blocks)

abbrev Ctx := B.T × (ℕ × (ℕ × List ℚ))
abbrev ctxC : Ctx B → W := prodCode B.tc (prodCode unaryCode (prodCode Nat.bits (listCode ratCode)))

noncomputable def cT : Procedure (ctxC B) B.tc (fun c => c.1) := first B.tc _
noncomputable def cN : Procedure (ctxC B) unaryCode (fun c => c.2.1) := (first unaryCode _).comp (second B.tc _)
noncomputable def cNB : Procedure (ctxC B) Nat.bits (fun c => c.2.1) := unaryToBits.comp (cN B)
noncomputable def cI : Procedure (ctxC B) Nat.bits (fun c => c.2.2.1) :=
  (first Nat.bits (listCode ratCode)).comp ((second unaryCode _).comp (second B.tc _))
noncomputable def cL : Procedure (ctxC B) (listCode ratCode) (fun c => c.2.2.2) :=
  (second Nat.bits (listCode ratCode)).comp ((second unaryCode _).comp (second B.tc _))

noncomputable def envP : Procedure (ctxC B) envC (fun c => (rDelta c.2.1, (B.wtT c.1, (c.2.2.2, c.2.1)))) :=
  (deltaP.comp (cN B)).pair ((B.wtP.comp (cT B)).pair ((cL B).pair (cNB B)))

noncomputable def loP : Procedure (ctxC B) (listCode ratCode)
    (fun c => (List.range c.2.1).map (loElem (rDelta c.2.1, (B.wtT c.1, (c.2.2.2, c.2.1))))) :=
  loVecP.comp ((cN B).pair (envP B))
noncomputable def hiP : Procedure (ctxC B) (listCode ratCode)
    (fun c => (List.range c.2.1).map (hiElem (rDelta c.2.1, (B.wtT c.1, (c.2.2.2, c.2.1))))) :=
  hiVecP.comp ((cN B).pair (envP B))

noncomputable def bitP {θ : ℕ → ℚ} (thP : Procedure unaryCode ratCode θ) :
    Procedure (ctxC B) boolCode (fun c => bitF B c.1 c.2.1 (θ c.2.1) c.2.2.1 c.2.2.2) := by
  let im1 := binarySub.comp ((cI B).pair (constant (ctxC B) Nat.bits 1))
  let im1n := binarySub.comp (im1.pair (cNB B))
  let b0 := ltQ.comp ((thP.comp (cN B)).pair (getQ.comp ((B.startP.comp (cT B)).pair (loP B))))
  let bUp := ltQ.comp ((getQ.comp (im1.pair (loP B))).pair (B.evalP.comp ((cT B).pair ((loP B).pair im1))))
  let bDown := ltQ.comp ((B.evalP.comp ((cT B).pair ((hiP B).pair im1n))).pair (getQ.comp (im1n.pair (hiP B))))
  exact (conditional (binaryZero.comp (cI B)) b0
    (conditional (binaryLe.comp ((cI B).pair (cNB B))) bUp bDown)).congrFun (by
      intro c
      simp only [bitF, Function.comp]
      by_cases h0 : c.2.2.1 = 0
      · simp [h0]
      · by_cases h1 : c.2.2.1 ≤ c.2.1
        · simp [h0, h1]
        · simp [h0, h1])

def mainF {θ : ℕ → ℚ} (c : Ctx B) : Bool :=
  (decide (c.2.2.1 < 2 * c.2.1 + 1) && decide (c.2.2.2.length = 2 * c.2.1 + 1)) && B.okT c.1 &&
    bitF B c.1 c.2.1 (θ c.2.1) c.2.2.1 c.2.2.2

noncomputable def mainP {θ : ℕ → ℚ} (thP : Procedure unaryCode ratCode θ) :
    Procedure (ctxC B) boolCode (mainF B (θ := θ)) := by
  let twoN1 := successor.comp (binaryMul.comp ((constant (ctxC B) Nat.bits 2).pair (cNB B)))
  let d1 := binaryLt.comp ((cI B).pair twoN1)
  let d2 := SSG28MachineProcD2.eqP.comp (((listLength ratCode 0).comp (cL B)).pair twoN1)
  let ok := B.okP.comp (cT B)
  exact (boolAnd.comp ((boolAnd.comp ((boolAnd.comp (d1.pair d2)).pair ok)).pair (bitP B thP))).congrFun (by
    intro c; simp only [mainF, Function.comp, Nat.succ_eq_add_one])

end Main

/-! ## the reply procedure -/

abbrev inC : W × (ℕ × List ℚ) → W := prodCode (id : W → W) SSG28Machine.eqCode

/-- **The reply procedure, generic in the threshold.** -/
noncomputable def replyP (B : Blocks) {θ : ℕ → ℚ} (thP : Procedure unaryCode ratCode θ) :
    Procedure inC boolCode (replyL θ) := by
  let xP := first (id : W → W) SSG28Machine.eqCode
  let ctx : Procedure inC (ctxC B) (fun xa => (B.tab xa.1, (SSG28Decode.nOf xa.1.reverse, xa.2))) :=
    (B.tabP.comp xP).pair ((SSG28MachineProcD2.nUP.comp xP).pair
      ((parseQueryP.comp (second (id : W → W) SSG28Machine.eqCode)).congrFun (fun _ => rfl)))
  exact (conditional (SSG28MachineProcD2.validFP.comp xP) ((mainP B thP).comp ctx)
    (constant inC boolCode false)).congrFun (by
      intro xa
      rw [← repF_eq B θ xa]
      simp only [repF, mainF, Function.comp])

noncomputable def replyGeP (B : Blocks) : Procedure inC boolCode (replyL thetaGe) := replyP B thetaGeP
noncomputable def replyGtP (B : Blocks) : Procedure inC boolCode (replyL thetaGt) := replyP B thetaGtP

end SSG28MachineReply
