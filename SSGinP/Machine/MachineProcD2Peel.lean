module

public import SSGinP.Machine.MachineProcD2Eval
public import SSGinP.Theory.Theory

@[expose] public section

/-!
# SSGinP.Machine.MachineProcD2Peel: peeling (the stopping test `peelAll`) and the ranks
`prank` read from the layout, by `n` rounds of a fixed round procedure.
State `(q, (P, C))`: `P` = which nodes are peeled, `C` = per-node count of rounds in which it was not yet peeled.
-/

namespace SSG28MachineProcD2

open OAI.ExactQuantumFactoring.BitStackProgram OAI.ExactQuantumFactoring.BitStackProgram.Procedure

/-- one peeling decision at node `i` (cf. `SSG.peelStep`). -/
def peelF (q : List Bool × (ℕ × ℕ)) (P : List Bool) (i : ℕ) : Bool :=
  P.getD i false ||
    (if tyF q i ≤ 1 then P.getD (chF q i 6) false && P.getD (chF q i 7) false
     else if tyF q i = 2 then P.getD (chF q i 6) false || P.getD (chF q i 7) false
     else true)

abbrev pc : ℕ × ((List Bool × (ℕ × ℕ)) × List Bool) → List Bool :=
  prodCode Nat.bits (prodCode qc (listCode boolCode))

noncomputable def peelBitP : Procedure pc boolCode (fun x => peelF x.2.1 x.2.2 x.1) := by
  let i := first Nat.bits (prodCode qc (listCode boolCode))
  let s := second Nat.bits (prodCode qc (listCode boolCode))
  let q := (first qc (listCode boolCode)).comp s
  let P := (second qc (listCode boolCode)).comp s
  let t := unaryToBits.comp (tyP.comp (i.pair q))
  let cj := unaryToBits.comp ((chP 6).comp (i.pair q))
  let ck := unaryToBits.comp ((chP 7).comp (i.pair q))
  let a := (listGet boolCode false).comp (cj.pair P)
  let b := (listGet boolCode false).comp (ck.pair P)
  let pi := (listGet boolCode false).comp (i.pair P)
  let le1 := binaryLe.comp (t.pair (constant pc Nat.bits 1))
  let is2 := eqP.comp (t.pair (constant pc Nat.bits 2))
  let inner := conditional le1 (boolAnd.comp (a.pair b))
    (conditional is2 (boolOr.comp (a.pair b)) (constant pc boolCode true))
  exact (boolOr.comp (pi.pair inner)).congrFun (by
    intro x
    simp only [peelF, Function.comp_apply, headD_drop]
    by_cases h1 : tyF x.2.1 x.1 ≤ 1
    · simp [h1]
    · by_cases h2 : tyF x.2.1 x.1 = 2 <;> simp [h1, h2])

/-- the state code. -/
abbrev sc : (List Bool × (ℕ × ℕ)) × (List Bool × List ℕ) → List Bool :=
  prodCode qc (prodCode (listCode boolCode) (listCode unaryCode))

/-- one round. -/
def roundF (s : (List Bool × (ℕ × ℕ)) × (List Bool × List ℕ)) : (List Bool × (ℕ × ℕ)) × (List Bool × List ℕ) :=
  let P' := (List.range s.1.2.2).map (peelF s.1 s.2.1)
  (s.1, (P', (List.range s.1.2.2).map (fun i => s.2.2.getD i 0 + (if P'.getD i false then 0 else 1))))

noncomputable def newPP : Procedure (prodCode qc (listCode boolCode)) (listCode boolCode)
    (fun s => (List.range s.1.2.2).map (peelF s.1 s.2)) := by
  let step : Procedure (prodCode unaryCode (prodCode qc (listCode boolCode))) boolCode
      (fun x => peelF x.2.1 x.2.2 x.1) :=
    (peelBitP.comp ((unaryToBits.comp (first unaryCode (prodCode qc (listCode boolCode)))).pair
      (second unaryCode (prodCode qc (listCode boolCode))))).congrFun (by intro x; rfl)
  exact ((tabulate (f := fun (s : (List Bool × (ℕ × ℕ)) × List Bool) i => peelF s.1 s.2 i) false step).comp
    ((nUOfQ.comp (first qc (listCode boolCode))).pair (identity (prodCode qc (listCode boolCode))))).congrFun
    (by intro s; rfl)

theorem headD_drop_n (l : List ℕ) (p : ℕ) : (l.drop p).headD 0 = l.getD p 0 := by
  induction l generalizing p with
  | nil => simp
  | cons b l ih => cases p with
    | zero => simp
    | succ p => simp [ih]

noncomputable def newCP : Procedure sc (listCode unaryCode)
    (fun s => (List.range s.1.2.2).map (fun i => s.2.2.getD i 0 + (if s.2.1.getD i false then 0 else 1))) := by
  let e := prodCode unaryCode sc
  let iB := unaryToBits.comp (first unaryCode sc)
  let s := second unaryCode sc
  let P := (first (listCode boolCode) (listCode unaryCode)).comp
    ((second qc (prodCode (listCode boolCode) (listCode unaryCode))).comp s)
  let C := (second (listCode boolCode) (listCode unaryCode)).comp
    ((second qc (prodCode (listCode boolCode) (listCode unaryCode))).comp s)
  let c := (listGet unaryCode 0).comp (iB.pair C)
  let pb := (listGet boolCode false).comp (iB.pair P)
  let step : Procedure e unaryCode (fun x => x.2.2.2.getD x.1 0 + (if x.2.2.1.getD x.1 false then 0 else 1)) :=
    (conditional pb c (unarySuccessor.comp c)).congrFun (by
      intro x
      simp only [Function.comp_apply, headD_drop, headD_drop_n, id]
      cases x.2.2.1.getD x.1 false <;> simp)
  exact ((tabulate (f := fun (s : (List Bool × (ℕ × ℕ)) × (List Bool × List ℕ)) i =>
      s.2.2.getD i 0 + (if s.2.1.getD i false then 0 else 1)) 0 step).comp
    ((nUOfQ.comp (first qc (prodCode (listCode boolCode) (listCode unaryCode)))).pair (identity sc))).congrFun
    (by intro s; rfl)

noncomputable def roundP : Procedure sc sc roundF := by
  let q := first qc (prodCode (listCode boolCode) (listCode unaryCode))
  let PC := second qc (prodCode (listCode boolCode) (listCode unaryCode))
  let P := (first (listCode boolCode) (listCode unaryCode)).comp PC
  let C := (second (listCode boolCode) (listCode unaryCode)).comp PC
  let P' := newPP.comp (q.pair P)
  let C' := newCP.comp (q.pair (P'.pair C))
  exact (q.pair (P'.pair C')).congrFun (by intro s; rfl)


/-! ### Iterating the round -/

theorem listCode_elem_le (xs : List ℕ) (c : ℕ) (h : c ∈ xs) : c ≤ (listCode unaryCode xs).length := by
  induction xs with
  | nil => simp at h
  | cons a as ih =>
    rw [listCode_length_cons]
    rcases List.mem_cons.mp h with rfl | h
    · simp [unaryCode]; omega
    · have := ih h; omega

theorem getD_le_of (xs : List ℕ) (B i : ℕ) (h : ∀ c ∈ xs, c ≤ B) : xs.getD i 0 ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : xs[i]? with
  | none => simp
  | some c => simpa using h c (List.mem_of_getElem? hx)

/-- invariant of the iterated round: the parameters stay, the lists have length `≤ max _ m`, the counts grow by `≤ 1`. -/
theorem round_inv (a : (List Bool × (ℕ × ℕ)) × (List Bool × List ℕ)) (B : ℕ)
    (hB : ∀ c ∈ a.2.2, c ≤ B) : ∀ i, (roundF^[i] a).1 = a.1 ∧
      (roundF^[i] a).2.1.length ≤ max a.2.1.length a.1.2.2 ∧
      (roundF^[i] a).2.2.length ≤ max a.2.2.length a.1.2.2 ∧
      ∀ c ∈ (roundF^[i] a).2.2, c ≤ B + i := by
  intro i
  induction i with
  | zero => simpa using hB
  | succ i ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨h1, ?_, ?_, ?_⟩
    · simp [roundF, h1]
    · simp [roundF, h1]
    · intro c hc
      simp only [roundF, List.mem_map, List.mem_range] at hc
      obtain ⟨j, -, rfl⟩ := hc
      have := getD_le_of _ _ j h4
      split_ifs <;> omega

theorem sc_length (s : (List Bool × (ℕ × ℕ)) × (List Bool × List ℕ)) :
    (sc s).length = 2 * (qc s.1).length + 2 * (listCode boolCode s.2.1).length +
      (listCode unaryCode s.2.2).length + 2 := by
  simp only [sc, prodCode, pairBits_length]; omega

theorem m_le_qc (q : List Bool × (ℕ × ℕ)) : q.2.2 ≤ (qc q).length := by
  simp only [qc, prodCode, pairBits_length, unaryCode, List.length_replicate]; omega

theorem lcBool_le (P : List Bool) : (listCode boolCode P).length ≤ P.length * 4 + 1 := by
  have := listCode_length_map_bound boolCode id P 1 (by intro a _; simp [boolCode])
  simpa using this

theorem lcUnary_le (C : List ℕ) (B : ℕ) (h : ∀ c ∈ C, c ≤ B) :
    (listCode unaryCode C).length ≤ C.length * (2 * B + 2) + 1 := by
  have := listCode_length_map_bound unaryCode id C B (by intro a ha; simpa [unaryCode] using h a ha)
  simpa using this

theorem round_growth (N : ℕ) (a : (List Bool × (ℕ × ℕ)) × (List Bool × List ℕ)) (i : ℕ) (hi : i ≤ N) :
    (sc (roundF^[i] a)).length ≤ (Polynomial.C 12 * (Polynomial.X + 1) ^ 2).eval (N + (sc a).length) := by
  have hL := sc_length a
  set L := (sc a).length
  have hB : ∀ c ∈ a.2.2, c ≤ L := fun c hc =>
    (listCode_elem_le _ c hc).trans (by omega)
  obtain ⟨h1, h2, h3, h4⟩ := round_inv a L hB i
  have hq : (qc a.1).length ≤ L := by omega
  have hm := m_le_qc a.1
  have hP0 := list_length_le_code boolCode a.2.1
  have hC0 := list_length_le_code unaryCode a.2.2
  have hP : (roundF^[i] a).2.1.length ≤ L := by
    have : max a.2.1.length a.1.2.2 ≤ L := max_le (by omega) (by omega)
    omega
  have hC : (roundF^[i] a).2.2.length ≤ L := by
    have : max a.2.2.length a.1.2.2 ≤ L := max_le (by omega) (by omega)
    omega
  have e1 := lcBool_le (roundF^[i] a).2.1
  have e2 := lcUnary_le (roundF^[i] a).2.2 (L + i) h4
  rw [sc_length, h1]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  have : (roundF^[i] a).2.2.length * (2 * (L + i) + 2) ≤ L * (2 * (L + N) + 2) :=
    Nat.mul_le_mul hC (by omega)
  push_cast
  nlinarith

/-- `n` rounds from the parameters. -/
noncomputable def roundsP : Procedure (prodCode unaryCode sc) sc (fun x => roundF^[x.1] x.2) :=
  roundP.iterate (Polynomial.C 12 * (Polynomial.X + 1) ^ 2) (fun N a i hi => round_growth N a i hi)


/-! ### Agreement with `SSG.peel`, `SSG.cnt` -/

section spec
open SSG SSG28Decode

theorem getD_map_range {α : Type} (m : ℕ) (f : ℕ → α) (d : α) (i : ℕ) (hi : i < m) :
    ((List.range m).map f).getD i d = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

variable (l : List Bool) (h : ValidL l)

/-- `peel G k` as a list. -/
def peelL (k : ℕ) : List Bool :=
  (List.range (nOf l)).map (fun i => if hi : i < nOf l then peel (gameOf l h) k ⟨i, hi⟩ else false)

/-- the counts after `k` rounds. -/
def cntL (k : ℕ) : List ℕ :=
  (List.range (nOf l)).map (fun i => if hi : i < nOf l then
    cnt (fun k' => peel (gameOf l h) (k' + 1) ⟨i, hi⟩) k else 0)

theorem peelL_get (k : ℕ) (j : Fin (nOf l)) : (peelL l h k).getD j false = peel (gameOf l h) k j := by
  unfold peelL; rw [getD_map_range _ _ _ _ j.2]; simp

theorem peelF_eq (k : ℕ) (i : Fin (nOf l)) :
    peelF (qOf l) (peelL l h k) i = peel (gameOf l h) (k + 1) i := by
  have cJ : (peelL l h k).getD (chF (qOf l) i 6) false = peel (gameOf l h) k ((gameOf l h).child i false) := by
    rw [← childJ_eq l h i]; exact peelL_get l h k _
  have cK : (peelL l h k).getD (chF (qOf l) i 7) false = peel (gameOf l h) k ((gameOf l h).child i true) := by
    rw [← childK_eq l h i]; exact peelL_get l h k _
  unfold peelF
  rw [peelL_get l h k i, cJ, cK]
  show _ = peelStep (gameOf l h) (peel (gameOf l h) k) i
  unfold peelStep
  rw [nodeType_eq l h i]
  generalize tyF (qOf l) i = t
  rcases t with _ | _ | _ | _ | t <;> simp [typeOf]

theorem roundF_state (k : ℕ) :
    roundF (qOf l, (peelL l h k, cntL l h k)) = (qOf l, (peelL l h (k + 1), cntL l h (k + 1))) := by
  have hP : (List.range (nOf l)).map (peelF (qOf l) (peelL l h k)) = peelL l h (k + 1) := by
    unfold peelL
    apply List.map_congr_left; intro i hi
    have hi' : i < nOf l := List.mem_range.mp hi
    rw [dif_pos hi']
    exact peelF_eq l h k ⟨i, hi'⟩
  simp only [roundF, qOf]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · exact hP
  · simp only
    simp only [show (List.range (nOf l)).map (peelF (l, (nOf l, nOf l)) (peelL l h k)) = peelL l h (k + 1) from hP]
    unfold cntL
    apply List.map_congr_left; intro i hi
    have hi' : i < nOf l := List.mem_range.mp hi
    rw [dif_pos hi', getD_map_range _ _ _ _ hi', dif_pos hi', peelL_get l h (k + 1) ⟨i, hi'⟩]
    simp [cnt]

theorem rounds_state (k : ℕ) :
    roundF^[k] (qOf l, (peelL l h 0, cntL l h 0)) = (qOf l, (peelL l h k, cntL l h k)) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, roundF_state]

theorem peelL_zero : peelL l h 0 = (List.range (nOf l)).map (fun _ => false) := by
  unfold peelL; apply List.map_congr_left; intro i _; split <;> rfl

theorem cntL_zero : cntL l h 0 = (List.range (nOf l)).map (fun _ => 0) := by
  unfold cntL; apply List.map_congr_left; intro i _; split <;> rfl

/-- after `n` rounds the counts are the ranks `prank`. -/
theorem cntL_n_get (i : Fin (nOf l)) : (cntL l h (nOf l)).getD i 0 = prank (gameOf l h) i := by
  unfold cntL; rw [getD_map_range _ _ _ _ i.2]; simp [prank]

theorem peelAll_iff_count : peelAll (gameOf l h) = decide ((peelL l h (nOf l)).count true = nOf l) := by
  rw [Bool.eq_iff_iff, peelAll_iff, decide_eq_true_iff]
  have hlen : (peelL l h (nOf l)).length = nOf l := by simp [peelL]
  have hc : (peelL l h (nOf l)).count true = nOf l ↔ ∀ b ∈ peelL l h (nOf l), b = true := by
    have e := List.count_eq_length (a := true) (l := peelL l h (nOf l))
    rw [hlen] at e
    rw [e]; exact forall₂_congr (fun b _ => eq_comm)
  rw [hc]
  constructor
  · intro H b hb
    simp only [peelL, List.mem_map, List.mem_range] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    rw [dif_pos hi]; exact H ⟨i, hi⟩
  · intro H i
    have := H _ (List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.2, rfl⟩)
    simpa [i.2] using this

end spec


/-! ### Initial state, `n` rounds, ranks, `peelAll`, weights -/

def initF (q : List Bool × (ℕ × ℕ)) : (List Bool × (ℕ × ℕ)) × (List Bool × List ℕ) :=
  (q, ((List.range q.2.2).map (fun _ => false), (List.range q.2.2).map (fun _ => 0)))

noncomputable def initP : Procedure qc sc initF := by
  let ps := (tabulate (f := fun (_ : List Bool × (ℕ × ℕ)) (_ : ℕ) => false) false
    (constant (prodCode unaryCode qc) boolCode false)).comp (nUOfQ.pair (identity qc))
  let cs := (tabulate (f := fun (_ : List Bool × (ℕ × ℕ)) (_ : ℕ) => (0 : ℕ)) 0
    (constant (prodCode unaryCode qc) unaryCode 0)).comp (nUOfQ.pair (identity qc))
  exact ((identity qc).pair (ps.pair cs)).congrFun (by intro q; rfl)

def finalF (q : List Bool × (ℕ × ℕ)) : (List Bool × (ℕ × ℕ)) × (List Bool × List ℕ) :=
  roundF^[q.2.2] (initF q)

noncomputable def finalP : Procedure qc sc finalF :=
  (roundsP.comp (nUOfQ.pair initP)).congrFun (by intro q; rfl)

theorem finalF_eq (l : List Bool) (h : SSG28Decode.ValidL l) :
    finalF (qOf l) = (qOf l, (peelL l h (SSG28Decode.nOf l), cntL l h (SSG28Decode.nOf l))) := by
  unfold finalF
  have : initF (qOf l) = (qOf l, (peelL l h 0, cntL l h 0)) := by
    rw [peelL_zero, cntL_zero]; rfl
  rw [this]; exact rounds_state l h _

/-- the ranks, in unary. -/
noncomputable def ranksP : Procedure qc (listCode unaryCode) (fun q => (finalF q).2.2) :=
  ((second (listCode boolCode) (listCode unaryCode)).comp
    ((second qc (prodCode (listCode boolCode) (listCode unaryCode))).comp finalP)).congrFun (by intro q; rfl)

/-- `peelAll`, as computed. -/
def peelAllF (q : List Bool × (ℕ × ℕ)) : Bool := decide ((finalF q).2.1.count true = q.2.1)

noncomputable def peelAllP : Procedure qc boolCode peelAllF := by
  let P := (first (listCode boolCode) (listCode unaryCode)).comp
    ((second qc (prodCode (listCode boolCode) (listCode unaryCode))).comp finalP)
  exact (eqP.comp ((unaryToBits.comp (countTrueP.comp P)).pair nBOfQ)).congrFun (by intro q; rfl)

theorem peelAllF_eq (l : List Bool) (h : SSG28Decode.ValidL l) :
    peelAllF (qOf l) = SSG.peelAll (SSG28Decode.gameOf l h) := by
  rw [peelAll_iff_count l h, peelAllF, finalF_eq l h]; rfl

theorem ranks_get (l : List Bool) (h : SSG28Decode.ValidL l) (i : Fin (SSG28Decode.nOf l)) :
    ((finalF (qOf l)).2.2).getD i 0 = SSG.prank (SSG28Decode.gameOf l h) i := by
  rw [finalF_eq l h]; exact cntL_n_get l h i

/-- multiplication by 3, and `3^c` from `c` in unary. -/
noncomputable def mul3 : Procedure Nat.bits Nat.bits (fun x => 3 * x) :=
  (binaryMul.comp ((constant Nat.bits Nat.bits 3).pair (identity Nat.bits))).congrFun (by intro x; rfl)

theorem iterate_mul3 (i a : ℕ) : (fun x => 3 * x)^[i] a = 3 ^ i * a := by
  induction i generalizing a with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih]; ring

theorem bits_length_mul3 (i a : ℕ) : (Nat.bits (3 ^ i * a)).length ≤ 2 * i + (Nat.bits a).length := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len, Nat.size_le]
  have h1 : a < 2 ^ a.size := Nat.lt_size_self a
  have h2 : 3 ^ i ≤ 4 ^ i := Nat.pow_le_pow_left (by norm_num) i
  have h3 : (4 : ℕ) ^ i = 2 ^ (2 * i) := by rw [pow_mul]; norm_num
  rw [pow_add, ← h3]
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · calc 3 ^ i * a ≤ 4 ^ i * a := Nat.mul_le_mul_right a h2
      _ < 4 ^ i * 2 ^ a.size := Nat.mul_lt_mul_of_pos_left h1 (by positivity)

noncomputable def pow3P : Procedure unaryCode Nat.bits (fun c => 3 ^ c) :=
  ((mul3.iterate (Polynomial.C 2 * Polynomial.X) (by
      intro n a i hi
      rw [iterate_mul3]
      have := bits_length_mul3 i a
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      nlinarith)).comp ((identity unaryCode).pair (constant unaryCode Nat.bits 1))).congrFun
    (by intro c; simp [iterate_mul3])

/-- the weight `2 - 3^{-c}` of rank `c`. -/
noncomputable def wtOfRankP : Procedure unaryCode ratCode (fun c => 2 - 1 / (3 ^ c : ℚ)) :=
  (ratSub.comp ((constant unaryCode ratCode 2).pair (ratInv.comp (natToRat.comp pow3P)))).congrFun
    (by intro c; simp)

/-- **(F) the weights** `wt G i = 2 - (1/3)^(prank G i)` of all nodes. -/
noncomputable def wtsP : Procedure qc (listCode ratCode)
    (fun q => (finalF q).2.2.map (fun c => 2 - 1 / (3 ^ c : ℚ))) :=
  ((listMap (0 : ℕ) (0 : ℚ) wtOfRankP).comp ranksP).congrFun (by intro q; rfl)

theorem wts_get (l : List Bool) (h : SSG28Decode.ValidL l) (i : Fin (SSG28Decode.nOf l)) :
    (((finalF (qOf l)).2.2.map (fun c => 2 - 1 / (3 ^ c : ℚ)))).getD i 0 =
      SSG.wt (SSG28Decode.gameOf l h) i := by
  have hlen : i.val < ((finalF (qOf l)).2.2).length := by
    rw [finalF_eq l h]; simp [cntL]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlen]
  simp only [Option.map_some, Option.getD_some]
  have := ranks_get l h i
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen] at this
  simp only [Option.getD_some] at this
  rw [this, SSG.wt, one_div_pow]


/-! ### `WellFormed` and the pre-check `okGame` -/

def isT0F (q : List Bool × (ℕ × ℕ)) (i : ℕ) : Bool := decide (tyF q i = 3)
def isT1F (q : List Bool × (ℕ × ℕ)) (i : ℕ) : Bool := decide (4 ≤ tyF q i)
def selfF (q : List Bool × (ℕ × ℕ)) (i : ℕ) : Bool :=
  !(decide (3 ≤ tyF q i)) || (decide (chF q i 6 = i) && decide (chF q i 7 = i))

def wfF (q : List Bool × (ℕ × ℕ)) : Bool :=
  decide (((List.range q.2.2).map (isT0F q)).count true = 1) &&
  (decide (((List.range q.2.2).map (isT1F q)).count true = 1) &&
   decide (((List.range q.2.2).map (selfF q)).count true = q.2.2))

/-- the pre-check, as computed. -/
def okF (q : List Bool × (ℕ × ℕ)) : Bool := wfF q && peelAllF q

/-- a per-node test on `(i unary, q)`, tabulated over the nodes. -/
noncomputable def tabNodes {g : List Bool × (ℕ × ℕ) → ℕ → Bool}
    (p : Procedure (prodCode unaryCode qc) boolCode (fun x => g x.2 x.1)) :
    Procedure qc (listCode boolCode) (fun q => (List.range q.2.2).map (g q)) :=
  ((tabulate (f := g) false p).comp (nUOfQ.pair (identity qc))).congrFun (by intro q; rfl)

noncomputable def tyU : Procedure (prodCode unaryCode qc) Nat.bits (fun x => tyF x.2 x.1) :=
  (unaryToBits.comp (tyP.comp ((unaryToBits.comp (first unaryCode qc)).pair (second unaryCode qc)))).congrFun
    (by intro x; rfl)
noncomputable def chU (k : ℕ) : Procedure (prodCode unaryCode qc) Nat.bits (fun x => chF x.2 x.1 k) :=
  (unaryToBits.comp ((chP k).comp ((unaryToBits.comp (first unaryCode qc)).pair (second unaryCode qc)))).congrFun
    (by intro x; rfl)
noncomputable def iU : Procedure (prodCode unaryCode qc) Nat.bits (fun x => x.1) :=
  unaryToBits.comp (first unaryCode qc)

noncomputable def isT0P : Procedure (prodCode unaryCode qc) boolCode (fun x => isT0F x.2 x.1) :=
  (eqP.comp (tyU.pair (constant (prodCode unaryCode qc) Nat.bits 3))).congrFun (by intro x; rfl)
noncomputable def isT1P : Procedure (prodCode unaryCode qc) boolCode (fun x => isT1F x.2 x.1) :=
  (binaryLe.comp ((constant (prodCode unaryCode qc) Nat.bits 4).pair tyU)).congrFun (by intro x; rfl)
noncomputable def selfP : Procedure (prodCode unaryCode qc) boolCode (fun x => selfF x.2 x.1) :=
  (boolOr.comp ((boolNot.comp (binaryLe.comp ((constant (prodCode unaryCode qc) Nat.bits 3).pair tyU))).pair
    (boolAnd.comp ((eqP.comp ((chU 6).pair iU)).pair (eqP.comp ((chU 7).pair iU)))))).congrFun
    (by intro x; rfl)

noncomputable def wfP : Procedure qc boolCode wfF := by
  let c0 := oneHotP.comp (tabNodes isT0P)
  let c1 := oneHotP.comp (tabNodes isT1P)
  let c2 := eqP.comp ((unaryToBits.comp (countTrueP.comp (tabNodes selfP))).pair (unaryToBits.comp nUOfQ))
  exact (boolAnd.comp (c0.pair (boolAnd.comp (c1.pair c2)))).congrFun (by intro q; rfl)

/-- **(E) the pre-check procedure**: `okGame` (`WellFormed && peelAll`) of the decoded game. -/
noncomputable def okP : Procedure qc boolCode okF :=
  (boolAnd.comp (wfP.pair peelAllP)).congrFun (by intro q; rfl)

theorem count_map_range_sum (n : ℕ) (c : ℕ → Bool) :
    ((List.range n).map c).count true = ∑ i ∈ Finset.range n, (if c i then 1 else 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.count_append, ih, Finset.sum_range_succ]
    cases hcn : c n <;> simp [hcn, List.count_singleton]

theorem card_filter_eq_count (n : ℕ) (p : Fin n → Prop) [DecidablePred p] (c : ℕ → Bool)
    (hc : ∀ i : Fin n, p i ↔ c i = true) :
    (Finset.univ.filter p).card = ((List.range n).map c).count true := by
  rw [Finset.card_filter, count_map_range_sum, ← Fin.sum_univ_eq_sum_range (fun i => if c i then 1 else 0)]
  apply Finset.sum_congr rfl; intro i _
  by_cases h : p i
  · simp [h, (hc i).mp h]
  · have : c i = false := by simpa [hc i] using h
    simp [h, this]

theorem wfF_eq (l : List Bool) (h : SSG28Decode.ValidL l) :
    wfF (qOf l) = decide (SSG.WellFormed (SSG28Decode.gameOf l h)) := by
  set G := SSG28Decode.gameOf l h
  have e0 := card_filter_eq_count _ (fun i => G.nodeType i = .terminal0) (isT0F (qOf l)) (by
    intro i; rw [nodeType_eq l h i]; unfold isT0F; generalize tyF (qOf l) i = t
    rcases t with _ | _ | _ | _ | t <;> simp [SSG28Decode.typeOf])
  have e1 := card_filter_eq_count _ (fun i => G.nodeType i = .terminal1) (isT1F (qOf l)) (by
    intro i; rw [nodeType_eq l h i]; unfold isT1F; generalize tyF (qOf l) i = t
    rcases t with _ | _ | _ | _ | t <;> simp [SSG28Decode.typeOf])
  rw [Bool.eq_iff_iff, decide_eq_true_iff, SSG.WellFormed, e0, e1]
  unfold wfF
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  apply and_congr_right; intro _; apply and_congr_right; intro _
  show ((List.range (SSG28Decode.nOf l)).map (selfF (qOf l))).count true = SSG28Decode.nOf l ↔ _
  rw [count_map_eq_length_iff]
  constructor
  · intro H i hT
    have := H i i.2
    unfold selfF at this
    have h3 : 3 ≤ tyF (qOf l) i := by
      unfold SSG.isTerminal at hT; rw [nodeType_eq l h i] at hT
      revert hT; generalize tyF (qOf l) i = t; rcases t with _ | _ | _ | _ | t <;> simp [SSG28Decode.typeOf]
    simp only [h3, decide_true, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_iff] at this
    exact ⟨Fin.ext (by rw [childJ_eq l h i]; exact this.1), Fin.ext (by rw [childK_eq l h i]; exact this.2)⟩
  · intro H i hi
    unfold selfF
    by_cases h3 : 3 ≤ tyF (qOf l) i
    · have hT : SSG.isTerminal G ⟨i, hi⟩ = true := by
        unfold SSG.isTerminal; rw [nodeType_eq l h ⟨i, hi⟩]
        revert h3; generalize tyF (qOf l) i = t; rcases t with _ | _ | _ | _ | t <;> simp [SSG28Decode.typeOf]
      obtain ⟨hj, hk⟩ := H ⟨i, hi⟩ hT
      have hj' := congrArg Fin.val hj; have hk' := congrArg Fin.val hk
      rw [childJ_eq l h] at hj'; rw [childK_eq l h] at hk'
      simp [h3, hj', hk']
    · simp [h3]

theorem okF_eq (l : List Bool) (h : SSG28Decode.ValidL l) :
    okF (qOf l) = SSG28Reply.okGame (SSG28Decode.gameOf l h) := by
  rw [okF, wfF_eq l h, peelAllF_eq l h]; rfl

end SSG28MachineProcD2
