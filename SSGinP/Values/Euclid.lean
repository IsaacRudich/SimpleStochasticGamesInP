module

public import SSGinP.Values.Ctx

@[expose] public section

/-!
# SSGinP.Values.Euclid: the reconstruction `exactOf` as a BitStack `Procedure`

* `cfStepP`        : one step `SSGValues.cfStep` of the Euclid / continued-fraction loop, on the state code `cfC`.
* `CfBnd`, `cfStep_bnd`, `cfC_growth` : the UNIVERSAL size bound needed by `Procedure.iterate`: for an arbitrary
                     state, `r0·s1 + r1·s0` and `r0·q1 + r1·q0` are invariant under a step, so every component of
                     every iterate is bounded by a quantity read off the initial state.
* `cfIterP`        : the loop.
* `exactP`         : `(n, a) ↦ exactOf n a`, with `n` in unary and `a` in binary.
-/

set_option linter.unusedSimpArgs false

namespace SSGValuesEuclid

open SSGValues SSGValuesCtx
open OAI.ExactQuantumFactoring.BitStackProgram OAI.ExactQuantumFactoring.BitStackProgram.Procedure

abbrev nn : ℕ × ℕ → List Bool := prodCode Nat.bits Nat.bits
abbrev cfC : CFState → List Bool := prodCode nn (prodCode nn (prodCode nn nn))

/-! ## the step -/

section Step
noncomputable def pNQ : Procedure cfC nn (fun st => st.1) := first nn (prodCode nn (prodCode nn nn))
noncomputable def pT1 : Procedure cfC (prodCode nn (prodCode nn nn)) (fun st => st.2) :=
  second nn (prodCode nn (prodCode nn nn))
noncomputable def pR : Procedure cfC nn (fun st => st.2.1) := (first nn (prodCode nn nn)).comp pT1
noncomputable def pT2 : Procedure cfC (prodCode nn nn) (fun st => st.2.2) := (second nn (prodCode nn nn)).comp pT1
noncomputable def pS : Procedure cfC nn (fun st => st.2.2.1) := (first nn nn).comp pT2
noncomputable def pQ : Procedure cfC nn (fun st => st.2.2.2) := (second nn nn).comp pT2

noncomputable def fst2 {α : Type} {ea : α → List Bool} {f : α → ℕ × ℕ} (p : Procedure ea nn f) :
    Procedure ea Nat.bits (fun x => (f x).1) := (first Nat.bits Nat.bits).comp p
noncomputable def snd2 {α : Type} {ea : α → List Bool} {f : α → ℕ × ℕ} (p : Procedure ea nn f) :
    Procedure ea Nat.bits (fun x => (f x).2) := (second Nat.bits Nat.bits).comp p

noncomputable def cfPassP : Procedure cfC boolCode cfPass := by
  let t1 := binaryLe.comp ((snd2 pQ).pair (snd2 pNQ))
  let lhs := binaryMul.comp ((binaryMul.comp ((binaryMul.comp ((constant cfC Nat.bits 2).pair (snd2 pNQ))).pair
    (snd2 pNQ))).pair (snd2 pR))
  let rhs := binaryMul.comp ((fst2 pNQ).pair (snd2 pQ))
  exact (boolAnd.comp (t1.pair (binaryLt.comp (lhs.pair rhs)))).congrFun (by intro st; rfl)

noncomputable def cfAdvP : Procedure cfC cfC cfAdv := by
  let dm := binaryDivMod.comp ((fst2 pR).pair (snd2 pR))
  let c := fst2 dm
  let md := snd2 dm
  let s' := (snd2 pS).pair (binaryAdd.comp ((fst2 pS).pair (binaryMul.comp (c.pair (snd2 pS)))))
  let q' := (snd2 pQ).pair (binaryAdd.comp ((fst2 pQ).pair (binaryMul.comp (c.pair (snd2 pQ)))))
  exact (pNQ.pair (((snd2 pR).pair md).pair (s'.pair q'))).congrFun (by intro st; rfl)

noncomputable def cfStepP : Procedure cfC cfC cfStep :=
  (conditional cfPassP (identity cfC) cfAdvP).congrFun (by intro st; rfl)
end Step

/-! ## the universal size bound -/

/-- all components, and the two invariants, are at most `K`. -/
def CfBnd (K : ℕ) (st : CFState) : Prop :=
  st.1.1 ≤ K ∧ st.1.2 ≤ K ∧ st.2.1.1 ≤ K ∧ st.2.1.2 ≤ K ∧ st.2.2.1.1 ≤ K ∧ st.2.2.1.2 ≤ K ∧
    st.2.2.2.1 ≤ K ∧ st.2.2.2.2 ≤ K ∧
    st.2.1.1 * st.2.2.1.2 + st.2.1.2 * st.2.2.1.1 ≤ K ∧ st.2.1.1 * st.2.2.2.2 + st.2.1.2 * st.2.2.2.1 ≤ K

theorem adv_aux (r0 r1 t0 t1 K : ℕ) (h0 : t0 ≤ K) (hI : r0 * t1 + r1 * t0 ≤ K) :
    t0 + r0 / r1 * t1 ≤ K ∧ r1 * (t0 + r0 / r1 * t1) + r0 % r1 * t1 ≤ K := by
  have hdm : r1 * (r0 / r1) + r0 % r1 = r0 := Nat.div_add_mod r0 r1
  have e : r1 * (t0 + r0 / r1 * t1) + r0 % r1 * t1 = r0 * t1 + r1 * t0 := by
    have : r1 * (t0 + r0 / r1 * t1) + r0 % r1 * t1 = (r1 * (r0 / r1) + r0 % r1) * t1 + r1 * t0 := by ring
    rw [this, hdm]
  refine ⟨?_, by rw [e]; exact hI⟩
  rcases Nat.eq_zero_or_pos r1 with h | h
  · subst h; simpa using h0
  · have h1 : t0 + r0 / r1 * t1 ≤ r1 * (t0 + r0 / r1 * t1) := Nat.le_mul_of_pos_left _ h
    have h2 : r1 * (t0 + r0 / r1 * t1) ≤ r0 * t1 + r1 * t0 := by rw [← e]; exact Nat.le_add_right _ _
    omega

theorem cfStep_bnd (K : ℕ) (st : CFState) (h : CfBnd K st) : CfBnd K (cfStep st) := by
  unfold cfStep
  split
  · exact h
  · obtain ⟨⟨N, Q⟩, ⟨r0, r1⟩, ⟨s0, s1⟩, ⟨q0, q1⟩⟩ := st
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
    simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    obtain ⟨a1, a2⟩ := adv_aux r0 r1 s0 s1 K h5 h9
    obtain ⟨b1, b2⟩ := adv_aux r0 r1 q0 q1 K h7 h10
    have hm : r0 % r1 ≤ r0 := Nat.mod_le _ _
    exact ⟨h1, h2, h4, hm.trans h3, h6, a1, h8, b1, a2, b2⟩

theorem cfStep_iter_bnd (K : ℕ) (st : CFState) (h : CfBnd K st) : ∀ i, CfBnd K (cfStep^[i] st)
  | 0 => h
  | i + 1 => by rw [Function.iterate_succ_apply']; exact cfStep_bnd K _ (cfStep_iter_bnd K st h i)

theorem lt_pow_of_bits {x L : ℕ} (h : x.bits.length ≤ L) : x < 2 ^ L :=
  lt_of_lt_of_le (Nat.lt_size_self x) (Nat.pow_le_pow_right (by norm_num) (by rw [← Nat.size_eq_bits_len]; exact h))

theorem bits_of_lt_pow {x L : ℕ} (h : x < 2 ^ L) : x.bits.length ≤ L := by
  rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr h

theorem cfC_length (st : CFState) : (cfC st).length =
    4 * st.1.1.bits.length + 2 * st.1.2.bits.length + 4 * st.2.1.1.bits.length + 2 * st.2.1.2.bits.length +
    4 * st.2.2.1.1.bits.length + 2 * st.2.2.1.2.bits.length + 2 * st.2.2.2.1.bits.length +
    st.2.2.2.2.bits.length + 10 := by
  simp only [cfC, nn, prodCode, pairBits_length]; omega

/-- **the universal growth bound of the loop.** -/
theorem cfC_growth (st : CFState) (i : ℕ) :
    (cfC (cfStep^[i] st)).length ≤ 42 * (cfC st).length + 94 := by
  set L := (cfC st).length with hL
  have hlen := cfC_length st
  obtain ⟨⟨N, Q⟩, ⟨r0, r1⟩, ⟨s0, s1⟩, ⟨q0, q1⟩⟩ := st
  simp only at hlen
  set P := 2 ^ L with hP
  have cN : N < P := lt_pow_of_bits (by omega)
  have cQ : Q < P := lt_pow_of_bits (by omega)
  have cr0 : r0 < P := lt_pow_of_bits (by omega)
  have cr1 : r1 < P := lt_pow_of_bits (by omega)
  have cs0 : s0 < P := lt_pow_of_bits (by omega)
  have cs1 : s1 < P := lt_pow_of_bits (by omega)
  have cq0 : q0 < P := lt_pow_of_bits (by omega)
  have cq1 : q1 < P := lt_pow_of_bits (by omega)
  have m1 : r0 * s1 < P * P := Nat.mul_lt_mul'' cr0 cs1
  have m2 : r1 * s0 < P * P := Nat.mul_lt_mul'' cr1 cs0
  have m3 : r0 * q1 < P * P := Nat.mul_lt_mul'' cr0 cq1
  have m4 : r1 * q0 < P * P := Nat.mul_lt_mul'' cr1 cq0
  have hP1 : 1 ≤ P := Nat.one_le_two_pow
  have hPP : P ≤ P * P := Nat.le_mul_of_pos_left P hP1
  have hK : 2 ^ (2 * L + 4) = 16 * (P * P) := by rw [hP, pow_add, two_mul, pow_add]; ring
  have hb : CfBnd (2 ^ (2 * L + 4) - 1) ((N, Q), (r0, r1), (s0, s1), (q0, q1)) := by
    rw [hK]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only <;> omega
  have hi := cfStep_iter_bnd _ _ hb i
  have hpos : 0 < 2 ^ (2 * L + 4) := by positivity
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -, -⟩ := hi
  rw [cfC_length]
  have b1 := bits_of_lt_pow (show (cfStep^[i] ((N, Q), (r0, r1), (s0, s1), (q0, q1))).1.1 < 2 ^ (2 * L + 4) by omega)
  have b2 := bits_of_lt_pow (show (cfStep^[i] ((N, Q), (r0, r1), (s0, s1), (q0, q1))).1.2 < 2 ^ (2 * L + 4) by omega)
  have b3 := bits_of_lt_pow (show (cfStep^[i] ((N, Q), (r0, r1), (s0, s1), (q0, q1))).2.1.1 < 2 ^ (2 * L + 4) by omega)
  have b4 := bits_of_lt_pow (show (cfStep^[i] ((N, Q), (r0, r1), (s0, s1), (q0, q1))).2.1.2 < 2 ^ (2 * L + 4) by omega)
  have b5 := bits_of_lt_pow (show (cfStep^[i] ((N, Q), (r0, r1), (s0, s1), (q0, q1))).2.2.1.1 < 2 ^ (2 * L + 4) by omega)
  have b6 := bits_of_lt_pow (show (cfStep^[i] ((N, Q), (r0, r1), (s0, s1), (q0, q1))).2.2.1.2 < 2 ^ (2 * L + 4) by omega)
  have b7 := bits_of_lt_pow (show (cfStep^[i] ((N, Q), (r0, r1), (s0, s1), (q0, q1))).2.2.2.1 < 2 ^ (2 * L + 4) by omega)
  have b8 := bits_of_lt_pow (show (cfStep^[i] ((N, Q), (r0, r1), (s0, s1), (q0, q1))).2.2.2.2 < 2 ^ (2 * L + 4) by omega)
  omega

/-- the loop. -/
noncomputable def cfIterP : Procedure (prodCode unaryCode cfC) cfC (fun x => cfStep^[x.1] x.2) :=
  cfStepP.iterate (Polynomial.C 42 * Polynomial.X + Polynomial.C 94) (by
    intro n a i _
    have h := cfC_growth a i
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    omega)

/-! ## `exactOf` -/

theorem iterate_mul3 (i a : ℕ) : (fun x => 3 * x)^[i] a = 3 ^ i * a := by
  induction i generalizing a with
  | zero => simp
  | succ i ih => rw [Function.iterate_succ_apply', ih]; ring

theorem bits_mul3 (a : ℕ) : (3 * a).bits.length ≤ a.bits.length + 2 := by
  apply bits_of_lt_pow
  have h := Nat.lt_size_self a
  rw [Nat.size_eq_bits_len, pow_add]
  norm_num
  omega

noncomputable def mul3 : Procedure Nat.bits Nat.bits (fun x => 3 * x) :=
  (binaryMul.comp ((constant Nat.bits Nat.bits 3).pair (identity Nat.bits))).congrFun (by intro x; rfl)

noncomputable def pow3P : Procedure (prodCode unaryCode Nat.bits) Nat.bits (fun x => 3 ^ x.1 * x.2) :=
  (mul3.iterateLinear 2 bits_mul3).congrFun (by intro x; exact iterate_mul3 x.1 x.2)

/-- **the reconstruction as a procedure**: `(n, a) ↦ exactOf n a`. -/
noncomputable def exactP : Procedure (prodCode unaryCode Nat.bits) ratCode (fun x => exactOf x.1 x.2) := by
  let e := prodCode unaryCode Nat.bits
  let nU := first unaryCode Nat.bits
  let aB := second unaryCode Nat.bits
  let one := constant e Nat.bits 1
  let zero := constant e Nat.bits 0
  let m42 := unarySuccessor.comp (unarySuccessor.comp (unaryMul.comp ((constant e unaryCode 4).pair nU)))
  let m32 := unarySuccessor.comp (unarySuccessor.comp (unaryMul.comp ((constant e unaryCode 3).pair nU)))
  let Np := pow2P.comp (m42.pair one)
  let Qp := pow3P.comp (nU.pair one)
  let A := doubleOne.comp aB
  let init : Procedure e cfC (fun x => ((2 ^ (4 * x.1).succ.succ * 1, 3 ^ x.1 * 1),
      (2 ^ (4 * x.1).succ.succ * 1, 2 * x.2 + 1), (1, 0), (0, 1))) :=
    (Np.pair Qp).pair ((Np.pair A).pair ((one.pair zero).pair (zero.pair one)))
  let fin := cfIterP.comp (m32.pair init)
  exact (ratDiv.comp ((natToRat.comp (snd2 (pS.comp fin))).pair (natToRat.comp (snd2 (pQ.comp fin))))).congrFun (by
    intro x
    simp only [Function.comp, exactOf, recon, cfInit, cfOut, Nat.succ_eq_add_one, mul_one])

end SSGValuesEuclid
