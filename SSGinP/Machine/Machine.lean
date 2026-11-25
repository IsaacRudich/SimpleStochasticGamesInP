module

public import SSGinP.Machine.MachineElim
public import SSGinP.Machine.MachineBound
public import SSGinP.Machine.Reply

@[expose] public section

/-!
# SSGinP.Machine.Machine: THE MACHINE THEOREM

From
* oracle elimination (`SSG28MachineElim.eliminate`),
* the sign-recovery machine `OracleSpec.ExtremalSignRecovery` (hypothesis `hESR`),
* the single-call reduction (hypothesis `hcorr`, `single_call_correct`),
* the driver procedure (hypothesis `drv`) and the reply procedure (hypothesis `rep`),
there is ONE closed `BitProgram` deciding, on every input word `x`, whether `x` decodes to a game with property `P`,
within `(|x| + 2)^d` steps.
-/

namespace SSG28Machine

open SSG SSG28Reply SSG28Search SSG28MachineElim SSG28MachineBound
open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.ExactQuantumFactoring.BitStackProgram

/-- the query words, as data: index and the list of prices. -/
def eqCode (a : ℕ × List ℚ) : Word := encodeNat a.1 ++ a.2.flatMap encodeRat

theorem flatMap_encodeRat_inj' : ∀ (l l' : List ℚ), l.flatMap encodeRat = l'.flatMap encodeRat → l = l'
  | [], [], _ => rfl
  | [], y :: l', h => by simp [encodeRat] at h
  | x :: l, [], h => by simp [encodeRat] at h
  | x :: l, y :: l', h => by
    simp only [List.flatMap_cons] at h
    obtain ⟨hxy, h⟩ := encodeRat_append_inj h
    rw [hxy, flatMap_encodeRat_inj' l l' h]

theorem eqCode_eq {N : ℕ} {a : ℕ × List ℚ} {i : Fin N} {q : Fin N → ℚ} (h : eqCode a = priceQuery i q) :
    a = (i.val, List.ofFn q) := by
  unfold eqCode priceQuery at h
  obtain ⟨h1, h2⟩ := encodeNat_append_inj h
  rw [Prod.ext_iff]; exact ⟨h1, flatMap_encodeRat_inj' _ _ h2⟩

open Classical in
/-- the reply as a function of (input word, query data). -/
noncomputable def replyL (θ : ℕ → ℚ) (xa : Word × (ℕ × List ℚ)) : Bool :=
  match SSG28Decode.decode xa.1 with
  | some ⟨n, G⟩ =>
    if h : xa.2.1 < 2 * n + 1 ∧ xa.2.2.length = 2 * n + 1 then
      okGame G && replyGood G (θ n) (rDelta n) ⟨xa.2.1, h.1⟩ (fun g => xa.2.2.get ⟨g.val, by omega⟩)
    else false
  | none => false

theorem ssgReply_eqCode {n : ℕ} (G : Game n) (θ δ : ℚ) (a : ℕ × List ℚ) :
    ssgReply G θ δ (eqCode a) =
      if h : a.1 < 2 * n + 1 ∧ a.2.length = 2 * n + 1 then
        okGame G && replyGood G θ δ ⟨a.1, h.1⟩ (fun g => a.2.get ⟨g.val, by omega⟩)
      else false := by
  by_cases h : a.1 < 2 * n + 1 ∧ a.2.length = 2 * n + 1
  · rw [dif_pos h]
    have e : eqCode a = priceQuery (⟨a.1, h.1⟩ : Fin (2*n+1)) (fun g => a.2.get ⟨g.val, by omega⟩) := by
      unfold eqCode priceQuery
      congr 2
      exact (List.ext_getElem (by simp [h.2]) (fun k h1 h2 => by simp only [List.getElem_ofFn, List.get_eq_getElem])).symm
    rw [e, ssgReply_priceQuery]
  · rw [dif_neg h]
    unfold ssgReply
    rw [dif_neg]
    rintro ⟨⟨i, q⟩, hq⟩
    have := eqCode_eq hq
    apply h; rw [this]; simp only [List.length_ofFn]; exact ⟨i.isLt, trivial⟩

theorem replyW_eqCode (θ : ℕ → ℚ) (x : Word) (a : ℕ × List ℚ) : replyW θ x (eqCode a) = replyL θ (x, a) := by
  unfold replyW replyL
  rcases SSG28Decode.decode x with _ | ⟨n, G⟩
  · rfl
  · exact ssgReply_eqCode G (θ n) (rDelta n) a

theorem decode_len {x : Word} {n : ℕ} {G : Game n} (h : SSG28Decode.decode x = some ⟨n, G⟩) : n ≤ x.length := by
  unfold SSG28Decode.decode at h
  split_ifs at h with hv
  simp only [Option.some.injEq, Sigma.mk.injEq] at h
  obtain ⟨rfl, _⟩ := h
  have h1 := hv.1; have h2 := hv.2.1
  rw [List.length_reverse] at h2
  rw [h2]; nlinarith

/-- all replies `false`: the sign machine outputs `false`. -/
theorem pricePost_false {N R : ℕ} {anchor : Fin N} {h : Transcript} {out : Word}
    (hp : pricePost R anchor h out) (hall : ∀ e ∈ h, e.2 = [false]) : out = [false] :=
  hp.2.2 false Set.univ (fun _ => 0) trivial (by simp) (fun _ _ _ hmem _ _ => hall _ hmem)

theorem computesWithin_mono {p : BitProgram} {o : WordOracle} {x : Word} {T T' : ℕ}
    {P Q : Transcript → Word → Prop} (hT : T ≤ T') (hPQ : ∀ h out, P h out → Q h out)
    (hp : p.ComputesWithin o x T P) : p.ComputesWithin o x T' Q := by
  obtain ⟨e, c, hr, he, hc, hP⟩ := hp
  exact ⟨e, c, hr, he.trans hT, hc, hPQ _ _ hP⟩

/-! ### the time bound -/

theorem log2_rR (n : ℕ) : (rR n + 1).log2 ≤ 5 * n + 8 := by
  have h : (rR n + 1).log2 < 5 * n + 9 := by
    rw [Nat.log2_lt (by omega)]
    have h27 : 27 ^ n ≤ 32 ^ n := Nat.pow_le_pow_left (by norm_num) n
    have h32 : (32 : ℕ) ^ n = 2 ^ (5 * n) := by rw [pow_mul]; norm_num
    have : 2 ^ (5 * n + 9) = 512 * 2 ^ (5 * n) := by rw [pow_add]; ring
    have h1 : 1 ≤ 27 ^ n := Nat.one_le_pow _ _ (by norm_num)
    unfold rR rK; rw [this]; omega
  omega

theorem tbound (coef deg xl M : ℕ) (hM : M ≤ 10 * (xl + 2)) :
    coef * M ^ deg ≤ (xl + 2) ^ (coef + 5 * deg) := by
  have h10 : 10 * (xl + 2) ≤ (xl + 2) ^ 5 := by
    have : (xl + 2) ^ 5 = (xl + 2) ^ 4 * (xl + 2) := pow_succ _ _
    have h16 : 16 ≤ (xl + 2) ^ 4 := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ (xl + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    rw [this]; nlinarith
  have hp : M ^ deg ≤ (xl + 2) ^ (5 * deg) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (hM.trans h10) deg
  calc coef * M ^ deg ≤ (xl + 2) ^ coef * (xl + 2) ^ (5 * deg) :=
        Nat.mul_le_mul (le_pow_self coef xl) hp
    _ = _ := (pow_add _ _ _).symm

theorem elimBound_le {χ α : Type} {ex : χ → Word} {eq : α → Word} {d : χ → Word} {r : χ × α → Bool}
    (drv : Procedure ex (id : Word → Word) d) (proc : Procedure (prodCode ex eq) Procedure.boolCode r) :
    ∃ e0 kr, ∀ E, e0 ≤ E → ∀ xl T, T ≤ (xl + 2) ^ E →
      elimBound drv proc xl T ≤ (xl + 2) ^ (7 + 2 * E + (E + 5) * kr) := by
  obtain ⟨kd, hkd⟩ := poly_le drv.bound
  obtain ⟨kr, hkr⟩ := poly_le proc.bound
  refine ⟨1 + kd, kr, fun E hE xl T hT => ?_⟩
  set B := (xl + 2) ^ E with hB
  have hB1 : 1 ≤ B := one_le_pow xl E
  have hx : xl ≤ B := by
    calc xl ≤ (xl + 2) ^ 1 := by simp
      _ ≤ B := pow_mono (by omega)
  have hd : drv.bound.eval xl ≤ B := (hkd xl).trans (pow_mono (by omega))
  have h8 : 8 * B ≤ (xl + 2) ^ (E + 3) := by
    have : (xl + 2) ^ (E + 3) = B * (xl + 2) ^ 3 := by rw [hB, pow_add]
    have h3 : 8 ≤ (xl + 2) ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ (xl + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    rw [this]; nlinarith
  set C := (xl + 2) ^ ((E + 5) * kr) with hC
  have hC1 : 1 ≤ C := one_le_pow xl _
  have hy : proc.bound.eval (2 * xl + (xl + drv.bound.eval xl + T) + 1) ≤ C := by
    refine (hkr _).trans (comp_le (a := E + 3) ?_)
    omega
  have hs : stepB proc (xl + drv.bound.eval xl + T) xl ≤ 41 * B + C := by
    unfold stepB; omega
  have hT' : T * stepB proc (xl + drv.bound.eval xl + T) xl ≤ B * (41 * B + C) := Nat.mul_le_mul hT hs
  have h128 : 128 ≤ (xl + 2) ^ 7 := by
    calc 128 = 2 ^ 7 := by norm_num
      _ ≤ (xl + 2) ^ 7 := Nat.pow_le_pow_left (by omega) 7
  have hfin : elimBound drv proc xl T ≤ 128 * (B * B * C) := by
    unfold elimBound
    have : B * (41 * B + C) = 41 * (B * B) + B * C := by ring
    have hBB : B ≤ B * B := Nat.le_mul_of_pos_left B hB1
    have hBBC : B * B ≤ B * B * C := Nat.le_mul_of_pos_right _ hC1
    have hBC : B * C ≤ B * B * C := by nlinarith
    omega
  calc elimBound drv proc xl T ≤ 128 * (B * B * C) := hfin
    _ ≤ (xl + 2) ^ 7 * (B * B * C) := Nat.mul_le_mul_right _ h128
    _ = (xl + 2) ^ (7 + 2 * E + (E + 5) * kr) := by rw [hB, hC, pow_add, pow_add, two_mul, pow_add]; ring

/-! ### the theorem -/

open Classical in
/-- **THE MACHINE THEOREM** (given the two procedures and the two search theorems). -/
theorem machine (θ : ℕ → ℚ) (P : ∀ {n : ℕ}, Game n → Prop)
    (hESR : ExtremalSignRecovery)
    (hcorr : ∀ (n : ℕ) (G : Game n) (h : Transcript) (out : Word),
      pricePost (N := 2 * n + 1) (rR n) (dummy n) h out →
      (∀ e ∈ h, e.2 = [ssgReply G (θ n) (rDelta n) e.1]) → out = [decide (P G)])
    (drv : Procedure (id : Word → Word) (id : Word → Word) driverW)
    (rep : Procedure (prodCode (id : Word → Word) eqCode) Procedure.boolCode (replyL θ)) :
    ∃ (M : BitProgram) (d : ℕ), SSG28Closed.Closed M ∧ ∀ x : Word,
      SSG28Closed.DecidesWithin M x ((x.length + 2) ^ d)
        (decide (∃ n G, SSG28Decode.decode x = some ⟨n, G⟩ ∧ P G)) := by
  obtain ⟨p, coef, deg, hp⟩ := hESR
  obtain ⟨hclosed, helim⟩ := eliminate p drv rep
  obtain ⟨e0, kr, hbound⟩ := elimBound_le drv rep
  set E := e0 + coef + 5 * deg
  refine ⟨closedProg p drv rep, 7 + 2 * E + (E + 5) * kr, hclosed, fun x => ?_⟩
  have hb : ∀ T, T ≤ (x.length + 2) ^ E →
      elimBound drv rep x.length T ≤ (x.length + 2) ^ (7 + 2 * E + (E + 5) * kr) :=
    fun T hT => hbound E (by omega) x.length T hT
  have hR : ∀ a, replyW θ x (eqCode a) = replyL θ (x, a) := replyW_eqCode θ x
  cases hd : SSG28Decode.decode x with
  | none =>
    have hp1 := hp 1 1 one_pos one_pos 0 (fun _ w => replyW θ x w)
    have hdrv : driverW x = priceInput (N := 1) 1 0 := by simp [driverW, hd]
    rw [← hdrv] at hp1
    have hp2 := computesWithin_mono le_rfl
      (Q := fun h out => pricePost (N := 1) 1 0 h out ∧ ∀ e ∈ h, ∃ a, e.1 = eqCode a)
      (fun h out hpp => ⟨hpp, fun e he => by
        obtain ⟨i, q, hq⟩ := hpp.1 e he; exact ⟨(i.val, List.ofFn q), hq⟩⟩) hp1
    have hc := helim x (replyW θ x) hR _ _ hp2
    have hT : coef * (1 + (1 + 1).log2 + 1) ^ deg ≤ (x.length + 2) ^ E :=
      (tbound coef deg x.length _ (by simp; omega)).trans (pow_mono (by omega))
    refine computesWithin_mono (hb _ hT) ?_ hc
    rintro h out ⟨_, hist, hpp, hans⟩
    have : out = [false] := pricePost_false hpp (fun e he => by rw [hans e he]; simp [replyW, hd])
    rw [this]; simp
  | some ng =>
    obtain ⟨n, G⟩ := ng
    have hp1 := hp (2 * n + 1) (rR n) (by omega) (by unfold rR rK; positivity) (dummy n) (fun _ w => replyW θ x w)
    have hdrv : driverW x = priceInput (rR n) (dummy n) := by simp [driverW, hd]
    rw [← hdrv] at hp1
    have hp2 := computesWithin_mono le_rfl
      (Q := fun h out => pricePost (N := 2 * n + 1) (rR n) (dummy n) h out ∧ ∀ e ∈ h, ∃ a, e.1 = eqCode a)
      (fun h out hpp => ⟨hpp, fun e he => by
        obtain ⟨i, q, hq⟩ := hpp.1 e he; exact ⟨(i.val, List.ofFn q), hq⟩⟩) hp1
    have hc := helim x (replyW θ x) hR _ _ hp2
    have hn := decode_len hd
    have hT : coef * (2 * n + 1 + (rR n + 1).log2 + 1) ^ deg ≤ (x.length + 2) ^ E :=
      (tbound coef deg x.length _ (by have := log2_rR n; omega)).trans (pow_mono (by omega))
    refine computesWithin_mono (hb _ hT) ?_ hc
    rintro h out ⟨_, hist, hpp, hans⟩
    have : out = [decide (P G)] := hcorr n G hist out hpp (fun e he => by rw [hans e he]; simp [replyW, hd])
    rw [this]
    congr 2
    apply propext
    constructor
    · intro hP; exact ⟨n, G, rfl, hP⟩
    · rintro ⟨n', G', h', hP⟩
      cases h'
      exact hP

end SSG28Machine
