module

public import SSGinP.Values.Ctx
public import SSGinP.Bridge.Simulate
public import SSGinP.Bridge.EncodeDecode

@[expose] public section

/-!
# SSGinP.Values.Call: ONE ENGINE CALL as a BitStack `Procedure`

* `callMachine` : one closed `BitProgram` that, on EVERY word `x`, halts within `(|x|+2)^d` steps with one output
                  bit `b`; and if `x = ctxCode ((encode ⟨n, G⟩).reverse, (k, (a, j)))` for a well-formed Stopping
                  Game `G` with stable assignment `v`, then `b = true` if `thr a j + 1/(4·9^n) ≤ v k` and
                  `b = false` if `v k ≤ thr a j - 1/(4·9^n)`  (`CallSpec`).
                  Proof: `SSG28MachineElim.eliminate` with context type `Word` (driver and reply procedure parse
                  the context word), the ported `extremalSignRecovery`, and `SSGValues.call_post`.
* `callG`, `callP` : the decided bit as a function of the word (chosen by `Classical.choose` from the statement
                  above) and its `Procedure` (`SSGinP.Simulate.toProcedure`).
-/

namespace SSGValuesCall

open SSG SSG28Reply SSG28Search SSGValues SSG28Machine SSG28MachineProc SSG28MachineElim SSG28MachineBound
open SSGValuesCtx
open OAI.ExactQuantumFactoring.BitStackProgram OAI.ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.OracleSpec

/-- the driver: the public input of the sign-recovery machine for the game word inside the context word. -/
noncomputable def drvV : Procedure idW idW (fun x => driverW (unframe x).1) :=
  SSG28MachineProcD2.driverP.comp ((first idW idW).comp unframeP)

theorem eqCode_inj {a a' : ℕ × List ℚ} (h : eqCode a = eqCode a') : a = a' := by
  unfold eqCode at h
  obtain ⟨h1, h2⟩ := encodeNat_append_inj h
  exact Prod.ext h1 (flatMap_encodeRat_inj' _ _ h2)

open Classical in
/-- the reply on query words, for the context word `x`. -/
noncomputable def RV (x : Word) (q : Word) : Bool :=
  if h : ∃ a, eqCode a = q then rV (x, h.choose) else false

theorem RV_eq (x : Word) (a : ℕ × List ℚ) : RV x (eqCode a) = rV (x, a) := by
  have hex : ∃ a', eqCode a' = eqCode a := ⟨a, rfl⟩
  unfold RV
  rw [dif_pos hex, eqCode_inj hex.choose_spec]

theorem unframe_ctx (c : Ctx) : (unframe (ctxCode c)).1 = c.1 := congrArg Prod.fst (parse_ctxCode c)

/-- what the output bit of a call must satisfy. -/
def CallSpec (x : Word) (b : Bool) : Prop :=
  ∀ (n : ℕ) (G : Game n) (k : Fin n) (a j : ℕ), x = ctxCode ((encode ⟨n, G⟩).reverse, (k.val, (a, j))) →
    WellFormed G → StoppingGame G → ∀ v : Fin n → ℚ, F G v = v →
      (thr a j + Delta n ≤ v k → b = true) ∧ (v k ≤ thr a j - Delta n → b = false)

/-- **the closed machine of one call.** -/
theorem callMachine (hESR : ExtremalSignRecovery) :
    ∃ (M : BitProgram) (d : ℕ), SSG28Closed.Closed M ∧ ∀ x : Word,
      ∃ b, SSG28Closed.DecidesWithin M x ((x.length + 2) ^ d) b ∧ CallSpec x b := by
  obtain ⟨p, coef, deg, hp⟩ := hESR
  obtain ⟨hclosed, helim⟩ := eliminate p drvV repV
  obtain ⟨e0, kr, hbound⟩ := elimBound_le drvV repV
  set E := e0 + coef + 5 * deg
  refine ⟨closedProg p drvV repV, 7 + 2 * E + (E + 5) * kr, hclosed, fun x => ?_⟩
  have hb : ∀ T, T ≤ (x.length + 2) ^ E →
      elimBound drvV repV x.length T ≤ (x.length + 2) ^ (7 + 2 * E + (E + 5) * kr) :=
    fun T hT => hbound E (by omega) x.length T hT
  have hR : ∀ a, RV x (eqCode a) = rV (x, a) := RV_eq x
  have hlen : (unframe x).1.length ≤ x.length := by have := unframe_len x; omega
  cases hd : SSG28Decode.decode (unframe x).1 with
  | none =>
    have hp1 := hp 1 1 one_pos one_pos 0 (fun _ w => RV x w)
    have hdrv : driverW (unframe x).1 = priceInput (N := 1) 1 0 := by simp [driverW, hd]
    rw [← hdrv] at hp1
    have hp2 := computesWithin_mono le_rfl
      (Q := fun h out => pricePost (N := 1) 1 0 h out ∧ ∀ e ∈ h, ∃ a, e.1 = eqCode a)
      (fun h out hpp => ⟨hpp, fun e he => by
        obtain ⟨i, q, hq⟩ := hpp.1 e he; exact ⟨(i.val, List.ofFn q), hq⟩⟩) hp1
    have hc := helim x (RV x) hR _ _ hp2
    have hT : coef * (1 + (1 + 1).log2 + 1) ^ deg ≤ (x.length + 2) ^ E :=
      (tbound coef deg x.length _ (by simp; omega)).trans (pow_mono (by omega))
    obtain ⟨el, c, hrun, hle, hpc, -, hist, hpp, -⟩ := hc
    obtain ⟨b, hb'⟩ := hpp.2.1
    refine ⟨b, ⟨el, c, hrun, hle.trans (hb _ hT), hpc, hb'⟩, ?_⟩
    intro n G k a j hx
    exfalso
    rw [hx, unframe_ctx, SSGinP.decode_encode] at hd
    cases hd
  | some ng =>
    obtain ⟨n, G⟩ := ng
    have hp1 := hp (2 * n + 1) (rR n) (by omega) (by unfold rR rK; positivity) (dummy n) (fun _ w => RV x w)
    have hdrv : driverW (unframe x).1 = priceInput (rR n) (dummy n) := by simp [driverW, hd]
    rw [← hdrv] at hp1
    have hp2 := computesWithin_mono le_rfl
      (Q := fun h out => pricePost (N := 2 * n + 1) (rR n) (dummy n) h out ∧ ∀ e ∈ h, ∃ a, e.1 = eqCode a)
      (fun h out hpp => ⟨hpp, fun e he => by
        obtain ⟨i, q, hq⟩ := hpp.1 e he; exact ⟨(i.val, List.ofFn q), hq⟩⟩) hp1
    have hc := helim x (RV x) hR _ _ hp2
    have hn := decode_len hd
    have hT : coef * (2 * n + 1 + (rR n + 1).log2 + 1) ^ deg ≤ (x.length + 2) ^ E :=
      (tbound coef deg x.length _ (by have := log2_rR n; omega)).trans (pow_mono (by omega))
    obtain ⟨el, c, hrun, hle, hpc, -, hist, hpp, hans⟩ := hc
    obtain ⟨b, hb'⟩ := hpp.2.1
    refine ⟨b, ⟨el, c, hrun, hle.trans (hb _ hT), hpc, hb'⟩, ?_⟩
    intro n0 G0 k a j hx hw hs v hv
    have hd' := hd
    rw [hx, unframe_ctx, SSGinP.decode_encode] at hd'
    cases hd'
    have hans' : ∀ e ∈ hist, e.2 = [ssgReply (withStart G k) (thr a j) (rDelta n) e.1] := by
      intro e he
      rw [hans e he]
      obtain ⟨i, q, hq⟩ := hpp.1 e he
      have he1 : e.1 = eqCode (i.val, List.ofFn q) := hq
      rw [he1, hR, ← rT_spec (encode ⟨n, G⟩).reverse n G (SSGinP.decode_encode _) k a j]
      unfold rV
      rw [hx, parse_ctxCode]
    obtain ⟨b', hb2, h1, h2⟩ := call_post G hw hs v hv k (thr a j) hist _ hpp hans'
    have hbb : b = b' := by rw [hb'] at hb2; simpa using hb2
    rw [hbb]; exact ⟨h1, h2⟩

theorem callExists : ∃ (M : BitProgram) (d : ℕ), SSG28Closed.Closed M ∧ ∀ x : Word,
    ∃ b, SSG28Closed.DecidesWithin M x ((x.length + 2) ^ d) b ∧ CallSpec x b :=
  callMachine OAI.Optimization.LinearProgramming.PriceGame.extremalSignRecovery

/-- the closed machine of one call. -/
noncomputable def callM : BitProgram := callExists.choose
noncomputable def callD : ℕ := callExists.choose_spec.choose

theorem callM_spec : SSG28Closed.Closed callM ∧ ∀ x : Word,
    ∃ b, SSG28Closed.DecidesWithin callM x ((x.length + 2) ^ callD) b ∧ CallSpec x b :=
  callExists.choose_spec.choose_spec

/-- **the output bit of the call on the context word `x`.** -/
noncomputable def callG (x : Word) : Bool := (callM_spec.2 x).choose

theorem callG_decides (x : Word) : SSG28Closed.DecidesWithin callM x ((x.length + 2) ^ callD) (callG x) :=
  (callM_spec.2 x).choose_spec.1

theorem callG_spec (x : Word) : CallSpec x (callG x) := (callM_spec.2 x).choose_spec.2

/-- **one engine call as a `Procedure`** (on context words). -/
noncomputable def callP : Procedure (id : Word → Word) boolCode callG :=
  SSGinP.Simulate.toProcedure callM callM_spec.1 callD callG callG_decides

end SSGValuesCall
