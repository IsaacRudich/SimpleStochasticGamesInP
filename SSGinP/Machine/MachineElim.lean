module

public import SSGinP.Machine.Closed
public import OAI.Optimization.LinearProgramming.OracleSpec.CompilerProof
public import OAI.Optimization.LinearProgramming.OracleSpec.CompilerIO
public import OAI.Optimization.LinearProgramming.OracleSpec.BitStack
public import OAI.Computability.QuantumFactoring.BitStackProducts
public import OAI.Computability.QuantumFactoring.BitStackLists
public import OAI.Computability.QuantumFactoring.BitStackChoice

@[expose] public section

/-!
# SSGinP.Machine.MachineElim: ORACLE ELIMINATION (generic)

A `BitProgram` `p` that runs against the oracle `fun _ w => [R w]`, where on the words `eq a` the reply
`R (eq a) = r (c, a)` is computed by a BitStack `Procedure` from the pair (original input, query), and whose input
`d c` is itself computed from the original input `ex c` by a `Procedure`, is simulated by a CLOSED `BitProgram`
(no `ask` instruction) on the original input `ex c`, with polynomial overhead.

Part 1: general facts on runs, and the quoting loop.
-/

set_option linter.unusedSimpArgs false

namespace SSG28MachineElim

open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.ExactQuantumFactoring.BitStackProgram

/-! ## 1. runs of a `BitProgram` -/

section Runs
variable {p : BitProgram} {o : WordOracle}

theorem run_of_none {c d : p.Config} {n : ℕ} (h : p.Run o c n d) (hc : c.pc = none) : n = 0 ∧ d = c := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step ht _ => simp [BitProgram.tick, hc] at ht

theorem run_transcript_suffix {c d : p.Config} {n : ℕ} (h : p.Run o c n d) :
    ∃ l, d.transcript = l ++ c.transcript := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | @step c c' c'' n k ht _ ih =>
    obtain ⟨l, hl⟩ := ih
    have : ∃ l', c'.transcript = l' ++ c.transcript := by
      unfold BitProgram.tick at ht
      cases hpc : c.pc with
      | none => simp [hpc] at ht
      | some q =>
        simp only [hpc, Option.bind_eq_bind, Option.bind_some] at ht
        cases hi : p.instruction q (c.store (p.scan q)).head? <;> rw [hi] at ht <;>
          simp only [Option.some.injEq, Prod.mk.injEq, pure] at ht <;> obtain ⟨_, rfl⟩ := ht
        all_goals first | exact ⟨[], rfl⟩ | exact ⟨[_], rfl⟩
    obtain ⟨l', hl'⟩ := this
    exact ⟨l ++ l', by rw [hl, hl', List.append_assoc]⟩

/-- under a reply oracle, every transcript entry carries the oracle's answer. -/
theorem run_transcript_answers (R : Word → Bool) {c d : p.Config} {n : ℕ}
    (h : p.Run (fun _ w => [R w]) c n d) (hc : ∀ e ∈ c.transcript, e.2 = [R e.1]) :
    ∀ e ∈ d.transcript, e.2 = [R e.1] := by
  induction h with
  | refl => exact hc
  | @step c c' c'' n k ht _ ih =>
    apply ih
    unfold BitProgram.tick at ht
    cases hpc : c.pc with
    | none => simp [hpc] at ht
    | some q =>
      simp only [hpc, Option.bind_eq_bind, Option.bind_some] at ht
      cases hi : p.instruction q (c.store (p.scan q)).head? <;> rw [hi] at ht <;>
        simp only [Option.some.injEq, Prod.mk.injEq, pure] at ht <;> obtain ⟨_, rfl⟩ := ht
      all_goals first
        | exact hc
        | (intro e he; simp only [List.mem_cons] at he; rcases he with rfl | he
           · rfl
           · exact hc e he)

end Runs

/-! ## 2. the quoting loop -/

section Quote
variable {K : Type} [DecidableEq K]

/-- pop `a`; for each bit `b` push `true, b`... onto `t` (so `t` receives the quoted bits in reverse order of
popping) and push `b` back onto `x`. -/
def quoteLoop' (a t x : K) : Program K :=
  .loop a (.seq (.push t false) (.seq (.push t true) (.push x false)))
    (.seq (.push t true) (.seq (.push t true) (.push x true)))

theorem quoteLoop'_runs (a t x : K) (hat : a ≠ t) (hax : a ≠ x) (htx : t ≠ x) (s : Store K) :
    Runs (quoteLoop' a t x) s
      (Function.update (Function.update (Function.update s a []) t
        ((s a).reverse.flatMap (fun b => [true, b]) ++ s t)) x ((s a).reverse ++ s x))
      (4 * (s a).length + 1) := by
  generalize hs : s a = xs at *
  induction xs generalizing s with
  | nil =>
    have he : Function.update (Function.update (Function.update s a []) t
        (([] : List Bool).reverse.flatMap (fun b => [true, b]) ++ s t)) x (([] : List Bool).reverse ++ s x) = s := by
      funext k
      by_cases ha : k = a <;> by_cases ht : k = t <;> by_cases hx : k = x <;>
        simp_all [Function.update]
    rw [he]
    exact Runs.loop_nil hs
  | cons y ys ih =>
    let s1 := Function.update s a ys
    let s2 := Function.update s1 t (y :: s1 t)
    let s3 := Function.update s2 t (true :: s2 t)
    let s4 := Function.update s3 x (y :: s3 x)
    have h4a : s4 a = ys := by simp [s4, s3, s2, s1, hat, hax]
    have htail := ih s4 h4a
    have body : ∀ b, b = y → Runs (.seq (.push t b) (.seq (.push t true) (.push x b))) s1 s4 3 := by
      intro b hb; subst hb
      exact Runs.seq (Runs.push _ _ _) (Runs.seq (Runs.push _ _ _) (Runs.push _ _ _))
    have hr : Runs (quoteLoop' a t x) s
        (Function.update (Function.update (Function.update s4 a []) t
          (ys.reverse.flatMap (fun b => [true, b]) ++ s4 t)) x (ys.reverse ++ s4 x))
        (4 * ys.length + 1 + 3 + 1) := by
      cases y
      · exact Runs.loop_false (a:=3) (b:=4*ys.length+1) hs (body false rfl) htail
      · exact Runs.loop_true (a:=3) (b:=4*ys.length+1) hs (body true rfl) htail
    convert hr using 1
    · funext k
      by_cases ha : k = a <;> by_cases ht : k = t <;> by_cases hx : k = x <;>
        simp_all [s4, s3, s2, s1, Function.update, List.reverse_cons, List.flatMap_append, List.append_assoc]

end Quote

/-! ## 3. the closed program -/

section Build
variable (p : BitProgram) {χ α : Type} {ex : χ → Word} {eq : α → Word} {d : χ → Word} {r : χ × α → Bool}
  (drv : Procedure ex (id : Word → Word) d) (proc : Procedure (prodCode ex eq) Procedure.boolCode r)

/-- the stacks: those of `p`, four auxiliary ones (0: the buffer of `p`, 1: the copy of the input, 2: scratch,
3: the input), the reply procedure's and the driver's. -/
abbrev StT := Fin p.stackCount ⊕ (Fin 4 ⊕ (proc.K ⊕ drv.K))

noncomputable def kk : ℕ := Fintype.card (StT p drv proc)
noncomputable def es : StT p drv proc ≃ Fin (kk p drv proc) := Fintype.equivFin _

variable {p drv proc}

noncomputable def sP (s : Fin p.stackCount) : Fin (kk p drv proc) := es p drv proc (.inl s)
noncomputable def sA (j : Fin 4) : Fin (kk p drv proc) := es p drv proc (.inr (.inl j))
noncomputable def sR (k : proc.K) : Fin (kk p drv proc) := es p drv proc (.inr (.inr (.inl k)))
noncomputable def sD (k : drv.K) : Fin (kk p drv proc) := es p drv proc (.inr (.inr (.inr k)))

variable (p drv proc)

noncomputable def embR : proc.K ↪ Fin (kk p drv proc) :=
  ⟨sR, by intro a b h; simpa [sR] using h⟩
noncomputable def embD : drv.K ↪ Fin (kk p drv proc) :=
  ⟨sD, by intro a b h; simpa [sD] using h⟩

/-- the reply subroutine: query from the buffer stack, quoted input copy in front, run the procedure,
replace the answer stack by its output. -/
noncomputable def askProg : Program (Fin (kk p drv proc)) :=
  .seq (reverseMove (sA 0) (sR proc.input)) (.seq (.push (sR proc.input) false)
    (.seq (reverseMove (sA 1) (sA 2)) (.seq (quoteLoop' (sA 2) (sR proc.input) (sA 1))
      (.seq (proc.program.relabel (embR p drv proc))
        (.seq (clear (sP p.answerStack)) (reverseMove (sR proc.output) (sP p.answerStack)))))))

/-- the prelude: copy the input to stack 1, run the driver on it, put its output on `p`'s input stack. -/
noncomputable def preProg : Program (Fin (kk p drv proc)) :=
  .seq (.loop (sA 3) (.seq (.push (sA 0) false) (.push (sA 2) false)) (.seq (.push (sA 0) true) (.push (sA 2) true)))
    (.seq (reverseMove (sA 0) (sA 1)) (.seq (reverseMove (sA 2) (sD drv.input))
      (.seq (drv.program.relabel (embD p drv proc))
        (.seq (reverseMove (sD drv.output) (sA 2)) (reverseMove (sA 2) (sP p.inputStack))))))

noncomputable def askCode : BitCode (kk p drv proc) := BitCode.ofBitStack (askProg p drv proc)
noncomputable def preCode : BitCode (kk p drv proc) := BitCode.ofBitStack (preProg p drv proc)
/-- the epilogue: `p`'s buffer, in order, into the real output buffer. -/
noncomputable def haltCode : BitCode (kk p drv proc) :=
  .seq (BitCode.ofBitStack (reverseMove (sA 0) (sA 2))) (BitCode.drain (sA 2))

/-- the control states. -/
abbrev QT := Fin p.states ⊕ ((Fin p.states × Fin (askCode p drv proc).numbering.count) ⊕
  (Fin (haltCode p drv proc).numbering.count ⊕ (Fin (preCode p drv proc).numbering.count ⊕ Unit)))

noncomputable def est : QT p drv proc ≃ Fin (Fintype.card (QT p drv proc)) := Fintype.equivFin _

variable {p drv proc}

noncomputable def mainSt (q : Fin p.states) : Fin (Fintype.card (QT p drv proc)) := est p drv proc (.inl q)
noncomputable def wA (n : Fin p.states) (i : (askCode p drv proc).Node) : Fin (Fintype.card (QT p drv proc)) :=
  est p drv proc (.inr (.inl (n, (askCode p drv proc).numbering.index i)))
noncomputable def wH (i : (haltCode p drv proc).Node) : Fin (Fintype.card (QT p drv proc)) :=
  est p drv proc (.inr (.inr (.inl ((haltCode p drv proc).numbering.index i))))
noncomputable def wP (i : (preCode p drv proc).Node) : Fin (Fintype.card (QT p drv proc)) :=
  est p drv proc (.inr (.inr (.inr (.inl ((preCode p drv proc).numbering.index i)))))
noncomputable def stopSt : Fin (Fintype.card (QT p drv proc)) := est p drv proc (.inr (.inr (.inr (.inr ()))))

variable (p drv proc)

/-- `p`'s own instructions; `emit` goes to the buffer stack, `ask` and `halt` call the subroutines. -/
noncomputable def mainInstr : BitInstruction (Fin p.states) (Fin p.stackCount) →
    BitInstruction (Fin (Fintype.card (QT p drv proc))) (Fin (kk p drv proc))
  | .jump n => .jump (mainSt n)
  | .push s b n => .push (sP s) b (mainSt n)
  | .pop s n => .pop (sP s) (mainSt n)
  | .emit b n => .push (sA 0) b (mainSt n)
  | .ask n => .jump (wA n (askCode p drv proc).entry)
  | .halt => .jump (wH (haltCode p drv proc).entry)

noncomputable def lineOf : QT p drv proc → BitCode.Line (Fin (Fintype.card (QT p drv proc))) (kk p drv proc)
  | .inl q => ⟨sP (p.scan q), fun o => mainInstr p drv proc (p.instruction q o)⟩
  | .inr (.inl (n, j)) => BitCode.line (sA 0) (askCode p drv proc) (mainSt n) (wA n)
      ((askCode p drv proc).numbering.index.symm j)
  | .inr (.inr (.inl j)) => BitCode.line (sA 0) (haltCode p drv proc) stopSt wH
      ((haltCode p drv proc).numbering.index.symm j)
  | .inr (.inr (.inr (.inl j))) => BitCode.line (sA 0) (preCode p drv proc) (mainSt p.start) wP
      ((preCode p drv proc).numbering.index.symm j)
  | .inr (.inr (.inr (.inr _))) => ⟨sA 0, fun _ => .halt⟩

/-- **the closed program**. -/
noncomputable def closedProg : BitProgram where
  states := Fintype.card (QT p drv proc)
  stackCount := kk p drv proc
  start := wP (preCode p drv proc).entry
  inputStack := sA 3
  answerStack := sA 0
  scan := fun s => (lineOf p drv proc ((est p drv proc).symm s)).scan
  instruction := fun s => (lineOf p drv proc ((est p drv proc).symm s)).op

/-! ### it is closed -/

/-- a code without `ask`. -/
def NoAsk {k : ℕ} : BitCode k → Prop
  | .ask => False
  | .seq a b => NoAsk a ∧ NoAsk b
  | .cases _ a b c => NoAsk a ∧ NoAsk b ∧ NoAsk c
  | .loop _ a b => NoAsk a ∧ NoAsk b
  | _ => True

theorem noAsk_ofBitStack {k : ℕ} (c : Program (Fin k)) : NoAsk (BitCode.ofBitStack c) := by
  induction c with
  | skip => trivial
  | push => trivial
  | seq _ _ ha hb => exact ⟨ha, hb⟩
  | cases _ _ _ _ ha hb hc => exact ⟨ha, hb, hc⟩
  | loop _ _ _ ha hb => exact ⟨ha, hb⟩

theorem line_noAsk {Q : Type} {k : ℕ} (base : Fin k) (c : BitCode k) (hc : NoAsk c) :
    ∀ (dest : Q) (w : c.Node → Q) (i : c.Node) (o : Option Bool) (nx : Q),
      (BitCode.line base c dest w i).op o ≠ .ask nx := by
  induction c with
  | skip => intro _ _ _ _ _; simp [BitCode.line]
  | push => intro _ _ _ _ _; simp [BitCode.line]
  | emit => intro _ _ _ _ _; simp [BitCode.line]
  | ask => exact absurd hc id
  | seq a b iha ihb =>
    intro dest w i o nx
    rcases i with i | i
    · exact iha hc.1 _ _ i o nx
    · exact ihb hc.2 _ _ i o nx
  | cases s a b c iha ihb ihc =>
    intro dest w i o nx
    rcases i with _ | i | i | i
    · simp only [BitCode.line]; cases o with
      | none => simp
      | some bb => cases bb <;> simp
    · exact iha hc.1 _ _ i o nx
    · exact ihb hc.2.1 _ _ i o nx
    · exact ihc hc.2.2 _ _ i o nx
  | loop s a b iha ihb =>
    intro dest w i o nx
    rcases i with _ | i | i
    · simp only [BitCode.line]; cases o with
      | none => simp
      | some bb => cases bb <;> simp
    · exact iha hc.1 _ _ i o nx
    · exact ihb hc.2 _ _ i o nx

theorem closedProg_closed : SSG28Closed.Closed (closedProg p drv proc) := by
  intro s o nx
  simp only [closedProg]
  generalize (est p drv proc).symm s = u
  rcases u with q | ⟨n, j⟩ | j | j | _
  · simp only [lineOf]; cases p.instruction q o <;> simp [mainInstr]
  · exact line_noAsk _ _ (noAsk_ofBitStack _) _ _ _ o nx
  · exact line_noAsk _ _ (by simp [haltCode, BitCode.drain, NoAsk, noAsk_ofBitStack]) _ _ _ o nx
  · exact line_noAsk _ _ (noAsk_ofBitStack _) _ _ _ o nx
  · simp [lineOf]

end Build

/-! ## 4. the store view -/

section Store
variable {p : BitProgram} {χ α : Type} {ex : χ → Word} {eq : α → Word} {d : χ → Word} {r : χ × α → Bool}
  {drv : Procedure ex (id : Word → Word) d} {proc : Procedure (prodCode ex eq) Procedure.boolCode r}

/-- a store of the closed program, given on the stack type. -/
noncomputable def mkS (f : StT p drv proc → Word) : Store (Fin (kk p drv proc)) :=
  fun t => f ((es p drv proc).symm t)

@[simp] theorem mkS_es (f : StT p drv proc → Word) (u : StT p drv proc) : mkS f (es p drv proc u) = f u := by
  simp [mkS]

theorem update_mkS (f : StT p drv proc → Word) (u : StT p drv proc) (v : Word) :
    Function.update (mkS f) (es p drv proc u) v = mkS (Function.update f u v) := by
  funext t
  obtain ⟨u', rfl⟩ := (es p drv proc).surjective t
  simp only [mkS_es, Function.update_apply, Equiv.apply_eq_iff_eq]

/-- the simulated store: `p`'s stacks, `p`'s buffer (reversed, on stack 0), the input copy (stack 1). -/
def simF (st : Fin p.stackCount → Word) (b x : Word) : StT p drv proc → Word
  | .inl s => st s
  | .inr (.inl j) => if j = 0 then b else if j = 1 then x else []
  | .inr (.inr _) => []

def withR (f : StT p drv proc → Word) (s : proc.K → Word) : StT p drv proc → Word
  | .inr (.inr (.inl k)) => s k
  | u => f u

def withD (f : StT p drv proc → Word) (s : drv.K → Word) : StT p drv proc → Word
  | .inr (.inr (.inr k)) => s k
  | u => f u

theorem overlay_R (f : StT p drv proc → Word) (s : Store proc.K) :
    overlay (embR p drv proc) (mkS f) s = mkS (withR f s) := by
  funext t
  obtain ⟨u, rfl⟩ := (es p drv proc).surjective t
  rcases u with u | u | u | u
  · rw [overlay_outside]; · simp [withR]
    intro k h; exact absurd ((es p drv proc).injective h) (by simp)
  · rw [overlay_outside]; · simp [withR]
    intro k h; exact absurd ((es p drv proc).injective h) (by simp)
  · refine (overlay_at (embR p drv proc) (mkS f) s u).trans ?_; simp [withR]
  · rw [overlay_outside]; · simp [withR]
    intro k h; exact absurd ((es p drv proc).injective h) (by simp)

theorem overlay_D (f : StT p drv proc → Word) (s : Store drv.K) :
    overlay (embD p drv proc) (mkS f) s = mkS (withD f s) := by
  funext t
  obtain ⟨u, rfl⟩ := (es p drv proc).surjective t
  rcases u with u | u | u | u
  · rw [overlay_outside]; · simp [withD]
    intro k h; exact absurd ((es p drv proc).injective h) (by simp)
  · rw [overlay_outside]; · simp [withD]
    intro k h; exact absurd ((es p drv proc).injective h) (by simp)
  · rw [overlay_outside]; · simp [withD]
    intro k h; exact absurd ((es p drv proc).injective h) (by simp)
  · refine (overlay_at (embD p drv proc) (mkS f) s u).trans ?_; simp [withD]

variable (drv proc)

theorem rm_mkS (u v : StT p drv proc) (huv : u ≠ v) (F : StT p drv proc → Word) :
    Runs (reverseMove (es p drv proc u) (es p drv proc v)) (mkS F)
      (mkS (Function.update (Function.update F u []) v ((F u).reverse ++ F v))) (2 * (F u).length + 1) := by
  have h := reverseMove_runs (es p drv proc u) (es p drv proc v) (by simpa using huv) (mkS F)
  simpa only [mkS_es, update_mkS] using h

theorem push_mkS (u : StT p drv proc) (bb : Bool) (F : StT p drv proc → Word) :
    Runs (.push (es p drv proc u) bb) (mkS F) (mkS (Function.update F u (bb :: F u))) 1 := by
  have h := Runs.push (mkS F) (es p drv proc u) bb
  simpa only [mkS_es, update_mkS] using h

theorem clear_mkS (u : StT p drv proc) (F : StT p drv proc → Word) :
    Runs (clear (es p drv proc u)) (mkS F) (mkS (Function.update F u [])) (2 * (F u).length + 1) := by
  have h := clear_runs (es p drv proc u) (mkS F)
  simpa only [mkS_es, update_mkS] using h

theorem quote_mkS (a t x : StT p drv proc) (hat : a ≠ t) (hax : a ≠ x) (htx : t ≠ x) (F : StT p drv proc → Word) :
    Runs (quoteLoop' (es p drv proc a) (es p drv proc t) (es p drv proc x)) (mkS F)
      (mkS (Function.update (Function.update (Function.update F a []) t
        ((F a).reverse.flatMap (fun b => [true, b]) ++ F t)) x ((F a).reverse ++ F x)))
      (4 * (F a).length + 1) := by
  have h := quoteLoop'_runs (es p drv proc a) (es p drv proc t) (es p drv proc x)
    (by simpa using hat) (by simpa using hax) (by simpa using htx) (mkS F)
  simpa only [mkS_es, update_mkS] using h

theorem dup_mkS (a b t : StT p drv proc) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (F : StT p drv proc → Word) :
    Runs (.loop (es p drv proc a) (.seq (.push (es p drv proc b) false) (.push (es p drv proc t) false))
      (.seq (.push (es p drv proc b) true) (.push (es p drv proc t) true))) (mkS F)
      (mkS (Function.update (Function.update (Function.update F a []) b ((F a).reverse ++ F b))
        t ((F a).reverse ++ F t))) (3 * (F a).length + 1) := by
  have h := duplicateReverse_loop_runs (es p drv proc a) (es p drv proc b) (es p drv proc t)
    (by simpa using hab) (by simpa using hat) (by simpa using hbt) (mkS F)
  simpa only [mkS_es, update_mkS] using h

theorem procR_mkS (c0 : χ) (a : α) (F : StT p drv proc → Word)
    (hF : ∀ k, F (.inr (.inr (.inl k))) = singletonStore proc.input (prodCode ex eq (c0, a)) k) :
    ∃ cp, cp ≤ proc.bound.eval (prodCode ex eq (c0, a)).length ∧
      Runs (proc.program.relabel (embR p drv proc)) (mkS F)
        (mkS (withR F (singletonStore proc.output [r (c0, a)]))) cp := by
  obtain ⟨cp, hcp, hp⟩ := proc.runs (c0, a)
  have h := hp.relabel (embR p drv proc) (mkS F)
  rw [overlay_R, overlay_R] at h
  have e : withR F (singletonStore proc.input (prodCode ex eq (c0, a))) = F := by
    funext u; rcases u with u | u | u | u <;> simp [withR, hF]
  rw [e] at h
  exact ⟨cp, hcp, h⟩

theorem procD_mkS (c0 : χ) (F : StT p drv proc → Word)
    (hF : ∀ k, F (.inr (.inr (.inr k))) = singletonStore drv.input (ex c0) k) :
    ∃ cp, cp ≤ drv.bound.eval (ex c0).length ∧
      Runs (drv.program.relabel (embD p drv proc)) (mkS F)
        (mkS (withD F (singletonStore drv.output (d c0)))) cp := by
  obtain ⟨cp, hcp, hp⟩ := drv.runs c0
  have h := hp.relabel (embD p drv proc) (mkS F)
  rw [overlay_D, overlay_D] at h
  have e : withD F (singletonStore drv.input (ex c0)) = F := by
    funext u; rcases u with u | u | u | u <;> simp [withD, hF]
  rw [e] at h
  exact ⟨cp, hcp, h⟩

end Store

/-! ## 5. the three subroutines on simulated stores -/

section Steps
variable {p : BitProgram} {χ α : Type} {ex : χ → Word} {eq : α → Word} {d : χ → Word} {r : χ × α → Bool}
  {drv : Procedure ex (id : Word → Word) d} {proc : Procedure (prodCode ex eq) Procedure.boolCode r}

/-- the reply subroutine replaces the answer stack by `[r (c0, a)]` and empties `p`'s buffer. -/
theorem ask_runs (st : Fin p.stackCount → Word) (b x : Word) (c0 : χ) (a : α) (hx : x = ex c0)
    (hb : b.reverse = eq a) :
    ∃ m, m ≤ 2 * b.length + 6 * x.length + 2 * (st p.answerStack).length + 10 +
        proc.bound.eval (2 * x.length + b.length + 1) ∧
      Runs (askProg p drv proc) (mkS (simF (drv := drv) (proc := proc) st b x))
        (mkS (simF (drv := drv) (proc := proc) (Function.update st p.answerStack [r (c0, a)]) [] x)) m := by
  classical
  let B : StT p drv proc := .inr (.inl 0)
  let X : StT p drv proc := .inr (.inl 1)
  let Tm : StT p drv proc := .inr (.inl 2)
  let Rin : StT p drv proc := .inr (.inr (.inl proc.input))
  let Rout : StT p drv proc := .inr (.inr (.inl proc.output))
  let PA : StT p drv proc := .inl p.answerStack
  set F0 := simF (drv := drv) (proc := proc) st b x with hF0
  set F1 := Function.update (Function.update F0 B []) Rin ((F0 B).reverse ++ F0 Rin) with hF1
  set F2 := Function.update F1 Rin (false :: F1 Rin) with hF2
  set F3 := Function.update (Function.update F2 X []) Tm ((F2 X).reverse ++ F2 Tm) with hF3
  set F4 := Function.update (Function.update (Function.update F3 Tm []) Rin
    ((F3 Tm).reverse.flatMap (fun b => [true, b]) ++ F3 Rin)) X ((F3 Tm).reverse ++ F3 X) with hF4
  have h1 := rm_mkS drv proc B Rin (by simp [B, Rin]) F0
  have h2 := push_mkS drv proc Rin false F1
  have h3 := rm_mkS drv proc X Tm (by simp [X, Tm]) F2
  have h4 := quote_mkS drv proc Tm Rin X (by simp [Tm, Rin]) (by simp [Tm, X]) (by simp [Rin, X]) F3
  obtain ⟨cp, hcp, h5⟩ := procR_mkS drv proc c0 a F4 (by
    intro k
    by_cases hk : k = proc.input
    · subst hk
      simp [F4, F3, F2, F1, F0, simF, Function.update_apply, B, X, Tm, Rin, singletonStore, prodCode,
        OAI.ExactQuantumFactoring.BitStackProgram.pairBits, OAI.ExactQuantumFactoring.BitStackProgram.quoteBits, hx, ← hb]
    · simp [F4, F3, F2, F1, F0, simF, Function.update_apply, B, X, Tm, Rin, singletonStore, hk])
  set F5 := withR F4 (singletonStore proc.output [r (c0, a)]) with hF5
  have h6 := clear_mkS drv proc PA F5
  have h7 := rm_mkS drv proc Rout PA (by simp [Rout, PA]) (Function.update F5 PA [])
  have hall := Runs.seq h1 (Runs.seq h2 (Runs.seq h3 (Runs.seq h4 (Runs.seq h5 (Runs.seq h6 h7)))))
  have efin : Function.update (Function.update (Function.update F5 PA []) Rout [])
      PA (((Function.update F5 PA []) Rout).reverse ++ (Function.update F5 PA []) PA) =
      simF (drv := drv) (proc := proc) (Function.update st p.answerStack [r (c0, a)]) [] x := by
    funext u
    rcases u with u | u | u | u
    · by_cases hu : u = p.answerStack
      · subst hu; simp [F5, withR, PA, Rout, simF, singletonStore]
      · simp [F5, withR, PA, Rout, simF, hu, F4, F3, F2, F1, F0, Function.update_apply, B, X, Tm, Rin]
    · fin_cases u <;> simp [F5, withR, PA, Rout, simF, F4, F3, F2, F1, F0, Function.update_apply, B, X, Tm, Rin]
    · by_cases ho : u = proc.output
      · subst ho; simp [F5, withR, PA, Rout, simF, singletonStore]
      · simp [F5, withR, PA, Rout, simF, singletonStore, ho, Function.update_apply]
    · simp [F5, withR, PA, Rout, simF, F4, F3, F2, F1, F0, Function.update_apply, B, X, Tm, Rin]
  rw [efin] at hall
  refine ⟨_, ?_, hall⟩
  have l5 : (Function.update F5 PA []) Rout = [r (c0, a)] := by simp [F5, withR, PA, Rout, singletonStore]
  have l6 : F5 PA = st p.answerStack := by
    simp [F5, withR, PA, F4, F3, F2, F1, F0, Function.update_apply, B, X, Tm, Rin, simF]
  have l3 : F3 Tm = x.reverse := by simp [F3, F2, F1, F0, Function.update_apply, B, X, Tm, Rin, simF]
  have l2 : F2 X = x := by simp [F2, F1, F0, Function.update_apply, B, X, Rin, simF]
  have l0 : F0 B = b := by simp [F0, B, simF]
  have hlen : (prodCode ex eq (c0, a)).length = 2 * x.length + b.length + 1 := by
    simp [prodCode, OAI.ExactQuantumFactoring.BitStackProgram.pairBits_length, hx, ← hb]
  rw [hlen] at hcp
  rw [l5, l6, l3, l2, l0, List.length_reverse]
  simp only [List.length_cons, List.length_nil]
  omega

/-- the prelude: from the initial store (input on stack 3) to the simulated initial store of `p` on `d c0`. -/
theorem pre_runs (c0 : χ) (x : Word) (hx : x = ex c0) :
    ∃ m, m ≤ 7 * x.length + 4 * (d c0).length + 5 + drv.bound.eval x.length ∧
      Runs (preProg p drv proc) (mkS (fun u => if u = .inr (.inl 3) then x else []))
        (mkS (simF (drv := drv) (proc := proc) (fun s => if s = p.inputStack then d c0 else []) [] x)) m := by
  classical
  let B : StT p drv proc := .inr (.inl 0)
  let X : StT p drv proc := .inr (.inl 1)
  let Tm : StT p drv proc := .inr (.inl 2)
  let I0 : StT p drv proc := .inr (.inl 3)
  let Din : StT p drv proc := .inr (.inr (.inr drv.input))
  let Dout : StT p drv proc := .inr (.inr (.inr drv.output))
  let PI : StT p drv proc := .inl p.inputStack
  set G0 : StT p drv proc → Word := fun u => if u = .inr (.inl 3) then x else [] with hG0
  set G1 := Function.update (Function.update (Function.update G0 I0 []) B ((G0 I0).reverse ++ G0 B))
        Tm ((G0 I0).reverse ++ G0 Tm) with hG1
  set G2 := Function.update (Function.update G1 B []) X ((G1 B).reverse ++ G1 X) with hG2
  set G3 := Function.update (Function.update G2 Tm []) Din ((G2 Tm).reverse ++ G2 Din) with hG3
  have h1 := dup_mkS drv proc I0 B Tm (by simp [I0, B]) (by simp [I0, Tm]) (by simp [B, Tm]) G0
  have h2 := rm_mkS drv proc B X (by simp [B, X]) G1
  have h3 := rm_mkS drv proc Tm Din (by simp [Tm, Din]) G2
  obtain ⟨cd, hcd, h4⟩ := procD_mkS drv proc c0 G3 (by
    intro k
    by_cases hk : k = drv.input
    · subst hk; simp [G3, G2, G1, G0, Function.update_apply, B, X, Tm, I0, Din, singletonStore, hx]
    · simp [G3, G2, G1, G0, Function.update_apply, B, X, Tm, I0, Din, singletonStore, hk])
  set G4 := withD G3 (singletonStore drv.output (d c0)) with hG4
  have h5 := rm_mkS drv proc Dout Tm (by simp [Dout, Tm]) G4
  have h6 := rm_mkS drv proc Tm PI (by simp [Tm, PI])
    (Function.update (Function.update G4 Dout []) Tm ((G4 Dout).reverse ++ G4 Tm))
  have hall := Runs.seq h1 (Runs.seq h2 (Runs.seq h3 (Runs.seq h4 (Runs.seq h5 h6))))
  have efin : Function.update (Function.update (Function.update (Function.update G4 Dout []) Tm
      ((G4 Dout).reverse ++ G4 Tm)) Tm []) PI
      ((Function.update (Function.update G4 Dout []) Tm ((G4 Dout).reverse ++ G4 Tm) Tm).reverse ++
        Function.update (Function.update G4 Dout []) Tm ((G4 Dout).reverse ++ G4 Tm) PI) =
      simF (drv := drv) (proc := proc) (fun s => if s = p.inputStack then d c0 else []) [] x := by
    funext u
    rcases u with u | u | u | u
    · by_cases hu : u = p.inputStack
      · subst hu; simp [G4, withD, PI, Dout, Tm, simF, singletonStore, G3, G2, G1, G0, Function.update_apply, Din, B, X, I0]
      · simp [G4, withD, PI, Dout, Tm, simF, hu, G3, G2, G1, G0, Function.update_apply, B, X, I0, Din]
    · fin_cases u <;> simp [G4, withD, PI, Dout, Tm, simF, G3, G2, G1, G0, Function.update_apply, B, X, I0, Din]
    · simp [G4, withD, PI, Dout, Tm, simF, G3, G2, G1, G0, Function.update_apply, B, X, I0, Din]
    · by_cases ho : u = drv.output
      · subst ho; simp [G4, withD, PI, Dout, Tm, simF, singletonStore]
      · by_cases hi : u = drv.input
        · subst hi; simp [G4, withD, PI, Dout, Tm, simF, singletonStore, ho, Function.update_apply]
        · simp [G4, withD, PI, Dout, Tm, simF, singletonStore, ho, hi, G3, G2, G1, G0, Function.update_apply, B, X, I0, Din]
  rw [efin] at hall
  refine ⟨_, ?_, hall⟩
  have l0 : G0 I0 = x := by simp [G0, I0]
  have l1 : G1 B = x.reverse := by simp [G1, G0, Function.update_apply, B, I0, Tm]
  have l2 : G2 Tm = x.reverse := by simp [G2, G1, G0, Function.update_apply, B, I0, Tm, X]
  have l4 : G4 Dout = d c0 := by simp [G4, withD, Dout, singletonStore]
  have l5 : G4 Tm = [] := by simp [G4, withD, G3, G2, G1, G0, Function.update_apply, B, X, I0, Tm, Din]
  rw [← hx] at hcd
  simp only [Function.update_self, l0, l1, l2, l4, l5, List.length_reverse, List.length_append, List.length_nil]
  omega

/-- the epilogue writes `p`'s buffer (stack 0, reversed) into the output buffer. -/
theorem halt_exec (st : Fin p.stackCount → Word) (b x : Word) (o : WordOracle) :
    ∃ f, BitCode.Executes (sA 0) o (haltCode p drv proc)
      ⟨mkS (simF (drv := drv) (proc := proc) st b x), [], []⟩ ⟨f, b, []⟩ (4 * b.length + 2) := by
  classical
  have h1 := BitCode.ofBitStack_exec (rm_mkS drv proc (.inr (.inl 0)) (.inr (.inl 2)) (by simp)
    (simF (drv := drv) (proc := proc) st b x)) (sA 0) o [] []
  have h2 := BitCode.drain_exec (sA 2 : Fin (kk p drv proc)) (sA 0) o
    ⟨mkS (Function.update (Function.update (simF (drv := drv) (proc := proc) st b x) (.inr (.inl 0)) [])
      (.inr (.inl 2)) ((simF (drv := drv) (proc := proc) st b x (.inr (.inl 0))).reverse ++
        simF (drv := drv) (proc := proc) st b x (.inr (.inl 2)))), [], []⟩
  have h := BitCode.Executes.seq h1 h2
  have hb : (mkS (Function.update (Function.update (simF (drv := drv) (proc := proc) st b x) (.inr (.inl 0)) [])
      (.inr (.inl 2)) ((simF (drv := drv) (proc := proc) st b x (.inr (.inl 0))).reverse ++
        simF (drv := drv) (proc := proc) st b x (.inr (.inl 2))))) (sA 2) = b.reverse := by
    simp [sA, simF]
  simp only [BitCode.Memory.drained, hb, List.reverse_reverse, List.append_nil, List.length_reverse] at h
  have e : 2 * (simF (drv := drv) (proc := proc) st b x (.inr (.inl 0))).length + 1 + (2 * b.length + 1) =
      4 * b.length + 2 := by simp [simF]; omega
  rw [e] at h
  exact ⟨_, h⟩

end Steps

/-! ## 6. the simulation -/

section Sim
variable {p : BitProgram} {χ α : Type} {ex : χ → Word} {eq : α → Word} {d : χ → Word} {r : χ × α → Bool}
  {drv : Procedure ex (id : Word → Word) d} {proc : Procedure (prodCode ex eq) Procedure.boolCode r}

theorem tick_place (P : BitProgram) (o : WordOracle) (s : Fin P.states) (m : BitCode.Memory P.stackCount) :
    P.tick o (BitCode.place P s m) = some (BitCode.perform P o m (P.instruction s (m.store (P.scan s)).head?)) := by
  unfold BitProgram.tick BitCode.place
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases P.instruction s (m.store (P.scan s)).head? <;> rfl

theorem config_eq_place (P : BitProgram) (c : P.Config) (q : Fin P.states) (hq : c.pc = some q) :
    c = BitCode.place P q ⟨c.store, c.bufferRev, c.transcript⟩ := by
  cases c; simp_all [BitCode.place]

theorem rep_ask (n : Fin p.states) :
    BitCode.Represents (closedProg p drv proc) (sA 0) (askCode p drv proc) (mainSt n) (wA n) := by
  intro i
  have e := (askCode p drv proc).numbering.index.symm_apply_apply i
  simp only [closedProg, wA, lineOf, Equiv.symm_apply_apply]
  rw [e]; exact ⟨rfl, rfl⟩

theorem rep_halt :
    BitCode.Represents (closedProg p drv proc) (sA 0) (haltCode p drv proc) stopSt wH := by
  intro i
  have e := (haltCode p drv proc).numbering.index.symm_apply_apply i
  simp only [closedProg, wH, lineOf, Equiv.symm_apply_apply]
  rw [e]; exact ⟨rfl, rfl⟩

theorem rep_pre :
    BitCode.Represents (closedProg p drv proc) (sA 0) (preCode p drv proc) (mainSt p.start) wP := by
  intro i
  have e := (preCode p drv proc).numbering.index.symm_apply_apply i
  simp only [closedProg, wP, lineOf, Equiv.symm_apply_apply]
  rw [e]; exact ⟨rfl, rfl⟩

theorem simF_update_inl (st : Fin p.stackCount → Word) (b x : Word) (s : Fin p.stackCount) (v : Word) :
    Function.update (simF (drv := drv) (proc := proc) st b x) (.inl s) v =
      simF (drv := drv) (proc := proc) (Function.update st s v) b x := by
  funext u; rcases u with u | u | u <;> simp [simF, Function.update_apply]

theorem simF_update_B (st : Fin p.stackCount → Word) (b x : Word) (v : Word) :
    Function.update (simF (drv := drv) (proc := proc) st b x) (.inr (.inl 0)) v =
      simF (drv := drv) (proc := proc) st v x := by
  funext u; rcases u with u | u | u
  · simp [simF]
  · fin_cases u <;> simp [simF]
  · simp [simF]

/-- the simulated configuration. -/
noncomputable def simC (c : p.Config) (x : Word) (q : Fin p.states) : (closedProg p drv proc).Config :=
  BitCode.place (closedProg p drv proc) (mainSt q) ⟨mkS (simF (drv := drv) (proc := proc) c.store c.bufferRev x), [], []⟩

theorem tick_simC (c : p.Config) (x : Word) (q : Fin p.states) (o : WordOracle) :
    (closedProg p drv proc).tick o (simC c x q) =
      some (BitCode.perform (closedProg p drv proc) o
        ⟨mkS (simF (drv := drv) (proc := proc) c.store c.bufferRev x), [], []⟩
        (mainInstr p drv proc (p.instruction q (c.store (p.scan q)).head?))) := by
  rw [simC]
  refine (tick_place (closedProg p drv proc) o (mainSt q) _).trans ?_
  simp [closedProg, mainSt, lineOf, sP, simF]

/-- per-step cost bound of the simulation. -/
noncomputable def stepB (proc : Procedure (prodCode ex eq) Procedure.boolCode r) (L xl : ℕ) : ℕ :=
  4 * L + 6 * xl + 11 + proc.bound.eval (2 * xl + L + 1)

theorem sim_run (c0 : χ) (x : Word) (hx : x = ex c0) (R : Word → Bool) (hR : ∀ a, R (eq a) = r (c0, a))
    (L : ℕ) {c dd : p.Config} {n : ℕ} (h : p.Run (fun _ w => [R w]) c n dd) :
    ∀ q, c.pc = some q → dd.pc = none → (∀ e ∈ dd.transcript, ∃ a, e.1 = eq a) →
      (∀ s, (c.store s).length + n ≤ L) → c.bufferRev.length + n ≤ L →
      ∃ m cf, (closedProg p drv proc).Run SSG28Closed.noOracle (simC c x q) m cf ∧ cf.pc = none ∧
        cf.bufferRev = dd.bufferRev ∧ cf.transcript = [] ∧ m ≤ n * stepB proc L x.length + (4 * L + 4) := by
  induction h with
  | refl c =>
    intro q hq hdd; rw [hq] at hdd; exact absurd hdd (by simp)
  | @step c c' c'' n k ht hrest ih =>
    intro q hq hdd htr hL hB
    have hS1 : 1 ≤ stepB proc L x.length := by unfold stepB; omega
    rw [config_eq_place p c q hq, tick_place] at ht
    simp only [Option.some.injEq] at ht
    have hhead : (BitCode.Memory.store ⟨c.store, c.bufferRev, c.transcript⟩ (p.scan q)).head? =
      (c.store (p.scan q)).head? := rfl
    rw [hhead] at ht
    have htk := tick_simC (drv := drv) (proc := proc) c x q SSG28Closed.noOracle
    generalize p.instruction q (c.store (p.scan q)).head? = I at ht htk
    cases I with
    | jump n' =>
      simp only [BitCode.perform, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      obtain ⟨m', cf, hr, h1, h2, h3, hm⟩ := ih n' rfl hdd htr (fun s => by have := hL s; simp [BitCode.place]; omega)
        (by simp [BitCode.place]; omega)
      refine ⟨1 + m', cf, BitProgram.Run.step (by rw [htk]; rfl) hr, h1, h2, h3, ?_⟩
      rw [Nat.add_mul]; omega
    | push s bb n' =>
      simp only [BitCode.perform, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      obtain ⟨m', cf, hr, h1, h2, h3, hm⟩ := ih n' rfl hdd htr
        (fun s' => by
          have := hL s'; have := hL s
          by_cases hs : s' = s
          · subst hs; simp [BitCode.place, BitCode.Memory.push]; omega
          · simp [BitCode.place, BitCode.Memory.push, Function.update_apply, hs]; omega)
        (by simp [BitCode.place, BitCode.Memory.push]; omega)
      refine ⟨1 + m', cf, BitProgram.Run.step (by
        rw [htk]; simp only [mainInstr, BitCode.perform, simC, BitCode.Memory.push, BitCode.place, sP]
        erw [mkS_es, update_mkS, simF_update_inl]; rfl) hr, h1, h2, h3, ?_⟩
      rw [Nat.add_mul]; omega
    | pop s n' =>
      simp only [BitCode.perform, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      obtain ⟨m', cf, hr, h1, h2, h3, hm⟩ := ih n' rfl hdd htr
        (fun s' => by
          have := hL s'
          by_cases hs : s' = s
          · subst hs; simp [BitCode.place, BitCode.Memory.pop]; omega
          · simp [BitCode.place, BitCode.Memory.pop, Function.update_apply, hs]; omega)
        (by simp [BitCode.place, BitCode.Memory.pop]; omega)
      refine ⟨1 + m', cf, BitProgram.Run.step (by
        rw [htk]; simp only [mainInstr, BitCode.perform, simC, BitCode.Memory.pop, BitCode.place, sP]
        erw [mkS_es, update_mkS, simF_update_inl]; rfl) hr, h1, h2, h3, ?_⟩
      rw [Nat.add_mul]; omega
    | emit bb n' =>
      simp only [BitCode.perform, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      obtain ⟨m', cf, hr, h1, h2, h3, hm⟩ := ih n' rfl hdd htr
        (fun s' => by have := hL s'; simp [BitCode.place, BitCode.Memory.emit]; omega)
        (by simp [BitCode.place, BitCode.Memory.emit]; omega)
      refine ⟨1 + m', cf, BitProgram.Run.step (by
        rw [htk]; simp only [mainInstr, BitCode.perform, simC, BitCode.Memory.push, BitCode.place, sA]
        erw [mkS_es, update_mkS, simF_update_B]; simp [simF, BitCode.Memory.emit, BitCode.place]) hr, h1, h2, h3, ?_⟩
      rw [Nat.add_mul]; omega
    | ask n' =>
      simp only [BitCode.perform, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      -- the query is a word `eq a`
      set w := c.bufferRev.reverse with hw
      obtain ⟨l, hl⟩ := run_transcript_suffix hrest
      have hmem : (w, [R w]) ∈ c''.transcript := by
        rw [hl]; simp [BitCode.place, BitCode.Memory.receive, hw]
      obtain ⟨a, ha⟩ := htr _ hmem
      have hb : c.bufferRev.reverse = eq a := ha
      obtain ⟨ma, hma, hra⟩ := ask_runs (drv := drv) (proc := proc) c.store c.bufferRev x c0 a hx hb
      have hex := BitCode.ofBitStack_exec hra (sA 0) SSG28Closed.noOracle [] []
      have hrun := BitCode.Executes.toMachine (p := closedProg p drv proc) hex (sA 0) (mainSt n') (wA n') (rep_ask n')
      have hRw : R w = r (c0, a) := by rw [show w = eq a from hb]; exact hR a
      obtain ⟨m', cf, hr, h1, h2, h3, hm⟩ := ih n' rfl hdd htr
        (fun s' => by
          have := hL s'
          by_cases hs : s' = p.answerStack
          · subst hs; simp [BitCode.place, BitCode.Memory.receive]; omega
          · simp [BitCode.place, BitCode.Memory.receive, Function.update_apply, hs]; omega)
        (by simp [BitCode.place, BitCode.Memory.receive]; omega)
      have hr' : (closedProg p drv proc).Run SSG28Closed.noOracle
          (simC (BitCode.place p n' (BitCode.Memory.receive ⟨c.store, c.bufferRev, c.transcript⟩ p.answerStack [R w])) x n')
          m' cf := hr
      refine ⟨1 + (ma + m'), cf, BitProgram.Run.step (by rw [htk]; rfl) ((hrun.append ?_)), h1, h2, h3, ?_⟩
      · convert hr' using 2
        simp [simC, BitCode.place, BitCode.Memory.receive, hRw]
      · have hbL : c.bufferRev.length ≤ L := by omega
        have hAL : (c.store p.answerStack).length ≤ L := by have := hL p.answerStack; omega
        have hmono := Procedure.eval_nat_mono proc.bound
          (show 2 * x.length + c.bufferRev.length + 1 ≤ 2 * x.length + L + 1 by omega)
        dsimp only at hmono
        have hk : 1 ≤ 1 + w.length + [R w].length := by omega
        have : ma + 1 ≤ stepB proc L x.length := by unfold stepB; omega
        have hkS : stepB proc L x.length ≤ (1 + w.length + [R w].length) * stepB proc L x.length :=
          Nat.le_mul_of_pos_left _ (by omega)
        have e2 := Nat.add_mul (1 + w.length + [R w].length) n (stepB proc L x.length)
        simp only [List.length_cons, List.length_nil] at e2 hkS ⊢
        omega
    | halt =>
      simp only [BitCode.perform, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      obtain ⟨hn0, rfl⟩ := run_of_none hrest rfl
      subst hn0
      obtain ⟨f, hex⟩ := halt_exec (drv := drv) (proc := proc) c.store c.bufferRev x SSG28Closed.noOracle
      have hrun := BitCode.Executes.toMachine (p := closedProg p drv proc) hex (sA 0) stopSt wH rep_halt
      have hstop : (closedProg p drv proc).tick SSG28Closed.noOracle
          (BitCode.place (closedProg p drv proc) (show Fin (closedProg p drv proc).states from stopSt) ⟨f, c.bufferRev, []⟩) =
          some (1, ⟨none, f, c.bufferRev, []⟩) := by
        refine (tick_place (closedProg p drv proc) _ _ _).trans ?_
        simp [closedProg, stopSt, lineOf, BitCode.perform]
      refine ⟨1 + ((4 * c.bufferRev.length + 2) + 1), ⟨none, f, c.bufferRev, []⟩,
        BitProgram.Run.step (by rw [htk]; rfl) (hrun.append (BitProgram.Run.single hstop)), rfl, rfl, rfl, ?_⟩
      have : c.bufferRev.length ≤ L := by omega
      omega

/-- the time bound of the closed program, in the input length `xl` and the time bound `T` of `p`. -/
noncomputable def elimBound (drv : Procedure ex (id : Word → Word) d) (proc : Procedure (prodCode ex eq) Procedure.boolCode r)
    (xl T : ℕ) : ℕ :=
  (7 * xl + 4 * (xl + drv.bound.eval xl) + 5 + drv.bound.eval xl) +
    T * stepB proc (xl + drv.bound.eval xl + T) xl + (4 * (xl + drv.bound.eval xl + T) + 4)

theorem stepB_mono {L L' : ℕ} (h : L ≤ L') (xl : ℕ) : stepB proc L xl ≤ stepB proc L' xl := by
  unfold stepB
  have := Procedure.eval_nat_mono proc.bound (show 2 * xl + L + 1 ≤ 2 * xl + L' + 1 by omega)
  dsimp only at this
  omega

end Sim

/-! ## 7. S1: the oracle elimination theorem -/

section Main
variable {χ α : Type} {ex : χ → Word} {eq : α → Word} {d : χ → Word} {r : χ × α → Bool}

/-- **S1, oracle elimination.** `p` runs on the driver's output `d c0` against the oracle `fun _ w => [R w]`,
whose reply on the words `eq a` is `r (c0, a)` (computed by the procedure `proc` from the original input and the
query), and asks only such words. Then the closed program `closedProg p drv proc` (no `ask` instruction) on the
original input `ex c0` halts within `elimBound` steps with the same output and an empty transcript, and `p`'s
transcript (which satisfies `post`) answered every query `w` by `[R w]`. -/
theorem eliminate (p : BitProgram) (drv : Procedure ex (id : Word → Word) d)
    (proc : Procedure (prodCode ex eq) Procedure.boolCode r) :
    SSG28Closed.Closed (closedProg p drv proc) ∧
    ∀ (c0 : χ) (R : Word → Bool), (∀ a, R (eq a) = r (c0, a)) →
      ∀ (T : ℕ) (post : Transcript → Word → Prop),
        p.ComputesWithin (fun _ w => [R w]) (d c0) T (fun h out => post h out ∧ ∀ e ∈ h, ∃ a, e.1 = eq a) →
        (closedProg p drv proc).ComputesWithin SSG28Closed.noOracle (ex c0) (elimBound drv proc (ex c0).length T)
          (fun h out => h = [] ∧ ∃ hist, post hist out ∧ ∀ e ∈ hist, e.2 = [R e.1]) := by
  refine ⟨closedProg_closed p drv proc, ?_⟩
  intro c0 R hR T post hp
  obtain ⟨el, cf, hrun, hel, hpc, hpost, hq⟩ := hp
  set x := ex c0 with hx
  -- the prelude
  obtain ⟨mp, hmp, hpre⟩ := pre_runs (p := p) (drv := drv) (proc := proc) c0 x hx
  have hpre' := BitCode.Executes.toMachine (p := closedProg p drv proc)
    (BitCode.ofBitStack_exec hpre (sA 0) SSG28Closed.noOracle [] []) (sA 0) (mainSt p.start) wP rep_pre
  have hinit : (closedProg p drv proc).initial x =
      BitCode.place (closedProg p drv proc) (wP (preCode p drv proc).entry)
        ⟨mkS (fun u => if u = .inr (.inl 3) then x else []), [], []⟩ := by
    simp only [BitProgram.initial, BitCode.place]
    congr 1
    funext t
    obtain ⟨u, rfl⟩ := (es p drv proc).surjective t
    simp [mkS, closedProg, sA]
  -- the main simulation
  have hlen : (d c0).length ≤ x.length + drv.bound.eval x.length := drv.output_length_le c0
  set L := (d c0).length + T with hL
  obtain ⟨m, cfin, hrun2, hpc2, hbuf2, htr2, hm⟩ := sim_run (drv := drv) (proc := proc) c0 x hx R hR L hrun
    p.start rfl hpc hq
    (fun s => by
      simp only [BitProgram.initial]
      split_ifs
      · omega
      · simp only [List.length_nil]; omega)
    (by simp [BitProgram.initial]; omega)
  have hrun1 : (closedProg p drv proc).Run SSG28Closed.noOracle ((closedProg p drv proc).initial x) mp
      (simC (p.initial (d c0)) x p.start) := by
    rw [hinit]; exact hpre'
  refine ⟨mp + m, cfin, hrun1.append hrun2, ?_, hpc2, htr2, cf.transcript, ?_,
    run_transcript_answers R hrun (by simp [BitProgram.initial])⟩
  · have hS := stepB_mono (proc := proc) (show L ≤ x.length + drv.bound.eval x.length + T by omega) x.length
    have h1 : el * stepB proc L x.length ≤ T * stepB proc (x.length + drv.bound.eval x.length + T) x.length :=
      Nat.mul_le_mul hel hS
    unfold elimBound
    omega
  · rw [hbuf2]; exact hpost

end Main

end SSG28MachineElim
