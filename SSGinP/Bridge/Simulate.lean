module

public import SSGinP.Machine.Closed
public import OAI.Computability.QuantumFactoring.BitStackChoice

@[expose] public section

/-!
# SSGinP.Bridge.Simulate: a closed `BitProgram` is a bit-stack `Procedure`

`SSGinP.Simulate.toProcedure`: a closed `BitProgram` `M` that decides `g` within `(|x|+2)^d` charged steps
gives a `Procedure id boolCode g` (hence, by the ported `Procedure.toTM2`, a Mathlib TM2 running in
polynomial time).

Construction. Stacks
`Stk M = Fin M.stackCount ⊕ (Fin M.states ⊕ Bool)`: the machine stacks, one flag stack per state, the
`run` stack (`inr (inr false)`) and the `out` stack (`inr (inr true)`), which holds `bufferRev`.

    program = push (flag start) true ; push run true ; loop run skip body ; drainAll

`body` finds the one set state flag (a chain of `cases`), reads the scanned top bit (and puts it back),
executes the translated instruction, and (unless the instruction is `halt`) sets the next flag and `run`.
`drainAll` empties every machine stack, so that the final store is `singletonStore out [g x]`.
-/

namespace SSGinP.Simulate

open OAI.Optimization.LinearProgramming.OracleSpec
open OAI.ExactQuantumFactoring.BitStackProgram
open SSG28Closed

/-- the stacks of the simulating program. -/
abbrev Stk (M : BitProgram) : Type := Fin M.stackCount ⊕ (Fin M.states ⊕ Bool)

/-- the store with machine stacks `st`, state flag set exactly at `fl`, `run` stack `r`, `out` stack `o`. -/
def E {M : BitProgram} (st : Fin M.stackCount → Word) (fl : Option (Fin M.states)) (r o : Word) :
    Store (Stk M)
  | .inl k => st k
  | .inr (.inl q) => if fl = some q then [true] else []
  | .inr (.inr false) => r
  | .inr (.inr true) => o

/-- the store that represents a machine configuration. -/
def encC {M : BitProgram} (c : M.Config) : Store (Stk M) :=
  E c.store c.pc (if c.pc.isSome then [true] else []) c.bufferRev

/-! ## the program -/

/-- set the flag of the next state and keep the main loop running. -/
def next (M : BitProgram) (q' : Fin M.states) : Program (Stk M) :=
  .seq (.push (.inr (.inl q')) true) (.push (.inr (.inr false)) true)

/-- translation of one instruction (`ask` never occurs in a closed program). -/
def trans (M : BitProgram) : BitInstruction (Fin M.states) (Fin M.stackCount) → Program (Stk M)
  | .jump q' => next M q'
  | .push s b q' => .seq (.push (.inl s) b) (next M q')
  | .pop s q' => .seq (.cases (.inl s) .skip .skip .skip) (next M q')
  | .emit b q' => .seq (.push (.inr (.inr true)) b) (next M q')
  | .ask _ => .skip
  | .halt => .skip

/-- execute state `q`: read the scanned top bit, put it back, run the instruction. -/
def exec (M : BitProgram) (q : Fin M.states) : Program (Stk M) :=
  .cases (.inl (M.scan q)) (trans M (M.instruction q none))
    (.seq (.push (.inl (M.scan q)) false) (trans M (M.instruction q (some false))))
    (.seq (.push (.inl (M.scan q)) true) (trans M (M.instruction q (some true))))

/-- find the set state flag among `l`, consume it, execute that state. -/
def chain (M : BitProgram) : List (Fin M.states) → Program (Stk M)
  | [] => .skip
  | i :: l => .cases (.inr (.inl i)) (chain M l) .skip (exec M i)

/-- one machine step. -/
def body (M : BitProgram) : Program (Stk M) := chain M (List.finRange M.states)

/-- empty the listed machine stacks. -/
def drainAll (M : BitProgram) : List (Fin M.stackCount) → Program (Stk M)
  | [] => .skip
  | k :: l => .seq (.loop (.inl k) .skip .skip) (drainAll M l)

/-- the whole simulating program. -/
def program (M : BitProgram) : Program (Stk M) :=
  .seq (.seq (.seq (.push (.inr (.inl M.start)) true) (.push (.inr (.inr false)) true))
    (.loop (.inr (.inr false)) .skip (body M))) (drainAll M (List.finRange M.stackCount))

/-! ## store bookkeeping -/

theorem Runs.cast' {K : Type} [DecidableEq K] {p : Program K} {s t s' t' : Store K} {c c' : ℕ}
    (h : Runs p s t c) (hs : s = s') (ht : t = t') (hc : c = c') : Runs p s' t' c' := by
  subst hs ht hc; exact h

theorem runs_push {K : Type} [DecidableEq K] (s t : Store K) (k : K) (b : Bool)
    (h : t = Function.update s k (b :: s k)) : Runs (.push k b) s t 1 := h ▸ Runs.push s k b

variable {M : BitProgram}

theorem E_upd_stk (st : Fin M.stackCount → Word) (fl : Option (Fin M.states)) (r o : Word)
    (k : Fin M.stackCount) (v : Word) :
    Function.update (E st fl r o) (.inl k) v = E (Function.update st k v) fl r o := by
  funext j
  rcases j with j | j | (_ | _) <;> simp [E, Function.update_apply]

theorem E_upd_flag_set (st : Fin M.stackCount → Word) (r o : Word) (q : Fin M.states) :
    Function.update (E st none r o) (.inr (.inl q)) [true] = E st (some q) r o := by
  funext j
  rcases j with j | j | (_ | _) <;> simp [E, Function.update_apply]
  split_ifs with h1 h2 h2 <;> simp_all

theorem E_upd_flag_clear (st : Fin M.stackCount → Word) (r o : Word) (q : Fin M.states) :
    Function.update (E st (some q) r o) (.inr (.inl q)) [] = E st none r o := by
  funext j
  rcases j with j | j | (_ | _) <;> simp [E, Function.update_apply]
  intro h1 h2; exact absurd h2.symm h1

theorem E_upd_run (st : Fin M.stackCount → Word) (fl : Option (Fin M.states)) (r o v : Word) :
    Function.update (E st fl r o) (.inr (.inr false)) v = E st fl v o := by
  funext j
  rcases j with j | j | (_ | _) <;> simp [E]

theorem E_upd_out (st : Fin M.stackCount → Word) (fl : Option (Fin M.states)) (r o v : Word) :
    Function.update (E st fl r o) (.inr (.inr true)) v = E st fl r v := by
  funext j
  rcases j with j | j | (_ | _) <;> simp [E]

@[simp] theorem E_stk (st : Fin M.stackCount → Word) (fl : Option (Fin M.states)) (r o : Word)
    (k : Fin M.stackCount) : E st fl r o (.inl k) = st k := rfl
@[simp] theorem E_flag (st : Fin M.stackCount → Word) (fl : Option (Fin M.states)) (r o : Word)
    (q : Fin M.states) : E st fl r o (.inr (.inl q)) = if fl = some q then [true] else [] := rfl
@[simp] theorem E_run (st : Fin M.stackCount → Word) (fl : Option (Fin M.states)) (r o : Word) :
    E st fl r o (.inr (.inr false)) = r := rfl
@[simp] theorem E_out (st : Fin M.stackCount → Word) (fl : Option (Fin M.states)) (r o : Word) :
    E st fl r o (.inr (.inr true)) = o := rfl

/-! ## one instruction -/

theorem next_runs (st : Fin M.stackCount → Word) (o : Word) (q' : Fin M.states) :
    Runs (next M q') (E st none [] o) (E st (some q') [true] o) 2 := by
  have h1 : Runs (.push (.inr (.inl q')) true) (E st none [] o) (E st (some q') [] o) 1 :=
    runs_push _ _ _ _ (by simp [← E_upd_flag_set])
  have h2 : Runs (.push (.inr (.inr false)) true) (E st (some q') [] o) (E st (some q') [true] o) 1 :=
    runs_push _ _ _ _ (by simp [E_upd_run])
  exact Runs.seq h1 h2

/-- a tick of a closed program costs 1, grows every stack by at most one bit, and is simulated by the
translated instruction. -/
theorem tick_sim (hM : Closed M) {c c' : M.Config} {k : ℕ} (h : M.tick noOracle c = some (k, c')) :
    ∃ q, c.pc = some q ∧ k = 1 ∧ (∀ j, (c'.store j).length ≤ (c.store j).length + 1) ∧
      ∃ a, a ≤ 4 ∧ Runs (trans M (M.instruction q (c.store (M.scan q)).head?))
        (E c.store none [] c.bufferRev) (encC c') a := by
  unfold BitProgram.tick at h
  cases hpc : c.pc with
  | none => simp [hpc] at h
  | some q =>
    refine ⟨q, rfl, ?_⟩
    simp only [hpc, Option.bind_eq_bind, Option.bind_some] at h
    cases hi : M.instruction q (c.store (M.scan q)).head? with
    | ask nx => exact absurd hi (hM _ _ _)
    | jump q' =>
      rw [hi] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨rfl, fun j => Nat.le_succ _, 2, by omega, next_runs _ _ _⟩
    | push s b q' =>
      rw [hi] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨rfl, fun j => ?_, 3, by omega, ?_⟩
      · by_cases hj : j = s
        · subst hj; simp
        · simp [Function.update_of_ne hj]
      · exact Runs.seq (runs_push _ _ _ _ (by simp [E_upd_stk])) (next_runs _ _ _)
    | pop s q' =>
      rw [hi] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨rfl, fun j => ?_, 4, by omega, ?_⟩
      · by_cases hj : j = s
        · subst hj; simp; omega
        · simp [Function.update_of_ne hj]
      · refine Runs.seq (a := 2) (b := 2) ?_ (next_runs _ _ _)
        cases hs : c.store s with
        | nil =>
          have he : Function.update c.store s ([] : Word).tail = c.store := by
            rw [List.tail_nil, ← hs, Function.update_eq_self]
          rw [he]
          exact Runs.cases_nil (by simp [hs]) (Runs.skip _)
        | cons b xs =>
          cases b
          · exact Runs.cases_false (xs := xs) (by simp [hs])
              (Runs.cast' (Runs.skip _) (by simp [E_upd_stk]) rfl rfl)
          · exact Runs.cases_true (xs := xs) (by simp [hs])
              (Runs.cast' (Runs.skip _) (by simp [E_upd_stk]) rfl rfl)
    | emit b q' =>
      rw [hi] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨rfl, fun j => Nat.le_succ _, 3, by omega, ?_⟩
      exact Runs.seq (runs_push _ _ _ _ (by simp [E_upd_out])) (next_runs _ _ _)
    | halt =>
      rw [hi] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨rfl, fun j => Nat.le_succ _, 1, by omega, Runs.skip _⟩

/-- executing state `q`. -/
theorem exec_runs (st : Fin M.stackCount → Word) (o : Word) (q : Fin M.states) {t : Store (Stk M)}
    {a : ℕ} (h : Runs (trans M (M.instruction q (st (M.scan q)).head?)) (E st none [] o) t a) :
    ∃ c, c ≤ a + 2 ∧ Runs (exec M q) (E st none [] o) t c := by
  cases hs : st (M.scan q) with
  | nil =>
    rw [hs] at h
    exact ⟨a + 1, by omega, Runs.cases_nil (by simp [hs]) h⟩
  | cons b xs =>
    rw [hs] at h
    have hback : E st none [] o = Function.update (Function.update (E st none [] o)
        (.inl (M.scan q)) xs) (.inl (M.scan q))
        (b :: Function.update (E st none [] o) (.inl (M.scan q)) xs (.inl (M.scan q))) := by
      rw [Function.update_self, Function.update_idem, E_upd_stk, ← hs, Function.update_eq_self]
    cases b
    · exact ⟨a + 1 + 1, by omega,
        Runs.cases_false (xs := xs) (by simp [hs]) (Runs.seq (runs_push _ _ _ _ hback) h)⟩
    · exact ⟨a + 1 + 1, by omega,
        Runs.cases_true (xs := xs) (by simp [hs]) (Runs.seq (runs_push _ _ _ _ hback) h)⟩

/-- the chain finds the set flag. -/
theorem chain_runs (st : Fin M.stackCount → Word) (r o : Word) (q : Fin M.states)
    {t : Store (Stk M)} {a : ℕ} (h : Runs (exec M q) (E st none r o) t a) :
    ∀ l : List (Fin M.states), q ∈ l →
      ∃ c, c ≤ a + l.length ∧ Runs (chain M l) (E st (some q) r o) t c := by
  intro l
  induction l with
  | nil => intro hq; simp at hq
  | cons i l ih =>
    intro hq
    by_cases hiq : i = q
    · subst hiq
      refine ⟨a + 1, by simp, ?_⟩
      exact Runs.cases_true (xs := []) (by simp) (Runs.cast' h (E_upd_flag_clear _ _ _ _).symm rfl rfl)
    · have hq' : q ∈ l := by
        rcases List.mem_cons.1 hq with h1 | h1
        · exact absurd h1.symm hiq
        · exact h1
      obtain ⟨c, hc, hr⟩ := ih hq'
      refine ⟨c + 1, by simp; omega, ?_⟩
      exact Runs.cases_nil (by simp [Ne.symm hiq]) hr

/-! ## the main loop -/

theorem loop_runs (hM : Closed M) {c c'' : M.Config} {n : ℕ} (h : M.Run noOracle c n c'')
    (hpc : c''.pc = none) :
    (∀ j, (c''.store j).length ≤ (c.store j).length + n) ∧
    ∃ a, a ≤ (M.states + 8) * n + 1 ∧
      Runs (.loop (.inr (.inr false)) .skip (body M)) (encC c) (encC c'') a := by
  induction h with
  | refl c =>
    exact ⟨fun j => le_rfl, 1, by omega, Runs.loop_nil (by simp [encC, hpc])⟩
  | @step c c' c'' n k ht hr ih =>
    obtain ⟨hlen, b, hb, hloop⟩ := ih hpc
    obtain ⟨q, hq, rfl, hlen1, a, ha, hA⟩ := tick_sim hM ht
    obtain ⟨e, he, hE⟩ := exec_runs _ _ _ hA
    obtain ⟨c1, hc1, hbody⟩ := chain_runs _ _ _ _ hE (List.finRange M.states) (List.mem_finRange q)
    rw [List.length_finRange] at hc1
    refine ⟨fun j => by have := hlen j; have := hlen1 j; omega, b + c1 + 1, ?_, ?_⟩
    · have : (M.states + 8) * (1 + n) = (M.states + 8) + (M.states + 8) * n := by ring
      omega
    · refine Runs.loop_true (xs := []) (by simp [encC, hq]) (Runs.cast' hbody ?_ rfl rfl) hloop
      simp [encC, hq, E_upd_run]

/-! ## cleanup -/

theorem drain_runs (o : Word) (k : Fin M.stackCount) (w : Word) :
    ∀ st : Fin M.stackCount → Word, st k = w →
      Runs (.loop (.inl k) .skip .skip) (E st none [] o : Store (Stk M))
        (E (Function.update st k []) none [] o) (2 * w.length + 1) := by
  induction w with
  | nil =>
    intro st hs
    have he : Function.update st k [] = st := by rw [← hs, Function.update_eq_self]
    rw [he]
    exact Runs.loop_nil (by simp [hs])
  | cons b w ih =>
    intro st hs
    have h2 := ih (Function.update st k w) (by simp)
    rw [Function.update_idem] at h2
    cases b
    · exact Runs.cast' (Runs.loop_false (xs := w) (by simp [hs])
        (Runs.cast' (Runs.skip _) (E_upd_stk _ _ _ _ _ _).symm rfl rfl) h2) rfl rfl
        (by simp; omega)
    · exact Runs.cast' (Runs.loop_true (xs := w) (by simp [hs])
        (Runs.cast' (Runs.skip _) (E_upd_stk _ _ _ _ _ _).symm rfl rfl) h2) rfl rfl
        (by simp; omega)

theorem drainAll_runs (o : Word) (L : ℕ) (l : List (Fin M.stackCount)) :
    ∀ st : Fin M.stackCount → Word, (∀ j, (st j).length ≤ L) →
      ∃ c, c ≤ l.length * (2 * L + 2) + 1 ∧
        Runs (drainAll M l) (E st none [] o)
          (E (fun j => if j ∈ l then [] else st j) none [] o) c := by
  induction l with
  | nil => intro st _; exact ⟨1, by omega, Runs.cast' (Runs.skip _) rfl (by simp) rfl⟩
  | cons k l ih =>
    intro st hst
    have h1 := drain_runs (M := M) o k _ st rfl
    obtain ⟨c, hc, h2⟩ := ih (Function.update st k []) (fun j => by
      by_cases hj : j = k
      · subst hj; simp
      · simpa [Function.update_of_ne hj] using hst j)
    refine ⟨c + (2 * (st k).length + 1), ?_, Runs.cast' (Runs.seq h1 h2) rfl ?_ rfl⟩
    · have := hst k
      have : (l.length + 1) * (2 * L + 2) = l.length * (2 * L + 2) + (2 * L + 2) := by ring
      simp only [List.length_cons]
      omega
    · congr 1
      funext j
      by_cases hj : j = k
      · subst hj; simp
      · simp [hj]

/-! ## assembly -/

/-- the time bound, as a polynomial in the input length. -/
noncomputable def bound (M : BitProgram) (d : ℕ) : Polynomial ℕ :=
  Polynomial.C M.stackCount *
      (Polynomial.C 2 * (Polynomial.X + (Polynomial.X + Polynomial.C 2) ^ d) + Polynomial.C 2) +
    Polynomial.C (M.states + 8) * (Polynomial.X + Polynomial.C 2) ^ d + Polynomial.C 4

theorem bound_eval (M : BitProgram) (d X : ℕ) :
    (bound M d).eval X = M.stackCount * (2 * (X + (X + 2) ^ d) + 2) + (M.states + 8) * (X + 2) ^ d + 4 := by
  simp [bound]

theorem program_runs (hM : Closed M) (d : ℕ) (g : Word → Bool)
    (h : ∀ x, DecidesWithin M x ((x.length + 2) ^ d) (g x)) (x : Word) :
    ∃ c, c ≤ (bound M d).eval x.length ∧
      Runs (program M) (singletonStore (.inl M.inputStack) x)
        (singletonStore (.inr (.inr true)) (Procedure.boolCode (g x))) c := by
  obtain ⟨n, c, hrun, hn, hpc, hout⟩ := h x
  have hbuf : c.bufferRev = [g x] := by
    have := congrArg List.reverse hout
    simpa using this
  obtain ⟨hlen, a, ha, hloop⟩ := loop_runs hM hrun hpc
  have hL : ∀ j, (c.store j).length ≤ x.length + n := fun j => by
    have := hlen j
    have h0 : ((M.initial x).store j).length ≤ x.length := by
      simp only [BitProgram.initial]
      split_ifs <;> simp
    omega
  obtain ⟨b, hb, hdrain⟩ := drainAll_runs (M := M) c.bufferRev (x.length + n)
    (List.finRange M.stackCount) c.store hL
  rw [List.length_finRange] at hb
  have hinit : (singletonStore (.inl M.inputStack) x : Store (Stk M)) =
      E (M.initial x).store none [] [] := by
    funext j
    rcases j with j | j | (_ | _) <;>
      simp [singletonStore, Function.update_apply, BitProgram.initial]
  have hstart : Runs (.seq (.push (.inr (.inl M.start)) true) (.push (.inr (.inr false)) true))
      (E (M.initial x).store none [] [] : Store (Stk M)) (encC (M.initial x)) 2 := by
    have := next_runs (M := M) (M.initial x).store [] M.start
    exact Runs.cast' this rfl (by simp [encC, BitProgram.initial]) rfl
  have hfinal : (E (fun j => if j ∈ List.finRange M.stackCount then [] else c.store j) none []
      c.bufferRev : Store (Stk M)) = singletonStore (.inr (.inr true)) (Procedure.boolCode (g x)) := by
    funext j
    rcases j with j | j | (_ | _) <;>
      simp [singletonStore, hbuf]
  have hend : encC c = E c.store none [] c.bufferRev := by simp [encC, hpc]
  rw [hend] at hloop
  refine ⟨b + (a + 2), ?_, ?_⟩
  · rw [bound_eval]
    have h1 : M.stackCount * (2 * (x.length + n) + 2) ≤
        M.stackCount * (2 * (x.length + (x.length + 2) ^ d) + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : (M.states + 8) * n ≤ (M.states + 8) * (x.length + 2) ^ d :=
      Nat.mul_le_mul_left _ hn
    omega
  · rw [hinit, ← hfinal]
    exact Runs.seq (Runs.seq hstart hloop) hdrain

/-- **Theorem B1.** A closed `BitProgram` deciding `g` within `(|x|+2)^d` steps is a `Procedure`. -/
noncomputable def toProcedure (M : BitProgram) (hM : SSG28Closed.Closed M) (d : ℕ)
    (g : Word → Bool) (h : ∀ x, SSG28Closed.DecidesWithin M x ((x.length + 2) ^ d) (g x)) :
    Procedure (id : Word → Word) Procedure.boolCode g where
  K := Stk M
  finiteK := inferInstance
  decideK := inferInstance
  input := .inl M.inputStack
  output := .inr (.inr true)
  program := program M
  bound := bound M d
  runs := fun x => program_runs hM d g h x

end SSGinP.Simulate
