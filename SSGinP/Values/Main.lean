module

public import SSGinP.Values.Output
public import SSGinP.Main

@[expose] public section

/-!
# SSGinP.Values.Main: THE VALUES OF ALL NODES AND OPTIMAL STRATEGIES OF A STOPPING GAME
# ARE COMPUTABLE IN POLYNOMIAL TIME, on a Mathlib Turing machine

The definitions (`Solution`, `IsSolution`,
`natBits`, `encodeSolution`, `SolvesSSGValues`, `PTimeWord`) are in `SSGinP.Defs`, the sanity lemmas in SSGinP.Values.Statement.

The machine: reverse the input word; `okGame` test (well formed, stopping by peeling), else write nothing; for
every node `4n+1` bisection steps, each one run of the closed machine obtained from the ported sign-recovery
machine by oracle elimination (`SSGinP.Values.Call`); the exact value by the continued-fraction reconstruction of the
fraction with denominator `≤ 3^n` (`SSGinP.Values.Round`, `SSGinP.Values.Euclid`); the greedy strategies of the exact
values (`SSGinP.Values.Strat`); the output word (`SSGinP.Values.Output`).  No linear system is solved.
-/

namespace SSG

/-- the function computed by the machine: the output word of the game `x`. -/
noncomputable def ssgValuesFun (x : Σ n, Game n) : List Bool := SSGValuesOutput.outF (encode x).reverse

/-- `ssgValuesFun` writes the exact values and optimal strategies (`SolvesSSGValues`). -/
theorem ssgValuesFun_solves : SolvesSSGValues ssgValuesFun := by
  rintro ⟨n, G⟩
  constructor
  · rintro ⟨hw, hs⟩
    obtain ⟨v, hv⟩ := stable_point_exists G hs
    exact ⟨⟨v, greedyMax G v, greedyMin G v⟩,
      (isSolution_iff G _).mpr (SSGValues.greedy_isSolution G hs v hv),
      SSGValuesOutput.outF_accept n G hw hs v hv⟩
  · intro h
    exact SSGValuesOutput.outF_reject n G h

/-- `ssgValuesFun` as a BitStack `Procedure` on encoded games. -/
noncomputable def ssgValuesProc :
    OAI.ExactQuantumFactoring.BitStackProgram.Procedure encode (id : List Bool → List Bool) ssgValuesFun :=
  (SSGValuesOutput.outP.comp SSGinP.encodeReverse).congrFun (fun _ => rfl)

/-- `ssgValuesFun` is computable in polynomial time by a Turing machine (`PTimeWord`). -/
theorem ssgValuesFun_ptime : PTimeWord ssgValuesFun :=
  ⟨ssgValuesProc.toTM2, ssgValuesProc.toTM2_finite⟩

/-- **The values of all nodes and optimal strategies of a Stopping Game are computable in polynomial time.** -/
theorem ssg_values_in_P_proved : ∃ f, SolvesSSGValues f ∧ PTimeWord f :=
  ⟨ssgValuesFun, ssgValuesFun_solves, ssgValuesFun_ptime⟩

end SSG
