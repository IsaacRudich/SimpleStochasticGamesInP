module

public import SSGinP.Main
public import SSGinP.Values.Main

@[expose] public section

/-!
# Proved solution

The ten theorems of `Challenge.lean`, with the same names and statements, proved from the library `SSGinP`
(which builds on the files under `OAI/`). The definitions they mention are those of `SSGinP/Defs.lean`, a verbatim
copy of the definitions of `Challenge.lean` (`scripts/check_defs_sync.py`).
-/

namespace SSG

variable {n : Nat}

/-- **The SSG decision problem is in P.** -/
theorem ssg_in_P : ∃ f, SolvesSSG f ∧ PTime f :=
  ssg_in_P_proved

/-- **The strict SSG decision problem is in P.** -/
theorem ssgStrict_in_P : ∃ f, SolvesSSGStrict f ∧ PTime f :=
  ssgStrict_in_P_proved

/-- the word of a game on `n` nodes has length exactly `10 n²`. -/
theorem encode_length (G : Game n) : (encode ⟨n, G⟩).length = 10 * n ^ 2 :=
  encode_length_proved G

/-- the word determines the game: different games have different words. -/
theorem encode_injective : Function.Injective encode :=
  encode_injective_proved

/-- **The values of all nodes and optimal strategies of a Stopping Game are computable in polynomial time.** -/
theorem ssg_values_in_P : ∃ f, SolvesSSGValues f ∧ PTimeWord f :=
  ssg_values_in_P_proved

/-- the output word has length `4 n² + 2 n`. -/
theorem encodeSolution_length (s : Solution n) : (encodeSolution s).length = 4 * n ^ 2 + 2 * n :=
  encodeSolution_length_proved s

/-- the values of an answer are unique: `s.value i` is the value of node `i`. -/
theorem isSolution_value_unique (G : Game n) (s s' : Solution n) (h : IsSolution G s) (h' : IsSolution G s') :
    s.value = s'.value :=
  isSolution_value_unique_proved G s s' h h'

/-- the `2 n` bits lose nothing: on a Stopping Game every value of an answer is `≥ 0` and its numerator and
denominator are below `2^(2n)`. -/
theorem isSolution_value_bits (G : Game n) (hs : StoppingGame G) (s : Solution n) (h : IsSolution G s)
    (i : Fin n) :
    0 ≤ s.value i ∧ (s.value i).num.toNat < 2 ^ (2 * n) ∧ (s.value i).den < 2 ^ (2 * n) :=
  isSolution_value_bits_proved G hs s h i

/-- the word determines the answer (among the answers of one game). -/
theorem encodeSolution_injective (G : Game n) (s s' : Solution n) (h : IsSolution G s) (h' : IsSolution G s')
    (he : encodeSolution s = encodeSolution s') : s = s' :=
  encodeSolution_injective_proved G s s' h h' he

/-- consistency with the decision problem of section 4. -/
theorem ssgDecision_iff_value (G : Game n) (s : Solution n) (h : IsSolution G s) :
    SSGDecision G ↔ WellFormed G ∧ StoppingGame G ∧ 1 / 2 ≤ s.value G.startNode :=
  ssgDecision_iff_value_proved G s h

end SSG
