module

import Solution

/-!
Prints the axioms used by the ten advertised theorems as proved in `Solution.lean`.
Run with `lake env lean test/Axioms.lean` after `lake build`. Every line must list exactly
`propext`, `Classical.choice`, `Quot.sound` (or a subset): no `sorryAx`, no `Lean.ofReduceBool`.
-/

#print axioms SSG.ssg_in_P
#print axioms SSG.ssgStrict_in_P
#print axioms SSG.encode_length
#print axioms SSG.encode_injective
#print axioms SSG.ssg_values_in_P
#print axioms SSG.encodeSolution_length
#print axioms SSG.isSolution_value_unique
#print axioms SSG.isSolution_value_bits
#print axioms SSG.encodeSolution_injective
#print axioms SSG.ssgDecision_iff_value
