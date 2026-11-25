-- Not from openai_math. On Lean 4.33 this file held compatibility shims (`ite_eq_left`, `ite_eq_right`,
-- `dite_eq_left`, `dite_eq_right`, `Finset.prod_le_prod₀`, `List.nodup_iff_length_dedup_eq`). Lean 4.35 / Mathlib
-- v4.35.0 have all six, so only the imports remain (the ported files import this module).
module

public import Mathlib.Basic.Logic.Basic
public import Mathlib.Data.List.Dedup
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
