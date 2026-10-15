/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import HigherDyson2.Dyson.RTermExpand

/-!
# The order of the terms of the higher rank series

The `n`-th term `𝒯_{m,n}` of `R_m` is divisible by `q^{n²}` in `𝒜[[q]]`, so its
coefficients `[q^N] 𝒯_{m,n}` vanish for `N < n²`.

## Main results

* `HigherDyson2.RTerm_coeff_eq_zero_of_lt`: `[q^N] 𝒯_{m,n} = 0` for `N < n²`.

## Implementation notes

The statement holds for every `m : ℕ`, including `m = 0`, where `𝒯_{0,n} = q^{n²}`; the
hypothesis `1 ≤ m` is therefore dropped.
-/

public section

open PowerSeries

namespace HigherDyson2

/-- **Order of `𝒯_{m,n}`**: `[q^N] 𝒯_{m,n} = 0` whenever `N < n²`. -/
@[higher_dyson_2 "lem_R_term_order"]
theorem RTerm_coeff_eq_zero_of_lt (m : ℕ) {n N : ℕ} (hN : N < n ^ 2) :
    qCoeff N (RTerm m n) = 0 := by
  rw [qCoeff, RTerm_eq, coeff_X_pow_mul']
  exact ite_eq_right_iff.mpr fun h => absurd h (not_le.mpr hN)

end HigherDyson2
