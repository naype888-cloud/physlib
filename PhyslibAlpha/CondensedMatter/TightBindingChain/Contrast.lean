/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.SpacetimeFoam
/-!

# The contrast of the NRS angle and its scale invariance

## i. Overview

No uncertainty vector is spacelike: whatever the state, the Robertson–Schrödinger relation keeps
it inside the causal cone, so nothing moves faster than light.

In the maximal current state of the open tight binding chain the proper time quantum, the proper
time in units of the bracket, is the tangent of the NRS angle: the ratio of the proper time
`σ_H σ_X sin θ` to the pairing `σ_H σ_X cos θ`. It is zero for `N = 2, 3`, where the
uncertainty vector is lightlike, and from four sites on it is positive and stays strictly below
its long chain limit `√(π² / 3 - 3)`, which no chain reaches.

`C_Nava`, the NRS angle and the proper time quantum depend on the number of sites alone. Two
chains with the same number of sites have the same values, whatever their lattice spacing `a` and
hopping `t ≠ 0`.

## ii. Key results

- `causalCharacter_uncertaintyVector_ne_spaceLike` : no uncertainty vector is spacelike.
- `properTimeQuantum_eq_tan_angleNRS` : the proper time quantum is `tan θ_NRS`.
- `properTimeQuantum_mem_Ioo` : from four sites on it lies in `(0, √(π² / 3 - 3))`.
- `CNava_eq_of_N_eq`, `angleNRS_eq_of_N_eq`, `properTimeQuantum_eq_of_N_eq` : they depend on the
  number of sites alone.

## iii. Table of contents

- A. No uncertainty vector is spacelike
- B. The contrast of the NRS angle
- C. Scale invariance

## iv. References

* H. P. Robertson, *A general formulation of the uncertainty principle and its classical
  interpretation*, Phys. Rev. 35 (1930) 667.

-/

@[expose] public section

namespace ProbabilisticTheory
namespace UnitalPositiveLinearMap

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-!

## A. No uncertainty vector is spacelike

-/

/-- **Nothing moves faster than light.** No uncertainty vector is spacelike. -/
theorem causalCharacter_uncertaintyVector_ne_spaceLike (ω : 𝓢[ℂ, A]) (a b : Observable A) :
    Lorentz.Vector.causalCharacter (uncertaintyVector ω a b) ≠
      Lorentz.Vector.CausalCharacter.spaceLike := by
  rw [Ne, Lorentz.Vector.spaceLike_iff_norm_sq_neg, minkowskiProduct_uncertaintyVector, not_lt]
  exact centeredGramDefect_nonneg ω a b

end UnitalPositiveLinearMap
end ProbabilisticTheory

namespace CondensedMatter
namespace TightBindingChain

variable (T : TightBindingChain)

/-!

## B. The contrast of the NRS angle

-/

/-- **The proper time quantum is the tangent of the NRS angle.** -/
theorem properTimeQuantum_eq_tan_angleNRS (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.properTimeQuantum = Real.tan T.angleNRS := by
  have h1 := T.one_le_CNava ht hN
  have hC : 0 < T.CNava := zero_lt_one.trans_le h1
  rw [T.properTimeQuantum_eq ht hN, T.angleNRS_eq ht hN, Real.tan_arccos, dimQuantum,
    div_eq_mul_inv, one_div T.CNava, inv_inv, ← Real.sqrt_sq hC.le,
    ← Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hC.le]
  congr 1
  field_simp
  ring

/-- From four sites on the proper time quantum lies strictly between `0` and its long chain limit
`√(π² / 3 - 3)`. -/
theorem properTimeQuantum_mem_Ioo (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    T.properTimeQuantum ∈ Set.Ioo 0 √(Real.pi ^ 2 / 3 - 3) :=
  ⟨T.properTimeQuantum_pos ht hN, T.properTime_maxCurrentState_div_lt_sqrt ht hN⟩

/-!

## C. Scale invariance

-/

variable {T} {T' : TightBindingChain}

/-- `C_Nava` depends on the number of sites alone. -/
lemma CNava_eq_of_N_eq (ht : T.t ≠ 0) (ht' : T'.t ≠ 0) (hN : 2 ≤ T.N) (h : T.N = T'.N) :
    T.CNava = T'.CNava := by
  have h1 := T.CNava_sq_eq_cNavaSqForm ht hN
  have h2 := T'.CNava_sq_eq_cNavaSqForm ht' (h ▸ hN)
  rw [h, ← h2] at h1
  exact (pow_left_inj₀ (zero_le_one.trans (T.one_le_CNava ht hN))
    (zero_le_one.trans (T'.one_le_CNava ht' (h ▸ hN))) two_ne_zero).mp h1

/-- The NRS angle depends on the number of sites alone. -/
lemma angleNRS_eq_of_N_eq (ht : T.t ≠ 0) (ht' : T'.t ≠ 0) (hN : 2 ≤ T.N) (h : T.N = T'.N) :
    T.angleNRS = T'.angleNRS := by
  rw [T.angleNRS_eq ht hN, T'.angleNRS_eq ht' (h ▸ hN), CNava_eq_of_N_eq ht ht' hN h]

/-- **Scale invariance.** The proper time quantum depends on the number of sites alone: two
chains with the same number of sites have the same value, whatever their lattice spacing and
hopping. -/
theorem properTimeQuantum_eq_of_N_eq (ht : T.t ≠ 0) (ht' : T'.t ≠ 0) (hN : 2 ≤ T.N)
    (h : T.N = T'.N) : T.properTimeQuantum = T'.properTimeQuantum := by
  rw [T.properTimeQuantum_eq_tan_angleNRS ht hN, T'.properTimeQuantum_eq_tan_angleNRS ht' (h ▸ hN),
    angleNRS_eq_of_N_eq ht ht' hN h]

end TightBindingChain
end CondensedMatter
