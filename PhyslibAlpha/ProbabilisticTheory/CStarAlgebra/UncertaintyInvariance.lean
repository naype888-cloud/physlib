/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.Uncertainty
/-!

# Invariance of Robertson's relation for several observables

## i. Overview

Replace a finite family of observables `a_i` by real linear combinations `b_k = ∑_i M_ki a_i`.
Covariance and the expectation of the bracket are both real bilinear, so the covariance matrix
and the bracket matrix transform in the same way, `Σ_b = M Σ_a Mᵀ` and `Ω_b = M Ω_a Mᵀ`. For a
square `M` both determinants are multiplied by `(det M)²`.

Hence Robertson's relation `|det Ω| ≤ det Σ` does not depend on how the observables are chosen:
the ratio `det Σ / |det Ω|` is invariant under every invertible real change of observables, and in
particular under any change of units or of scale, and so is the equality case.

## ii. Key results

- `recombine` : the real recombination `b_k = ∑_i M_ki a_i` of a family of observables.
- `covarianceMatrix_recombine` : `Σ_b = M Σ_a Mᵀ`.
- `bracketMatrix_recombine` : `Ω_b = M Ω_a Mᵀ`.
- `det_covarianceMatrix_recombine`, `det_bracketMatrix_recombine` : both determinants are
  multiplied by `(det M)²`.
- `robertson_det_ratio_invariant` : `det Σ_b · |det Ω_a| = det Σ_a · |det Ω_b|`.
- `robertson_det_eq_iff_of_det_ne_zero` : the equality case is invariant.

## iii. Table of contents

- A. Change of observables
- B. The determinants

## iv. References

* H. P. Robertson, *An indeterminacy relation for several observables and its classical
  interpretation*, Phys. Rev. 46 (1934) 794.

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped ComplexOrder selfAdjoint
open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {ι κ : Type*} [Fintype ι]

/-!

## A. Change of observables

-/

/-- The real recombination `b_k = ∑_i M_ki a_i` of a family of observables. -/
noncomputable def recombine (M : Matrix κ ι ℝ) (a : ι → Observable A) : κ → Observable A :=
  fun k => ∑ i, M k i • a i

namespace UnitalPositiveLinearMap

/-- Under the real change of observables `b_k = ∑_i M_ki a_i`, the covariance matrix becomes
`M Σ Mᵀ`. -/
lemma covarianceMatrix_recombine (ω : 𝓢[ℂ, A]) (a : ι → Observable A) (M : Matrix κ ι ℝ) :
    covarianceMatrix ω (recombine M a) = M * covarianceMatrix ω a * Mᵀ := by
  ext k l
  simp only [recombine, covarianceMatrix, covariance, of_apply, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, mul_apply, transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Under the real change of observables `b_k = ∑_i M_ki a_i`, the bracket matrix becomes
`M Ω Mᵀ`. -/
lemma bracketMatrix_recombine (ω : 𝓢[ℂ, A]) (a : ι → Observable A) (M : Matrix κ ι ℝ) :
    bracketMatrix ω (recombine M a) = M * bracketMatrix ω a * Mᵀ := by
  have hl (t : ℝ) (x y : Observable A) : ⁅t • x, y⁆ = t • ⁅x, y⁆ := smul_lie t x y
  have hr (t : ℝ) (x y : Observable A) : ⁅x, t • y⁆ = t • ⁅x, y⁆ := lie_smul t x y
  have hs (x : Observable A) (y : ι → Observable A) : ⁅x, ∑ j, y j⁆ = ∑ j, ⁅x, y j⁆ :=
    lie_sum Finset.univ y x
  ext k l
  simp only [recombine, bracketMatrix, of_apply, sum_lie, hs, hl, hr, map_sum, map_smul,
    smul_eq_mul, mul_apply, transpose_apply, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-!

## B. The determinants

-/

variable [DecidableEq ι]

/-- A square change of observables multiplies `det Σ` by `(det M)²`. -/
lemma det_covarianceMatrix_recombine (ω : 𝓢[ℂ, A]) (a : ι → Observable A) (M : Matrix ι ι ℝ) :
    (covarianceMatrix ω (recombine M a)).det =
      M.det ^ 2 * (covarianceMatrix ω a).det := by
  rw [covarianceMatrix_recombine, det_mul, det_mul, det_transpose]
  ring

/-- A square change of observables multiplies `det Ω` by `(det M)²`. -/
lemma det_bracketMatrix_recombine (ω : 𝓢[ℂ, A]) (a : ι → Observable A) (M : Matrix ι ι ℝ) :
    (bracketMatrix ω (recombine M a)).det =
      M.det ^ 2 * (bracketMatrix ω a).det := by
  rw [bracketMatrix_recombine, det_mul, det_mul, det_transpose]
  ring

/-- **Robertson's relation does not depend on the choice of observables.** Under every square real
change of observables `b_k = ∑_i M_ki a_i`, `det Σ_b · |det Ω_a| = det Σ_a · |det Ω_b|`: the ratio
`det Σ / |det Ω|` is invariant. -/
lemma robertson_det_ratio_invariant (ω : 𝓢[ℂ, A]) (a : ι → Observable A)
    (M : Matrix ι ι ℝ) :
    (covarianceMatrix ω (recombine M a)).det * |(bracketMatrix ω a).det| =
      (covarianceMatrix ω a).det * |(bracketMatrix ω (recombine M a)).det| := by
  rw [det_covarianceMatrix_recombine, det_bracketMatrix_recombine, abs_mul,
    abs_pow, sq_abs]
  ring

/-- The equality case of Robertson's relation is invariant under every invertible real change of
observables. -/
lemma robertson_det_eq_iff_of_det_ne_zero (ω : 𝓢[ℂ, A]) (a : ι → Observable A)
    {M : Matrix ι ι ℝ} (hM : M.det ≠ 0) :
    |(bracketMatrix ω (recombine M a)).det| =
        (covarianceMatrix ω (recombine M a)).det ↔
      |(bracketMatrix ω a).det| = (covarianceMatrix ω a).det := by
  rw [det_covarianceMatrix_recombine, det_bracketMatrix_recombine, abs_mul,
    abs_pow, sq_abs]
  exact mul_right_inj' (pow_ne_zero 2 hM)

end UnitalPositiveLinearMap

end ProbabilisticTheory
