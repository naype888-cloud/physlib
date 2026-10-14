/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.Basic
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.UncertaintyInvariance
/-!

# Robertson's relation on the cube, for every choice of observables

## i. Overview

In the maximal current state of the open tight binding cube, the six observables `(H, X)` of the
three axes satisfy `det Σ = (C(x) C(y) C(z))² |det Ω|`, and Robertson's relation
for several observables is strict from `4 × 4 × 4` on. Under a real change of observables
`b_k = ∑_i M_ki a_i` both determinants are multiplied by `(det M)²`. Hence the same identity holds
for every real recombination of the six observables, and the strict inequality for every
invertible one: it does not depend on the units, the scale or the basis in which the observables
are measured. The scale of the particle enters only through `|det Ω|`; the ratio
`det Σ / |det Ω|` depends only on the numbers of sites.

## ii. Key results

- `det_bracketMatrix_cubePairs` : `det Ω = (Ω_x Ω_y Ω_z)²` for the six observables.
- `det_covarianceMatrix_recombine_maxCurrentCubeState` : `det Σ = (C_x C_y C_z)² |det Ω|` for
  every real recombination of the six observables.
- `robertson_det_recombine_maxCurrentCubeState_strict` : from `4 × 4 × 4` on, `|det Ω| < det Σ`
  for every invertible real recombination.

## iii. Table of contents

- A. The bracket determinant
- B. Every choice of observables

## iv. References

* H. P. Robertson, *An indeterminacy relation for several observables and its classical
  interpretation*, Phys. Rev. 46 (1934) 794.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open scoped ComplexOrder selfAdjoint QuantumMechanics.FiniteHilbertSpace
open ProbabilisticTheory
open QuantumMechanics FiniteHilbertSpace UnitalPositiveLinearMap
open Matrix

variable (Tx Ty Tz : TightBindingChain)

/-!

## A. The bracket determinant

-/

/-- In any state of the cube, the determinant of the bracket matrix of the six observables is the
square of the product of the brackets of the three axes. -/
lemma det_bracketMatrix_cubePairs (ω : 𝓢[ℂ, Tx.CubeOperators Ty Tz]) :
    (bracketMatrix ω (Tx.cubePairs Ty Tz)).det =
      (Tx.axisBracket Ty Tz ω 0 * Tx.axisBracket Ty Tz ω 1 * Tx.axisBracket Ty Tz ω 2) ^ 2 := by
  rw [bracketMatrix_cubePairs, det_blockDiagonal, Fin.prod_univ_three]
  simp only [det_fin_two_of, zero_mul, zero_sub, mul_neg, neg_neg]
  ring

/-!

## B. Every choice of observables

-/

/-- In the maximal current state of the cube, `det Σ = (C_x C_y C_z)² |det Ω|` for every real
recombination `b_k = ∑_i M_ki a_i` of the six observables. -/
lemma det_covarianceMatrix_recombine_maxCurrentCubeState (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0)
    (hz : Tz.t ≠ 0) (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N)
    (M : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℝ) :
    (covarianceMatrix (Tx.maxCurrentCubeVectorState Ty Tz)
        (recombine M (Tx.cubePairs Ty Tz))).det =
      (Tx.uncertaintyRatio * Ty.uncertaintyRatio * Tz.uncertaintyRatio) ^ 2 *
        |(bracketMatrix (Tx.maxCurrentCubeVectorState Ty Tz)
          (recombine M (Tx.cubePairs Ty Tz))).det| := by
  rw [det_covarianceMatrix_recombine, det_bracketMatrix_recombine,
    Tx.det_covarianceMatrix_maxCurrentCubeState Ty Tz hx hy hz hNx hNy hNz,
    det_bracketMatrix_cubePairs, abs_mul, abs_pow, sq_abs, abs_of_nonneg (sq_nonneg _)]
  ring

/-- **Robertson's relation is strict on the cube for every choice of observables.** From
`4 × 4 × 4` on, in the maximal current state, `|det Ω| < det Σ` for every invertible real
recombination of the six observables `(H, X)` of the three axes. -/
lemma robertson_det_recombine_maxCurrentCubeState_strict (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0)
    (hz : Tz.t ≠ 0) (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N)
    {M : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℝ} (hM : M.det ≠ 0) :
    |(bracketMatrix (Tx.maxCurrentCubeVectorState Ty Tz)
        (recombine M (Tx.cubePairs Ty Tz))).det| <
      (covarianceMatrix (Tx.maxCurrentCubeVectorState Ty Tz)
        (recombine M (Tx.cubePairs Ty Tz))).det := by
  rw [Tx.det_covarianceMatrix_recombine_maxCurrentCubeState Ty Tz hx hy hz (by omega) (by omega)
    (by omega)]
  have hpos : 0 < |(bracketMatrix (Tx.maxCurrentCubeVectorState Ty Tz)
      (recombine M (Tx.cubePairs Ty Tz))).det| := by
    rw [det_bracketMatrix_recombine, det_bracketMatrix_cubePairs,
      sq_axisBracket_maxCurrentCubeState]
    exact abs_pos.mpr (mul_ne_zero (pow_ne_zero 2 hM) (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero
      (Tx.bound_ne_zero hx (by omega)) (Ty.bound_ne_zero hy (by omega)))
      (Tz.bound_ne_zero hz (by omega)))))
  have hC : 1 < (Tx.uncertaintyRatio * Ty.uncertaintyRatio * Tz.uncertaintyRatio) ^ 2 :=
    one_lt_pow₀ (one_lt_mul_of_lt_of_le
      (one_lt_mul_of_lt_of_le (Tx.one_lt_uncertaintyRatio hx hNx)
        (Ty.one_le_uncertaintyRatio hy (by omega)))
      (Tz.one_le_uncertaintyRatio hz (by omega))) two_ne_zero
  nlinarith

end TightBindingChain
end CondensedMatter
