/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.QuantumThermodynamics.ThermalUncertainty

/-!

# The heat semigroup is the Gibbs weight

## i. Overview

For a Hermitian matrix `L`, the evolution `e^{-t L}` is the unnormalized thermal state of `L` at
the inverse temperature `t`: `e^{-t L} = Z(t) ρ_t`. With `L` the Laplacian of a graph this says
that diffusion for the time `t` is the Gibbs state of the Laplacian at `β = t`. The propagator is
positive definite for every `t`, since a thermal state has full rank.

## ii. Key results

- `HermitianMat.exp_neg_smul_eq_partition_smul_thermal` : `e^{-t L} = Z(t) ρ_t`.
- `HermitianMat.posDef_exp_neg_smul` : `e^{-t L}` is positive definite.

## iii. Table of contents

- A. The heat semigroup and the thermal state

## iv. References

-/

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-! ## A. The heat semigroup and the thermal state -/

namespace HermitianMat

/-- **The evolution `e^{-t L}` is `Z(t)` times the thermal state of `L` at `β = t`.** -/
lemma exp_neg_smul_eq_partition_smul_thermal (L : HermitianMat d ℂ) (t : ℝ) :
    NormedSpace.exp (((-t : ℝ) : ℂ) • L.mat) =
      ((L.partitionFunctionBetaReal t : ℝ) : ℂ) • (MState.thermalBetaReal L t).M.mat := by
  have h : (((-t : ℝ) : ℂ) • L.mat) = ((-t) • L).mat := by
    rw [HermitianMat.mat_smul, Complex.coe_smul]
  have hZ : (L.partitionFunctionBetaReal t) ≠ 0 := (L.partitionFunctionBetaReal_pos t).ne'
  rw [h, ← exp_mat, MState.thermalBetaReal_M, HermitianMat.mat_smul, ← Complex.coe_smul,
    smul_smul]
  have : ((L.partitionFunctionBetaReal t : ℝ) : ℂ) * ((L.partitionFunctionBetaReal t)⁻¹ : ℝ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hZ, Complex.ofReal_one]
  rw [this, one_smul]

/-- The evolution `e^{-t L}` is positive definite for every `t`. -/
lemma posDef_exp_neg_smul (L : HermitianMat d ℂ) (t : ℝ) :
    (NormedSpace.exp (((-t : ℝ) : ℂ) • L.mat)).PosDef := by
  rw [exp_neg_smul_eq_partition_smul_thermal, Complex.coe_smul]
  exact (MState.thermalBetaReal_posDef L t).smul (L.partitionFunctionBetaReal_pos t)

end HermitianMat
