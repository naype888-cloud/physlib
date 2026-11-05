/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.StateOrderUncertainty
public import PhyslibAlpha.QuantumThermodynamics.ThermalUncertainty

/-!

# The thermal state in the order of the matrix algebra

## i. Overview

`thermalAlgState` is a state of the matrix algebra in the algebraic language (`AlgState`). With the
order of the matrices, it is also a state `𝓢[ℂ, Matrix d d ℂ]` (`AlgState.toState`), and the two
languages describe the same covariance and the same bracket. Robertson's relation in the thermal
state is therefore one statement, whichever language is used.

## ii. Key results

- `thermalState` : the thermal state as a state `𝓢[ℂ, Matrix d d ℂ]`.
- `ofState_thermalState` : it returns to `thermalAlgState`.
- `thermalState_apply` : `φ(a) = tr(ρ a)`.
- `covarianceMatrix_thermalState`, `bracketMatrix_thermalState` : `Σ` and `Ω` agree in both
  languages.
- `robertson_det_thermalState` : Robertson's relation for `𝓢[ℂ, Matrix d d ℂ]`.

## iii. Table of contents

- A. The thermal state in the order
- B. Uncertainty

## iv. References

-/

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder MatrixOrder selfAdjoint Matrix.Norms.L2Operator
open ProbabilisticTheory

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-! ## A. The thermal state in the order -/

/-- The thermal state as a state `𝓢[ℂ, Matrix d d ℂ]` for the order of the matrices. -/
def thermalState (H : HermitianMat d ℂ) (β : ℝ) : 𝓢[ℂ, Matrix d d ℂ] :=
  (thermalAlgState H β).toState

lemma ofState_thermalState (H : HermitianMat d ℂ) (β : ℝ) :
    AlgState.ofState (thermalState H β) = thermalAlgState H β :=
  AlgState.ofState_toState _

lemma thermalState_apply (H : HermitianMat d ℂ) (β : ℝ) (a : Matrix d d ℂ) :
    thermalState H β a = ((MState.thermalBetaReal H β).M.mat * a).trace :=
  thermalAlgState_apply H β a

/-! ## B. Uncertainty -/

lemma covarianceMatrix_thermalState {ι : Type*} (H : HermitianMat d ℂ) (β : ℝ)
    (a : ι → Observable (Matrix d d ℂ)) :
    (thermalAlgState H β).covarianceMatrix a =
      UnitalPositiveLinearMap.covarianceMatrix (thermalState H β) a := by
  rw [← ofState_thermalState H β]
  exact UnitalPositiveLinearMap.covarianceMatrix_ofState _ a

lemma bracketMatrix_thermalState {ι : Type*} (H : HermitianMat d ℂ) (β : ℝ)
    (a : ι → Observable (Matrix d d ℂ)) :
    (thermalAlgState H β).bracketMatrix a =
      UnitalPositiveLinearMap.bracketMatrix (thermalState H β) a := by
  rw [← ofState_thermalState H β]
  exact UnitalPositiveLinearMap.bracketMatrix_ofState _ a

/-- **Robertson's relation in the thermal state**, for the state `𝓢[ℂ, Matrix d d ℂ]`. -/
lemma robertson_det_thermalState {ι : Type*} [Fintype ι] [DecidableEq ι] (H : HermitianMat d ℂ)
    (β : ℝ) (a : ι → Observable (Matrix d d ℂ)) :
    |(UnitalPositiveLinearMap.bracketMatrix (thermalState H β) a).det| ≤
      (UnitalPositiveLinearMap.covarianceMatrix (thermalState H β) a).det := by
  rw [← bracketMatrix_thermalState, ← covarianceMatrix_thermalState]
  exact robertson_det_thermal H β a
