/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
public import PhyslibAlpha.CondensedMatter.QuasiLocal.Gibbs
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.StateUncertainty
public import PhyslibAlpha.QuantumThermodynamics.ThermalState

/-!

# The thermal state is a state of the matrix algebra

## i. Overview

The thermal state `MState.thermalBetaReal H β` is a density matrix; the Gibbs state `gibbsState`
of `CondensedMatter.QuasiLocal` is a state of the algebra of matrices. They are the same state:
`tr(ρ a) = ω(a)`. Hence everything proved for states of a star algebra applies to the thermal
state, in particular Robertson's relation `|det Ω| ≤ det Σ` for any finite family of observables,
and the expectation of a commutator with the Hamiltonian vanishes.

## ii. Key results

- `HermitianMat.exp_mat` : the matrix of `H.exp` is `NormedSpace.exp H.mat`.
- `thermalAlgState` : the thermal state as an `AlgState` of the matrix algebra.
- `thermalAlgState_apply` : `ω(a) = tr(ρ a)`.
- `robertson_det_thermal` : Robertson's relation in the thermal state.
- `thermalAlgState_commutator_hamiltonian` : `ω([H, a]) = 0`.

## iii. Table of contents

- A. The matrix of the exponential
- B. The thermal state as an `AlgState`
- C. Uncertainty in the thermal state

## iv. References

-/

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open CondensedMatter.QuasiLocal ProbabilisticTheory

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## A. The matrix of the exponential -/

namespace HermitianMat

/-- The matrix of `H.exp` is the matrix exponential of `H`. -/
lemma exp_mat (H : HermitianMat d ℂ) : H.exp.mat = NormedSpace.exp H.mat := by
  open scoped Matrix.Norms.L2Operator in
  unfold HermitianMat.exp
  rw [HermitianMat.cfc_eq]
  exact CFC.real_exp_eq_normedSpace_exp (a := H.mat) H.H

end HermitianMat

variable [Nonempty d]

/-! ## B. The thermal state as an `AlgState` -/

omit [Nonempty d] in
lemma gibbsWeight_real_smul (H : HermitianMat d ℂ) (β : ℝ) :
    gibbsWeight ((β : ℂ) • H.mat) = (((-β) • H).exp).mat := by
  rw [HermitianMat.exp_mat, gibbsWeight]
  congr 1
  have : (((-β) • H : HermitianMat d ℂ)).mat = -((β : ℂ) • H.mat) := by
    rw [HermitianMat.mat_smul, neg_smul, Complex.coe_smul]
  rw [this]

omit [Nonempty d] in
lemma partition_real_smul (H : HermitianMat d ℂ) (β : ℝ) :
    partition ((β : ℂ) • H.mat) = ((H.partitionFunctionBetaReal β : ℝ) : ℂ) := by
  rw [partition, gibbsWeight_real_smul, HermitianMat.partitionFunctionBetaReal,
    ← HermitianMat.trace_eq_trace]
  rfl

omit [Nonempty d] in
omit [Fintype d] [DecidableEq d] in
lemma isHermitian_real_smul (H : HermitianMat d ℂ) (β : ℝ) :
    ((β : ℂ) • H.mat).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, H.H.eq]
  simp

/-- The thermal state as a state of the matrix algebra: the Gibbs state of `βH`. -/
def thermalAlgState (H : HermitianMat d ℂ) (β : ℝ) : AlgState (Matrix d d ℂ) :=
  gibbsState ((β : ℂ) • H.mat) (isHermitian_real_smul H β)

/-- The expectation in the thermal state is `tr(ρ a)`. -/
lemma thermalAlgState_apply (H : HermitianMat d ℂ) (β : ℝ) (a : Matrix d d ℂ) :
    thermalAlgState H β a = ((MState.thermalBetaReal H β).M.mat * a).trace := by
  change gibbsFunctional _ a = _
  rw [gibbsFunctional_apply, partition_real_smul, gibbsWeight_real_smul,
    MState.thermalBetaReal_M]
  simp [Matrix.trace_smul]

/-! ## C. Uncertainty in the thermal state -/

/-- **Robertson's relation in the thermal state**: for every finite family of observables of the
matrix algebra, `|det Ω| ≤ det Σ`. -/
lemma robertson_det_thermal {ι : Type*} [Fintype ι] [DecidableEq ι] (H : HermitianMat d ℂ)
    (β : ℝ) (a : ι → selfAdjoint (Matrix d d ℂ)) :
    |((thermalAlgState H β).bracketMatrix a).det| ≤
      ((thermalAlgState H β).covarianceMatrix a).det :=
  (thermalAlgState H β).robertson_det a

/-- The thermal state is stationary: the expectation of `[H, a]` vanishes. -/
lemma thermalAlgState_commutator_hamiltonian (H : HermitianMat d ℂ) (β : ℝ)
    (a : Matrix d d ℂ) : thermalAlgState H β ⁅H.mat, a⁆ = 0 := by
  rw [thermalAlgState_apply, Ring.lie_def, Matrix.mul_sub]
  have h1 : Commute (((-β) • H).mat) H.mat := by
    rw [HermitianMat.mat_smul]
    exact (Commute.refl _).smul_left _
  have hc : Commute (MState.thermalBetaReal H β).M.mat H.mat := by
    rw [MState.thermalBetaReal_M, HermitianMat.mat_smul]
    exact h1.exp_left'.smul_left _
  have h2 : ((MState.thermalBetaReal H β).M.mat * (a * H.mat)).trace =
      ((MState.thermalBetaReal H β).M.mat * (H.mat * a)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hc.eq]
  rw [Matrix.trace_sub, h2, sub_self]
