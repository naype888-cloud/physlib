/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.QuantumThermodynamics.ThermalUncertainty

/-!

# The thermal state satisfies the KMS condition

## i. Overview

The Gibbs state of `βH` on the algebra of matrices satisfies the Kubo–Martin–Schwinger condition
at inverse temperature `β`: if `σ(b) = e^{-βH} b e^{βH}` is the evolution by the imaginary time
`iβ`, then `ω(a σ(b)) = ω(b a)` for all `a`, `b`. In finite dimension this is the cyclicity of the
trace; it is a theorem about a concrete state and not a definition.

## ii. Key results

- `imaginaryTimeFlow` : `b ↦ e^{-βH} b e^{βH}`.
- `gibbsWeight_neg_mul` : `e^{βH} e^{-βH} = 1`.
- `thermalAlgState_kms` : `ω(a σ(b)) = ω(b a)`.

## iii. Table of contents

- A. The evolution by imaginary time
- B. The KMS condition

## iv. References

* O. Bratteli & D. Robinson, Operator Algebras and Quantum Statistical Mechanics 2,
  Definition 5.3.1.

-/

@[expose] public section

noncomputable section

open scoped Matrix ComplexOrder
open CondensedMatter.QuasiLocal ProbabilisticTheory

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## A. The evolution by imaginary time -/

/-- The Gibbs weight of `-h` is the inverse of the Gibbs weight of `h`. -/
lemma gibbsWeight_neg_mul (h : Matrix d d ℂ) : gibbsWeight (-h) * gibbsWeight h = 1 := by
  unfold gibbsWeight
  rw [neg_neg, Matrix.exp_neg]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _))

/-- The evolution by the imaginary time `iβ`: `b ↦ e^{-βH} b e^{βH}`. -/
def imaginaryTimeFlow (H : HermitianMat d ℂ) (β : ℝ) (b : Matrix d d ℂ) : Matrix d d ℂ :=
  gibbsWeight ((β : ℂ) • H.mat) * b * gibbsWeight (-((β : ℂ) • H.mat))

/-! ## B. The KMS condition -/

/-- **The KMS condition**: the thermal state satisfies `ω(a σ(b)) = ω(b a)`, where `σ` is the
evolution by the imaginary time `iβ`. -/
lemma thermalAlgState_kms [Nonempty d] (H : HermitianMat d ℂ) (β : ℝ) (a b : Matrix d d ℂ) :
    thermalAlgState H β (a * imaginaryTimeFlow H β b) = thermalAlgState H β (b * a) := by
  change gibbsFunctional _ _ = gibbsFunctional _ _
  rw [gibbsFunctional_apply, gibbsFunctional_apply]
  congr 1
  set W := gibbsWeight ((β : ℂ) • H.mat)
  set V := gibbsWeight (-((β : ℂ) • H.mat))
  have hVW : V * W = 1 := gibbsWeight_neg_mul _
  unfold imaginaryTimeFlow
  change (W * (a * (W * b * V))).trace = (W * (b * a)).trace
  calc (W * (a * (W * b * V))).trace = (V * (W * (a * (W * b)))).trace := by
        rw [show W * (a * (W * b * V)) = (W * (a * (W * b))) * V by simp only [Matrix.mul_assoc],
          Matrix.trace_mul_comm]
    _ = (a * (W * b)).trace := by rw [← Matrix.mul_assoc V W, hVW, Matrix.one_mul]
    _ = (W * (b * a)).trace := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_assoc]
