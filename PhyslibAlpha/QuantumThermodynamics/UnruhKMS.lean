/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.QuantumThermodynamics.ThermalKMS
public import PhyslibAlpha.Relativity.General.Unruh

/-!

# The Unruh temperature is the inverse temperature of a KMS state

## i. Overview

The worldline of a uniformly accelerated observer has the imaginary period `2π / a`, and no
shorter one (`Rindler.period_ge`). The thermal state `thermalAlgState K β` of a Hermitian
generator `K` satisfies the KMS condition at `β` (`thermalAlgState_kms`). Taking `β = 2π / a`
joins the two: the KMS state at the inverse temperature of the worldline is the thermal state of
`K`, and its temperature is the Unruh temperature `a / 2π`.

That the state seen by the accelerated observer is this state, with `K` the generator of the
boosts, is the identification of Bisognano and Wichmann. It is not derived here: it is the
hypothesis `IsRindlerThermal`, and everything below holds for any state that satisfies it.

## ii. Key results

- `Rindler.rindlerThermal` : the thermal state at the inverse temperature `2π / a`.
- `Rindler.rindlerThermal_kms` : it satisfies the KMS condition at `2π / a`.
- `Rindler.inverse_temperature_eq` : `2π / a = 1 / (a / 2π)`.
- `Rindler.kms_period_minimal` : no imaginary period of the worldline is shorter than the
  inverse temperature of this state.

## iii. Table of contents

- A. The thermal state of the worldline
- B. KMS and the period

## iv. References

* J. J. Bisognano & E. H. Wichmann, On the duality condition for a Hermitian scalar field,
  1975.
* W. G. Unruh, Notes on black-hole evaporation, 1976.

-/

@[expose] public section

noncomputable section

open scoped Real
open ProbabilisticTheory

namespace Rindler

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-! ## A. The thermal state of the worldline -/

/-- The thermal state of the generator `K` at the inverse temperature `2π / a` of the worldline
of acceleration `a`. -/
def rindlerThermal (K : HermitianMat d ℂ) (a : ℝ) : AlgState (Matrix d d ℂ) :=
  thermalAlgState K (2 * π / a)

/-- The hypothesis of Bisognano and Wichmann: the state of the accelerated observer is the thermal
state of the generator of the boosts. -/
def IsRindlerThermal (ω : AlgState (Matrix d d ℂ)) (K : HermitianMat d ℂ) (a : ℝ) : Prop :=
  ω = rindlerThermal K a

/-! ## B. KMS and the period -/

/-- The thermal state of the worldline satisfies the KMS condition at `2π / a`. -/
lemma rindlerThermal_kms (K : HermitianMat d ℂ) (a : ℝ) (x y : Matrix d d ℂ) :
    rindlerThermal K a (x * imaginaryTimeFlow K (2 * π / a) y) = rindlerThermal K a (y * x) :=
  thermalAlgState_kms K (2 * π / a) x y

/-- A state that is the thermal state of the worldline satisfies the KMS condition at `2π / a`. -/
lemma IsRindlerThermal.kms {ω : AlgState (Matrix d d ℂ)} {K : HermitianMat d ℂ} {a : ℝ}
    (h : IsRindlerThermal ω K a) (x y : Matrix d d ℂ) :
    ω (x * imaginaryTimeFlow K (2 * π / a) y) = ω (y * x) := by
  rw [h]
  exact rindlerThermal_kms K a x y

/-- The inverse temperature of the state is the inverse of the Unruh temperature. -/
lemma inverse_temperature_eq {a : ℝ} (ha : 0 < a) :
    2 * π / a = 1 / unruhTemperature a := by
  rw [eq_div_iff (unruhTemperature_pos ha).ne', mul_comm]
  exact unruhTemperature_mul_period ha.ne'

/-- **No imaginary period of the worldline is shorter than the inverse temperature of the KMS
state.** -/
lemma kms_period_minimal {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (hper : PeriodicInImaginaryTime a β) :
    2 * π / a ≤ β :=
  period_ge ha hβ hper

end Rindler
