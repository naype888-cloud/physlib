/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.Uncertainty
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.StateOrder
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.StateUncertainty

/-!

# The two uncertainty relations of a state agree

## i. Overview

On a C⋆-algebra, Robertson's relation for several observables is stated once for `AlgState`
(`AlgState.robertson_det`) and once for `𝓢[ℂ, A]` (`UnitalPositiveLinearMap.robertson_det`).
Through `AlgState.ofState` the matrices `Σ` and `Ω` of the two statements are equal, so a result
about the quasi-local algebra of a crystal and a result about the tight binding chain describe the
same covariance and the same bracket.

## ii. Key results

- `UnitalPositiveLinearMap.covariance_ofState`, `UnitalPositiveLinearMap.bracket_ofState` : the
  covariance and the expectation of the bracket do not depend on the language of states.
- `UnitalPositiveLinearMap.covarianceMatrix_ofState`,
  `UnitalPositiveLinearMap.bracketMatrix_ofState` : the matrices `Σ` and `Ω` agree.
- `UnitalPositiveLinearMap.robertson_det_of_algState` : Robertson's relation for `𝓢[ℂ, A]` from
  the one for `AlgState`.

## iii. Table of contents

- A. Covariance and bracket
- B. The matrices `Σ` and `Ω`
- C. Robertson's relation through `AlgState`

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped ComplexOrder selfAdjoint

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace UnitalPositiveLinearMap

/-! ## A. Covariance and bracket -/

/-- The centered observable is the fluctuation `a - ω(a) 1`. -/
lemma coe_centered_eq_fluctuation (φ : 𝓢[ℂ, A]) (a : Observable A) :
    (centered φ a : A) = (AlgState.ofState φ).fluctuation a := by
  have h : φ (a : A) = ((expectation φ a : ℝ) : ℂ) := apply_observable_eq_expectation φ a
  simp only [centered, LinearMap.centered, AlgState.fluctuation, AlgState.ofState_apply, h]
  simp [Complex.coe_smul]
  rfl

lemma covariance_ofState (φ : 𝓢[ℂ, A]) (a b : Observable A) :
    (AlgState.ofState φ).covariance a b = covariance φ a b := by
  rw [covariance_eq_re_apply_centered_mul, coe_centered_eq_fluctuation,
    coe_centered_eq_fluctuation]
  rfl

lemma bracket_ofState (φ : 𝓢[ℂ, A]) (a b : Observable A) :
    (AlgState.ofState φ).bracket a b = φ⟨⁅a, b⁆⟩ := by
  rw [AlgState.bracket, AlgState.ofState_apply, apply_observable_eq_expectation]
  simp

/-! ## B. The matrices `Σ` and `Ω` -/

lemma covarianceMatrix_ofState {ι : Type*} (φ : 𝓢[ℂ, A]) (a : ι → Observable A) :
    (AlgState.ofState φ).covarianceMatrix a = covarianceMatrix φ a := by
  ext j k
  exact covariance_ofState φ _ _

lemma bracketMatrix_ofState {ι : Type*} (φ : 𝓢[ℂ, A]) (a : ι → Observable A) :
    (AlgState.ofState φ).bracketMatrix a = bracketMatrix φ a := by
  ext j k
  exact bracket_ofState φ _ _

/-! ## C. Robertson's relation through `AlgState` -/

/-- Robertson's relation for several observables in a state `𝓢[ℂ, A]`, obtained from the one
for `AlgState`. -/
lemma robertson_det_of_algState {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : 𝓢[ℂ, A])
    (a : ι → Observable A) : |(bracketMatrix φ a).det| ≤ (covarianceMatrix φ a).det := by
  rw [← bracketMatrix_ofState, ← covarianceMatrix_ofState]
  exact (AlgState.ofState φ).robertson_det a

end UnitalPositiveLinearMap
end ProbabilisticTheory
