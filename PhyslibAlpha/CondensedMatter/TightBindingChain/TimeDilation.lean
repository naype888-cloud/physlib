/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.CausalCone
public import PhyslibAlpha.CondensedMatter.TightBindingChain.VolumetricQuantum
/-!

# The time dilation of the uncertainty

## i. Overview

Robertson–Schrödinger is the Cauchy–Schwarz inequality of two fluctuations; its Minkowski mirror
is the reverse Cauchy–Schwarz inequality of two causal vectors. Between the two sits a right
triangle. Its hypotenuse is the uncertainty product `σ_a σ_b`; the angle `θ` between the
fluctuations splits it into the pairing `σ_a σ_b cos θ` and the proper time of the uncertainty
vector, `τ = σ_a σ_b sin θ`.

Measured against the time axis of any observer at rest, the reverse Cauchy–Schwarz inequality
gives `τ ≤ v₀`: proper time never exceeds coordinate time. This is the time dilation of the
uncertainty.

For the energy and position of the open tight binding chain in the maximal current state, `θ` is
the NRS angle: `τ = σ_H σ_X sin θ_NRS`. Saturation, `N = 2, 3`, is `θ_NRS = 0` and `τ = 0`.

## ii. Key results

- `uncertaintyAngle` : the angle between two fluctuations.
- `norm_pairing_eq_mul_cos` : the pairing is `σ_a σ_b cos θ`.
- `properTime_uncertaintyVector_eq_mul_sin` : the proper time is `σ_a σ_b sin θ`.
- `properTime_uncertaintyVector_le_timeComponent` : proper time never exceeds coordinate time.
- `properTime_maxCurrentState_eq_mul_sin_angleNRS` : in the maximal current state,
  `τ = σ_H σ_X sin θ_NRS`.

## iii. Table of contents

- A. The right triangle of the uncertainty
- B. Time dilation
- C. The NRS angle

## iv. References

* H. P. Robertson, *A general formulation of the uncertainty principle and its classical
  interpretation*, Phys. Rev. 35 (1930) 667.
* P. Langevin, *L'évolution de l'espace et du temps*, Scientia 10 (1911) 31.

-/

@[expose] public section

namespace ProbabilisticTheory
namespace UnitalPositiveLinearMap

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (ω : 𝓢[ℂ, A]) (a b : Observable A)

/-!

## A. The right triangle of the uncertainty

-/

/-- The angle between the fluctuations of `a` and `b` in `ω`,
`arccos (‖ω(δa δb)‖ / (σ_a σ_b))`. -/
noncomputable def uncertaintyAngle : ℝ :=
  Real.arccos (‖ω ((centered ω a : A) * centered ω b)‖ / √(variance ω a * variance ω b))

private lemma norm_pairing_le :
    ‖ω ((centered ω a : A) * centered ω b)‖ ≤ √(variance ω a * variance ω b) := by
  have h := centeredGramDefect_nonneg ω a b
  rw [centeredGramDefect] at h
  rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm]
  exact Real.sqrt_le_sqrt (by linarith)

/-- The pairing of the fluctuations is `σ_a σ_b cos θ`. -/
lemma norm_pairing_eq_mul_cos :
    ‖ω ((centered ω a : A) * centered ω b)‖ =
      √(variance ω a * variance ω b) * Real.cos (uncertaintyAngle ω a b) := by
  rcases (Real.sqrt_nonneg (variance ω a * variance ω b)).eq_or_lt with h | h
  · rw [← h, zero_mul]
    exact le_antisymm (h ▸ norm_pairing_le ω a b) (norm_nonneg _)
  · have h0 := div_nonneg (norm_nonneg (ω ((centered ω a : A) * centered ω b))) h.le
    rw [uncertaintyAngle, Real.cos_arccos (by linarith) ((div_le_one h).mpr
      (norm_pairing_le ω a b)), mul_div_cancel₀ _ h.ne']

/-- **The right triangle of the uncertainty.** The proper time of the uncertainty vector is
`σ_a σ_b sin θ`. -/
theorem properTime_uncertaintyVector_eq_mul_sin :
    SpaceTime.properTime 0 (uncertaintyVector ω a b) =
      √(variance ω a * variance ω b) * Real.sin (uncertaintyAngle ω a b) := by
  have hv : 0 ≤ variance ω a * variance ω b :=
    mul_nonneg (variance_nonneg _ _) (variance_nonneg _ _)
  rw [SpaceTime.properTime, sub_zero, minkowskiProduct_uncertaintyVector, uncertaintyAngle,
    Real.sin_arccos, ← Real.sqrt_mul hv]
  rcases hv.eq_or_lt with h | h
  · have h0 := centeredGramDefect_nonneg ω a b
    have hp : Complex.normSq (ω ((centered ω a : A) * centered ω b)) = 0 := by
      rw [centeredGramDefect, ← h] at h0
      linarith [Complex.normSq_nonneg (ω ((centered ω a : A) * centered ω b))]
    rw [← h, zero_mul, centeredGramDefect, ← h, hp, sub_zero]
  · congr 1
    rw [centeredGramDefect, div_pow, Real.sq_sqrt hv, Complex.sq_norm, mul_sub, mul_one,
      mul_div_cancel₀ _ h.ne']

/-!

## B. Time dilation

-/

/-- **Time dilation of the uncertainty.** Against the time axis of an observer at rest, the
proper time of the uncertainty vector never exceeds its time component, the mean variance. -/
theorem properTime_uncertaintyVector_le_timeComponent :
    SpaceTime.properTime 0 (uncertaintyVector ω a b) ≤ uncertaintyVector ω a b (Sum.inl 0) := by
  have he : Lorentz.Vector.causallyFollows 0 (Lorentz.Vector.basis (Sum.inl 0) :
      Lorentz.Vector 3) := by
    rw [Lorentz.Vector.causallyFollows_zero_iff]
    simp
  have h := Lorentz.Vector.sqrt_mul_sqrt_le_minkowskiProduct_of_causallyFollows
    (causallyFollows_uncertaintyVector ω a b) he
  simpa [SpaceTime.properTime] using h

end UnitalPositiveLinearMap
end ProbabilisticTheory

namespace CondensedMatter
namespace TightBindingChain

open ProbabilisticTheory UnitalPositiveLinearMap

variable (T : TightBindingChain)

/-!

## C. The NRS angle

-/

/-- **The proper time of the maximal current state is `σ_H σ_X sin θ_NRS`.** -/
theorem properTime_maxCurrentState_eq_mul_sin_angleNRS :
    SpaceTime.properTime 0 (T.energyPositionVector T.maxCurrentVectorState) =
      √(variance T.maxCurrentVectorState T.openHamiltonianObservable *
        variance T.maxCurrentVectorState T.positionObservable) * Real.sin T.angleNRS :=
  properTime_uncertaintyVector_eq_mul_sin _ _ _

end TightBindingChain
end CondensedMatter
