/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Physlib.Cosmology.FLRW.MatterContent
/-!

# A time-dependent vacuum term

## i. Overview

`MatterContent` reads the cosmological constant as a fluid of density `ρ_Λ = Λ c² / (8 π G)`
and pressure `p_Λ = - ρ_Λ c²`. Here `Λ` may depend on cosmic time. The vacuum fluid is added
to a cosmic fluid `(ρ, p)`, and the Friedmann equations are imposed on the total with no
separate cosmological constant.

The vacuum has `ρ_Λ + p_Λ / c² = 0`, so it drops out of the pressure term of the continuity
equation and only its time derivative remains. The continuity equation of the total, which
follows from the Friedmann equations, becomes a balance between the cosmic fluid and the
vacuum: `∂ₜ ρ + 3 H (ρ + p / c²) = - (c² / (8 π G)) ∂ₜ Λ`. A decreasing `Λ` is a source for
the cosmic fluid, and the cosmic fluid satisfies its own continuity equation exactly when
`∂ₜ Λ = 0`.

## ii. Key results

- `vacuumDensity`, `vacuumPressure` : `ρ_Λ (t)` and `p_Λ (t)` of a time-dependent `Λ`.
- `vacuumDensity_add_vacuumPressure_div` : `ρ_Λ + p_Λ / c² = 0`.
- `deriv_vacuumDensity` : `∂ₜ ρ_Λ = (c² / (8 π G)) ∂ₜ Λ`.
- `continuityEquation_add_vacuum_iff` : the continuity equation of the total is the balance
  `∂ₜ ρ + 3 H (ρ + p / c²) = - ∂ₜ ρ_Λ`.
- `energy_balance_of_friedmann` : the balance follows from the Friedmann equations.
- `source_pos_of_deriv_neg` : a decreasing `Λ` is a positive source for the cosmic fluid.
- `continuityEquation_iff_deriv_eq_zero` : the cosmic fluid is conserved iff `∂ₜ Λ = 0`.

## iii. Table of contents

- A. The vacuum fluid of a time-dependent `Λ`
- B. The energy balance

## iv. References

- J. M. Overduin and F. I. Cooperstock, *Evolution of the scale factor with a variable
  cosmological term*, Phys. Rev. D 58 (1998) 043506.

-/

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

open Real Time

/-!

## A. The vacuum fluid of a time-dependent `Λ`

-/

/-- The vacuum density `ρ_Λ (t) = Λ (t) c² / (8 π G)` of a time-dependent `Λ`. -/
noncomputable def vacuumDensity (Λ : Time → ℝ) (G c : ℝ) : Time → ℝ :=
  fun s => cosmologicalConstantDensity (Λ s) G c

/-- The vacuum pressure `p_Λ (t) = - ρ_Λ (t) c²` of a time-dependent `Λ`. -/
noncomputable def vacuumPressure (Λ : Time → ℝ) (G c : ℝ) : Time → ℝ :=
  fun s => cosmologicalConstantPressure (Λ s) G c

/-- The vacuum has `ρ_Λ + p_Λ / c² = 0`. -/
lemma vacuumDensity_add_vacuumPressure_div {Λ : Time → ℝ} {G c : ℝ} (hc : c ≠ 0) (t : Time) :
    vacuumDensity Λ G c t + vacuumPressure Λ G c t / c ^ 2 = 0 := by
  unfold vacuumDensity vacuumPressure cosmologicalConstantPressure
  field_simp
  ring

/-- `∂ₜ ρ_Λ = (c² / (8 π G)) ∂ₜ Λ`. -/
lemma deriv_vacuumDensity {Λ : Time → ℝ} {G c : ℝ} {t : Time} (hΛ : DifferentiableAt ℝ Λ t) :
    ∂ₜ (vacuumDensity Λ G c) t = ∂ₜ Λ t * (c ^ 2 / (8 * π * G)) := by
  have h : vacuumDensity Λ G c = fun s => Λ s * (c ^ 2 / (8 * π * G)) := by
    funext s
    unfold vacuumDensity cosmologicalConstantDensity
    ring
  rw [h, deriv_mul_const _ _ hΛ]

lemma differentiableAt_vacuumDensity {Λ : Time → ℝ} {G c : ℝ} {t : Time}
    (hΛ : DifferentiableAt ℝ Λ t) : DifferentiableAt ℝ (vacuumDensity Λ G c) t := by
  have h : vacuumDensity Λ G c = fun s => Λ s * (c ^ 2 / (8 * π * G)) := by
    funext s
    unfold vacuumDensity cosmologicalConstantDensity
    ring
  rw [h]
  exact hΛ.mul_const _

/-!

## B. The energy balance

-/

/-- The continuity equation of the cosmic fluid plus the vacuum is the balance
  `∂ₜ ρ + 3 H (ρ + p / c²) = - ∂ₜ ρ_Λ`. -/
lemma continuityEquation_add_vacuum_iff {a ρ p Λ : Time → ℝ} {G c : ℝ} {t : Time}
    (hc : c ≠ 0) (hdρ : DifferentiableAt ℝ ρ t) (hΛ : DifferentiableAt ℝ Λ t) :
    ContinuityEquation a (fun s => ρ s + vacuumDensity Λ G c s)
        (fun s => p s + vacuumPressure Λ G c s) c t ↔
      ∂ₜ ρ t + 3 * hubbleConstant a t * (ρ t + p t / c ^ 2) =
        -∂ₜ (vacuumDensity Λ G c) t := by
  unfold ContinuityEquation
  rw [deriv_add _ _ hdρ (differentiableAt_vacuumDensity hΛ)]
  have hv := vacuumDensity_add_vacuumPressure_div (Λ := Λ) (G := G) hc t
  constructor
  · intro h
    linear_combination h - 3 * hubbleConstant a t * hv
  · intro h
    linear_combination h + 3 * hubbleConstant a t * hv

/-- **The energy balance.** If the cosmic fluid plus the vacuum of a time-dependent `Λ` satisfy
  the Friedmann equations, then `∂ₜ ρ + 3 H (ρ + p / c²) = - (c² / (8 π G)) ∂ₜ Λ`. -/
theorem energy_balance_of_friedmann {a ρ p Λ : Time → ℝ} {k G c : ℝ} {t : Time}
    (hG : G ≠ 0) (hc : c ≠ 0) (ha : a t ≠ 0) (hd1 : DifferentiableAt ℝ a t)
    (hd2 : DifferentiableAt ℝ (∂ₜ a) t) (hdρ : DifferentiableAt ℝ ρ t)
    (hΛ : DifferentiableAt ℝ Λ t)
    (hF1 : ∀ s, FirstOrderFriedmann a (fun s => ρ s + vacuumDensity Λ G c s) k 0 G c s)
    (hF2 : SecondOrderFriedmann a (fun s => ρ s + vacuumDensity Λ G c s)
      (fun s => p s + vacuumPressure Λ G c s) 0 G c t) :
    ∂ₜ ρ t + 3 * hubbleConstant a t * (ρ t + p t / c ^ 2) =
      -(∂ₜ Λ t * (c ^ 2 / (8 * π * G))) := by
  have hC : ContinuityEquation a (fun s => ρ s + vacuumDensity Λ G c s)
      (fun s => p s + vacuumPressure Λ G c s) c t :=
    continuityEquation_of_friedmann hG ha hd1 hd2
      (hdρ.add (differentiableAt_vacuumDensity hΛ)) hF1 hF2
  rw [continuityEquation_add_vacuum_iff hc hdρ hΛ, deriv_vacuumDensity hΛ] at hC
  exact hC

/-- **A decreasing `Λ` is a source for the cosmic fluid**: with `G > 0` and `∂ₜ Λ < 0`,
  `∂ₜ ρ + 3 H (ρ + p / c²) > 0`. -/
theorem source_pos_of_deriv_neg {a ρ p Λ : Time → ℝ} {k G c : ℝ} {t : Time}
    (hG : 0 < G) (hc : c ≠ 0) (ha : a t ≠ 0) (hd1 : DifferentiableAt ℝ a t)
    (hd2 : DifferentiableAt ℝ (∂ₜ a) t) (hdρ : DifferentiableAt ℝ ρ t)
    (hΛ : DifferentiableAt ℝ Λ t) (hΛ' : ∂ₜ Λ t < 0)
    (hF1 : ∀ s, FirstOrderFriedmann a (fun s => ρ s + vacuumDensity Λ G c s) k 0 G c s)
    (hF2 : SecondOrderFriedmann a (fun s => ρ s + vacuumDensity Λ G c s)
      (fun s => p s + vacuumPressure Λ G c s) 0 G c t) :
    0 < ∂ₜ ρ t + 3 * hubbleConstant a t * (ρ t + p t / c ^ 2) := by
  rw [energy_balance_of_friedmann hG.ne' hc ha hd1 hd2 hdρ hΛ hF1 hF2]
  have : 0 < c ^ 2 / (8 * π * G) := by positivity
  nlinarith

/-- **The cosmic fluid is conserved exactly when `Λ` is constant in time**: under the Friedmann
  equations, the continuity equation of `(ρ, p)` holds at `t` iff `∂ₜ Λ t = 0`. -/
theorem continuityEquation_iff_deriv_eq_zero {a ρ p Λ : Time → ℝ} {k G c : ℝ} {t : Time}
    (hG : G ≠ 0) (hc : c ≠ 0) (ha : a t ≠ 0) (hd1 : DifferentiableAt ℝ a t)
    (hd2 : DifferentiableAt ℝ (∂ₜ a) t) (hdρ : DifferentiableAt ℝ ρ t)
    (hΛ : DifferentiableAt ℝ Λ t)
    (hF1 : ∀ s, FirstOrderFriedmann a (fun s => ρ s + vacuumDensity Λ G c s) k 0 G c s)
    (hF2 : SecondOrderFriedmann a (fun s => ρ s + vacuumDensity Λ G c s)
      (fun s => p s + vacuumPressure Λ G c s) 0 G c t) :
    ContinuityEquation a ρ p c t ↔ ∂ₜ Λ t = 0 := by
  have hb := energy_balance_of_friedmann hG hc ha hd1 hd2 hdρ hΛ hF1 hF2
  have hk : c ^ 2 / (8 * π * G) ≠ 0 := by
    have := Real.pi_ne_zero
    positivity
  unfold ContinuityEquation
  rw [hb]
  constructor
  · intro h
    exact (mul_eq_zero.mp (neg_eq_zero.mp h)).resolve_right hk
  · intro h
    rw [h, zero_mul, neg_zero]

end Cosmology.FLRW.FriedmannEquation
