/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Physlib.Cosmology.FLRW.Solutions
/-!

# The horizon of the de Sitter solution

## i. Overview

The de Sitter solution `deSitterScaleFactor` of `Physlib.Cosmology.FLRW.Solutions` has the
constant Hubble parameter `H = σ √(Λ/3) c`. Its horizon is the sphere of radius
`r = √(3/Λ) = c / |H|`, of area `A = 12 π / Λ`. Given a length `ℓ > 0` (the Planck length), the
horizon entropy in units of the Boltzmann constant is `S = A / (4 ℓ²) = 3 π / (ℓ² Λ)`.

Read backwards, this fixes the cosmological constant by the entropy: `Λ = 3 π / (ℓ² S)`. For
every `S > 0` the de Sitter scale factor with this `Λ` solves both Friedmann equations and has
horizon entropy exactly `S`, and the Hubble parameter obeys `H² = π c² / (ℓ² S)`. The
cosmological constant is strictly decreasing in the entropy.

## ii. Key results

- `deSitterHorizonRadius`, `deSitterHorizonArea`, `deSitterEntropy`: `r`, `A` and `S`.
- `deSitterHorizonRadius_eq_div_abs_hubbleConstant`: `r = c / |H|`.
- `deSitterEntropy_eq`: `S = 3 π / (ℓ² Λ)`.
- `cosmologicalConstant_eq_of_deSitterEntropy`: `Λ = 3 π / (ℓ² S)`.
- `deSitterEntropy_entropyCosmologicalConstant`: the constant `3 π / (ℓ² S)` has entropy `S`.
- `entropyCosmologicalConstant_firstOrderFriedmann`,
  `entropyCosmologicalConstant_secondOrderFriedmann`: it gives a solution of both Friedmann
  equations.
- `sq_hubbleConstant_entropyCosmologicalConstant`: `H² = π c² / (ℓ² S)`.
- `entropyCosmologicalConstant_strictAntiOn`: `Λ` is strictly decreasing in `S`.

## iii. Table of contents

- A. The horizon
- B. The horizon entropy
- C. The cosmological constant fixed by the entropy

## iv. References

- G. W. Gibbons and S. W. Hawking, *Cosmological event horizons, thermodynamics, and particle
  creation*, Phys. Rev. D 15 (1977) 2738.

-/

@[expose] public section

namespace Cosmology.FLRW.FriedmannEquation

open Real Time

/-!

## A. The horizon

-/

/-- The radius `√(3/Λ)` of the horizon of the de Sitter solution. -/
noncomputable def deSitterHorizonRadius (Λ : ℝ) : ℝ := √(3 / Λ)

/-- The area `4 π r²` of the horizon of the de Sitter solution. -/
noncomputable def deSitterHorizonArea (Λ : ℝ) : ℝ := 4 * π * deSitterHorizonRadius Λ ^ 2

lemma deSitterHorizonArea_eq {Λ : ℝ} (hΛ : 0 < Λ) : deSitterHorizonArea Λ = 12 * π / Λ := by
  rw [deSitterHorizonArea, deSitterHorizonRadius, Real.sq_sqrt (by positivity)]
  ring

/-- The horizon radius is the Hubble radius `c / |H|` of the de Sitter solution. -/
lemma deSitterHorizonRadius_eq_div_abs_hubbleConstant {a₀ σ Λ c : ℝ} (hΛ : 0 < Λ) (hc : 0 < c)
    (ha₀ : a₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    deSitterHorizonRadius Λ = c / |hubbleConstant (deSitterScaleFactor a₀ σ Λ c) t| := by
  have habs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hs : 0 < √(Λ / 3) := Real.sqrt_pos.mpr (by positivity)
  rw [hubbleConstant_deSitterScaleFactor ha₀, abs_mul, abs_mul, habs, abs_of_pos hs,
    abs_of_pos hc, deSitterHorizonRadius, one_mul, div_mul_cancel_right₀ hc.ne',
    Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_div' _ hΛ.le, inv_div]

/-!

## B. The horizon entropy

-/

/-- The horizon entropy `A / (4 ℓ²)` of the de Sitter solution in units of the Boltzmann
  constant, for the length `ℓ` (the Planck length). -/
noncomputable def deSitterEntropy (Λ ℓ : ℝ) : ℝ := deSitterHorizonArea Λ / (4 * ℓ ^ 2)

lemma deSitterEntropy_eq {Λ ℓ : ℝ} (hΛ : 0 < Λ) :
    deSitterEntropy Λ ℓ = 3 * π / (ℓ ^ 2 * Λ) := by
  rw [deSitterEntropy, deSitterHorizonArea_eq hΛ]
  rcases eq_or_ne ℓ 0 with rfl | hℓ
  · simp
  · field_simp
    ring

lemma deSitterEntropy_pos {Λ ℓ : ℝ} (hΛ : 0 < Λ) (hℓ : ℓ ≠ 0) : 0 < deSitterEntropy Λ ℓ := by
  rw [deSitterEntropy_eq hΛ]
  positivity

/-- The cosmological constant is fixed by the horizon entropy: `Λ = 3 π / (ℓ² S)`. -/
lemma cosmologicalConstant_eq_of_deSitterEntropy {Λ ℓ : ℝ} (hΛ : 0 < Λ) (hℓ : ℓ ≠ 0) :
    Λ = 3 * π / (ℓ ^ 2 * deSitterEntropy Λ ℓ) := by
  rw [deSitterEntropy_eq hΛ]
  field_simp

/-!

## C. The cosmological constant fixed by the entropy

-/

/-- The cosmological constant `3 π / (ℓ² S)` of a de Sitter horizon of entropy `S`. -/
noncomputable def entropyCosmologicalConstant (S ℓ : ℝ) : ℝ := 3 * π / (ℓ ^ 2 * S)

lemma entropyCosmologicalConstant_pos {S ℓ : ℝ} (hS : 0 < S) (hℓ : ℓ ≠ 0) :
    0 < entropyCosmologicalConstant S ℓ := by
  unfold entropyCosmologicalConstant
  positivity

lemma deSitterEntropy_entropyCosmologicalConstant {S ℓ : ℝ} (hS : 0 < S) (hℓ : ℓ ≠ 0) :
    deSitterEntropy (entropyCosmologicalConstant S ℓ) ℓ = S := by
  rw [deSitterEntropy_eq (entropyCosmologicalConstant_pos hS hℓ), entropyCosmologicalConstant]
  field_simp

lemma entropyCosmologicalConstant_firstOrderFriedmann {a₀ σ S ℓ G c : ℝ} (hS : 0 < S)
    (hℓ : ℓ ≠ 0) (ha₀ : a₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    FirstOrderFriedmann (deSitterScaleFactor a₀ σ (entropyCosmologicalConstant S ℓ) c)
      (fun _ => 0) 0 (entropyCosmologicalConstant S ℓ) G c t :=
  deSitterScaleFactor_firstOrderFriedmann (entropyCosmologicalConstant_pos hS hℓ) ha₀ hσ t

lemma entropyCosmologicalConstant_secondOrderFriedmann {a₀ σ S ℓ G c : ℝ} (hS : 0 < S)
    (hℓ : ℓ ≠ 0) (ha₀ : a₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    SecondOrderFriedmann (deSitterScaleFactor a₀ σ (entropyCosmologicalConstant S ℓ) c)
      (fun _ => 0) (fun _ => 0) (entropyCosmologicalConstant S ℓ) G c t :=
  deSitterScaleFactor_secondOrderFriedmann (entropyCosmologicalConstant_pos hS hℓ) ha₀ hσ t

/-- The Hubble parameter of a de Sitter horizon of entropy `S` obeys `H² = π c² / (ℓ² S)`. -/
lemma sq_hubbleConstant_entropyCosmologicalConstant {a₀ σ S ℓ c : ℝ} (hS : 0 < S)
    (hℓ : ℓ ≠ 0) (ha₀ : a₀ ≠ 0) (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    hubbleConstant (deSitterScaleFactor a₀ σ (entropyCosmologicalConstant S ℓ) c) t ^ 2 =
      π * c ^ 2 / (ℓ ^ 2 * S) := by
  rw [hubbleConstant_deSitterScaleFactor ha₀,
    sq_deSitterRate (entropyCosmologicalConstant_pos hS hℓ).le hσ, entropyCosmologicalConstant]
  field_simp

/-- The cosmological constant of a de Sitter horizon is strictly decreasing in its entropy. -/
lemma entropyCosmologicalConstant_strictAntiOn {ℓ : ℝ} (hℓ : ℓ ≠ 0) :
    StrictAntiOn (fun S => entropyCosmologicalConstant S ℓ) (Set.Ioi 0) := by
  intro S₁ hS₁ S₂ _ h
  have hS₁ : (0 : ℝ) < S₁ := hS₁
  simp only [entropyCosmologicalConstant]
  gcongr

end Cosmology.FLRW.FriedmannEquation
