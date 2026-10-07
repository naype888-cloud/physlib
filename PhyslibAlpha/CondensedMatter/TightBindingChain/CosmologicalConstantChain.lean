/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.EntropyCurvature
public import PhyslibAlpha.CondensedMatter.TightBindingChain.LinkPuncture
/-!

# The cosmological constant in one line

## i. Overview

`HorizonCount`, `LinkPuncture` and `EntropyCurvature` each read the cosmological constant
`Λ = 3 π / (ℓ² log W)` counted on a cut of the open tight binding chain in one way. This file
puts the readings in one statement.

On four sites, with `2 g` quanta on the `M = 2` bonds across the first cut, `W = 2^{2g}` and

`Λ = 3 π / (ℓ² log W) = 3 π / (ℓ² 2 g log 2) = 12 π / A = 6 π² / (ℓ² log 2 (4 π - ∫ K dA))`,

with `A` the area of `2 g` lowest loop quantum gravity quanta at the Bekenstein–Hawking value of
the Immirzi parameter, and `∫ K dA` the total curvature of a closed surface of genus `g`
(defined by the Gauss–Bonnet formula, see `surfaceCurvature`). The horizon of `Λ` has entropy
`log W`, `Λ` is positive, and the de Sitter scale factor of `Λ` solves both Friedmann equations.

## ii. Key results

- `countCosmologicalConstant_eq_surfaceCurvature` : on any cut, with `2 g` quanta,
  `Λ = 6 π² / (ℓ² log M (4 π - ∫ K dA))`.
- `countCosmologicalConstant_chain` : the full chain on four sites.

## iii. Table of contents

- A. The constant and the curvature
- B. The chain

## iv. References

* A. Ashtekar, J. Baez, A. Corichi and K. Krasnov, *Quantum geometry and black hole entropy*,
  Phys. Rev. Lett. 80 (1998) 904–907.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain

open Real LoopQuantumGravity Cosmology.FLRW.FriedmannEquation

variable (T : TightBindingChain)

/-!

## A. The constant and the curvature

-/

/-- With `2 g` quanta on the `M` bonds across a cut,
`Λ = 6 π² / (ℓ² log M (4 π - ∫ K dA))` for the total curvature of a surface of genus `g`. -/
theorem countCosmologicalConstant_eq_surfaceCurvature (c g : ℕ) (ℓ : ℝ) :
    T.countCosmologicalConstant c (2 * g) ℓ =
      6 * π ^ 2 /
        (ℓ ^ 2 * Real.log (T.cutBonds c).card * (4 * π - surfaceCurvature g)) := by
  rw [countCosmologicalConstant, entropyCosmologicalConstant, cutEntropy_eq_surfaceCurvature]
  rw [div_mul_eq_mul_div, mul_div_assoc', div_div_eq_mul_div]
  ring

/-!

## B. The chain

-/

/-- **The cosmological constant in one line.** On four sites, with `2 g ≥ 2` quanta on the first
cut and `ℓ ≠ 0`, the counted constant `Λ` satisfies
`Λ = 3 π / (ℓ² log W) = 3 π / (ℓ² 2 g log 2) = 12 π / A = 6 π² / (ℓ² log 2 (4 π - ∫ K dA))`,
its horizon has entropy `log W`, it is positive, and its de Sitter scale factor solves both
Friedmann equations. -/
theorem countCosmologicalConstant_chain (hN : T.N = 4) {g : ℕ} (hg : 1 ≤ g) {ℓ : ℝ}
    (hℓ : ℓ ≠ 0) :
    let Λ := T.countCosmologicalConstant 0 (2 * g) ℓ
    Λ = 3 * π / (ℓ ^ 2 * T.cutEntropy 0 (2 * g)) ∧
      Λ = 3 * π / (ℓ ^ 2 * ((2 * g : ℕ) * Real.log 2)) ∧
      Λ = 12 * π / surfaceArea ℓ (Real.log 2 / (π * √3)) (List.replicate (2 * g) (1 / 2)) ∧
      Λ = 6 * π ^ 2 / (ℓ ^ 2 * Real.log 2 * (4 * π - surfaceCurvature g)) ∧
      deSitterEntropy Λ ℓ = T.cutEntropy 0 (2 * g) ∧
      0 < Λ ∧
      ∀ {a₀ σ G c' : ℝ}, a₀ ≠ 0 → (σ = 1 ∨ σ = -1) → ∀ t : Time,
        FirstOrderFriedmann (deSitterScaleFactor a₀ σ Λ c') (fun _ => 0) 0 Λ G c' t ∧
          SecondOrderFriedmann (deSitterScaleFactor a₀ σ Λ c') (fun _ => 0) (fun _ => 0)
            Λ G c' t := by
  have hk : 1 ≤ 2 * g := by omega
  have hM : 2 ≤ (T.cutBonds 0).card := (T.card_cutBonds_zero_of_four hN).ge
  have h2 : ((T.cutBonds 0).card : ℝ) = 2 := by exact_mod_cast T.card_cutBonds_zero_of_four hN
  refine ⟨rfl, ?_, T.countCosmologicalConstant_eq_div_surfaceArea hN hk hℓ, ?_,
    T.deSitterEntropy_countCosmologicalConstant hk hM hℓ,
    T.countCosmologicalConstant_pos hk hM hℓ, fun ha₀ hσ t =>
    ⟨T.countCosmologicalConstant_firstOrderFriedmann hk hM hℓ ha₀ hσ t,
      T.countCosmologicalConstant_secondOrderFriedmann hk hM hℓ ha₀ hσ t⟩⟩
  · rw [countCosmologicalConstant, entropyCosmologicalConstant, cutEntropy, h2]
  · rw [countCosmologicalConstant_eq_surfaceCurvature, h2]

end TightBindingChain
end CondensedMatter
