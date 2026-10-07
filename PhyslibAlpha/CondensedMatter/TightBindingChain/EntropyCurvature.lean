/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.CutCycles
/-!

# The entropy of a surface counts its curvature

## i. Overview

A closed orientable surface `Σ_g` of genus `g` has `2 g` independent cycles, and by the
Gauss–Bonnet theorem its total curvature is `∫ K dA = 2 π χ(Σ_g) = 2 π (2 - 2 g)`. Gauss–Bonnet
is not formalized in Mathlib, so here the total curvature of `Σ_g` is defined by that formula.

`2 g` bonds across a cut of the open tight binding chain give a bond graph with `2 g`
independent cycles, as many as `Σ_g` (`cycleRank_bondGraph`). Placing `2 g` quanta on the `M`
bonds across the cut, Boltzmann–Planck `S = log W` with `W = M^{2g}` and the Gauss–Bonnet
curvature of `Σ_g` give one line: `S = (log M / 2 π)(4 π - ∫ K dA)`. Each handle adds `2 log M` of
entropy and `-4 π` of curvature.

## ii. Key results

- `surfaceCurvature` : the total curvature `2 π (2 - 2 g)` of `Σ_g` (Gauss–Bonnet).
- `cycleRank_bondGraph_two_mul` : `2 g` bonds across the cut give `2 g` independent cycles.
- `cutEntropy_eq_surfaceCurvature` : `S = (log M / 2 π)(4 π - ∫ K dA)`.
- `cutEntropy_handle_step` : one handle adds `2 log M` of entropy and `-4 π` of curvature.

## iii. Table of contents

- A. The curvature of a closed surface
- B. The entropy counts the curvature

## iv. References

* M. do Carmo, *Differential Geometry of Curves and Surfaces*, Prentice Hall (1976), §4-5.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain

open Real

/-!

## A. The curvature of a closed surface

-/

/-- The total curvature `∫ K dA = 2 π χ(Σ_g) = 2 π (2 - 2 g)` of a closed orientable surface of
genus `g`, as given by the Gauss–Bonnet theorem. -/
noncomputable def surfaceCurvature (g : ℕ) : ℝ := 2 * π * (2 - 2 * g)

/-- One handle lowers the total curvature by `4 π`. -/
lemma surfaceCurvature_succ (g : ℕ) : surfaceCurvature (g + 1) = surfaceCurvature g - 4 * π := by
  simp only [surfaceCurvature]
  push_cast
  ring

/-!

## B. The entropy counts the curvature

-/

variable (T : TightBindingChain)

/-- `2 g` bonds across the cut give a bond graph with `2 g` independent cycles, as many as a
closed surface of genus `g`. -/
lemma cycleRank_bondGraph_two_mul {c g : ℕ} {S : Finset (Fin T.N × Fin T.N)}
    (hS : S ∈ (T.cutBonds c).powersetCard (2 * g)) : cycleRank (bondGraph S) = 2 * g := by
  rw [Finset.mem_powersetCard] at hS
  rw [T.cycleRank_bondGraph hS.1, hS.2]

/-- **The entropy of a surface counts its curvature**: `2 g` quanta on the bonds across the cut
have the entropy `S = (log M / 2 π)(4 π - ∫ K dA)` of the curvature of `Σ_g`. -/
theorem cutEntropy_eq_surfaceCurvature (c g : ℕ) :
    T.cutEntropy c (2 * g) =
      Real.log (T.cutBonds c).card / (2 * π) * (4 * π - surfaceCurvature g) := by
  rw [cutEntropy, surfaceCurvature]
  field_simp
  push_cast
  ring

/-- **One handle**: `2 log M` more entropy and `4 π` less curvature. -/
theorem cutEntropy_handle_step (c g : ℕ) :
    T.cutEntropy c (2 * (g + 1)) - T.cutEntropy c (2 * g) = 2 * Real.log (T.cutBonds c).card ∧
      surfaceCurvature (g + 1) - surfaceCurvature g = -(4 * π) := by
  refine ⟨?_, by rw [surfaceCurvature_succ]; ring⟩
  simp only [cutEntropy]
  push_cast
  ring

end TightBindingChain
end CondensedMatter
