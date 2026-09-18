/-
Copyright (c) 2026 Eduardo Nava-Hernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernández, José Arturo Nava-Hernández, Gerardo Gabriel Nava Gómez
-/
module

public import PhyslibAlpha.AlgebraicFramework.CStarAlgebra.DimUncertainty.D8_Szego

/-!
# Transport of the asymptotic defect to closed surfaces

This file isolates the finite-sum step which transports the universal asymptotic defect
`Gnomon.deltaInf` to a closed orientable surface of genus `g`.  The topological input is the
standard identity `b₁(Σ_g) = 2g`; the analytic input is the closed form for `deltaInf` proved
in `D8_Szego`.
-/

@[expose] public section

noncomputable section

open Real

namespace Gnomon

/-- Sum of the defects carried by a family of `b₁` independent cycles. -/
def cycleDefectSum (b₁ : ℕ) (defect : Fin b₁ → ℝ) : ℝ :=
  ∑ i, defect i

/-- A constant defect on every independent cycle sums to `b₁ * defect`. -/
theorem cycleDefectSum_of_constant (b₁ : ℕ) (defect : Fin b₁ → ℝ) (c : ℝ)
    (hdefect : ∀ i, defect i = c) :
    cycleDefectSum b₁ defect = (b₁ : ℝ) * c := by
  simp [cycleDefectSum, hdefect]

/-- Surface defect obtained by assigning `deltaInf` to each of the `2g` generators of the first
homology of a closed orientable surface of genus `g`. -/
def closedSurfaceDefect (g : ℕ) : ℝ :=
  cycleDefectSum (2 * g) fun _ => deltaInf

/-- Transport through the first Betti number `b₁(Σ_g) = 2g`. -/
theorem closedSurfaceDefect_eq_firstBetti_mul (g : ℕ) :
    closedSurfaceDefect g = ((2 * g : ℕ) : ℝ) * deltaInf := by
  exact cycleDefectSum_of_constant (2 * g) (fun _ => deltaInf) deltaInf fun _ => rfl

/-- Closed genus form: `Ω(Σ_g) = 2g δ_∞`. -/
theorem closedSurfaceDefect_eq_two_mul_genus_mul (g : ℕ) :
    closedSurfaceDefect g = 2 * (g : ℝ) * deltaInf := by
  rw [closedSurfaceDefect_eq_firstBetti_mul]
  push_cast
  rfl

/-- The asymptotic defect in the equivalent closed form shown in the surface formula. -/
theorem deltaInf_closed_form :
    deltaInf = Real.sqrt ((π ^ 2 - 6) / 3) - 1 := by
  unfold deltaInf Cinf
  congr 2
  ring

/-- Fully expanded closed form for the defect of a genus-`g` surface. -/
theorem closedSurfaceDefect_closed_form (g : ℕ) :
    closedSurfaceDefect g =
      2 * (g : ℝ) * (Real.sqrt ((π ^ 2 - 6) / 3) - 1) := by
  rw [closedSurfaceDefect_eq_two_mul_genus_mul, deltaInf_closed_form]

/-- The four-step transport displayed in the closed-surface formula. -/
theorem closedSurface_transport_chain (g : ℕ) :
    closedSurfaceDefect g =
        cycleDefectSum (2 * g) (fun _ => deltaInf) ∧
      cycleDefectSum (2 * g) (fun _ => deltaInf) = ((2 * g : ℕ) : ℝ) * deltaInf ∧
      ((2 * g : ℕ) : ℝ) * deltaInf = 2 * (g : ℝ) * deltaInf ∧
      deltaInf = Real.sqrt ((π ^ 2 - 6) / 3) - 1 := by
  refine ⟨rfl, closedSurfaceDefect_eq_firstBetti_mul g, ?_, deltaInf_closed_form⟩
  push_cast
  rfl

end Gnomon
