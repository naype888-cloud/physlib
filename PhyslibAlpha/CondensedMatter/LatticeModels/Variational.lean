/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.NormedSpace
/-!

# The variational principle on a finite dimensional Hilbert space

## i. Overview

For a linear map `H` of a finite dimensional complex Hilbert space `E` and a subspace `W`, the
ground energy of `H` on `W` is the infimum of the Rayleigh quotient `Re ⟪ψ, H ψ⟫` over the unit
vectors of `W`. It is bounded below by `-‖H‖`, every unit vector of `W` bounds it above, and it can
only go down when `W` grows. A hopping Hamiltonian on a finite lattice is the case where `E` is the
space of functions on the sites and `W` the functions supported in a smaller region.

## ii. Key results

- `groundEnergy` : the infimum of the Rayleigh quotient over the unit vectors of a subspace.
- `groundEnergy_le` : every unit vector of `W` bounds the ground energy above.
- `neg_opNorm_le_groundEnergy` : the ground energy is at least `-‖H‖`.
- `le_groundEnergy` : a lower bound of the Rayleigh quotient is a lower bound of the ground energy.
- `groundEnergy_anti` : a larger subspace has a lower ground energy.

## iii. Table of contents

- A. The Rayleigh quotient and the ground energy
- B. Bounds

## iv. References

-/

@[expose] public section

namespace CondensedMatter
namespace LatticeModels
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-!

## A. The Rayleigh quotient and the ground energy

-/

/-- The Rayleigh quotient `Re ⟪ψ, H ψ⟫` of `H` at `ψ`. -/
noncomputable def rayleigh (H : E →ₗ[ℂ] E) (ψ : E) : ℝ := RCLike.re ⟪ψ, H ψ⟫_ℂ

/-- The unit vectors of a subspace. -/
def UnitIn (W : Submodule ℂ E) : Type _ := {ψ : E // ψ ∈ W ∧ ‖ψ‖ = 1}

/-- The ground energy of `H` on the subspace `W`: the infimum of the Rayleigh quotient over its unit
vectors. -/
noncomputable def groundEnergy (H : E →ₗ[ℂ] E) (W : Submodule ℂ E) : ℝ :=
  ⨅ ψ : UnitIn W, rayleigh H ψ.1

/-- The operator norm of a linear map of a finite dimensional space. -/
noncomputable def opNorm (H : E →ₗ[ℂ] E) : ℝ := ‖LinearMap.toContinuousLinearMap H‖

/-!

## B. Bounds

-/

/-- The Rayleigh quotient of a unit vector is at least `-‖H‖`. -/
lemma rayleigh_ge (H : E →ₗ[ℂ] E) {ψ : E} (hψ : ‖ψ‖ = 1) : -opNorm H ≤ rayleigh H ψ := by
  have h1 : ‖⟪ψ, H ψ⟫_ℂ‖ ≤ ‖ψ‖ * ‖H ψ‖ := norm_inner_le_norm _ _
  have h2 : ‖H ψ‖ ≤ opNorm H * ‖ψ‖ :=
    (LinearMap.toContinuousLinearMap H).le_opNorm ψ
  have h3 : |RCLike.re ⟪ψ, H ψ⟫_ℂ| ≤ ‖⟪ψ, H ψ⟫_ℂ‖ := RCLike.abs_re_le_norm _
  rw [hψ] at h1 h2
  have := neg_abs_le (RCLike.re ⟪ψ, H ψ⟫_ℂ)
  unfold rayleigh
  linarith

/-- The Rayleigh quotient on the unit vectors of a subspace is bounded below. -/
lemma bddBelow_rayleigh (H : E →ₗ[ℂ] E) (W : Submodule ℂ E) :
    BddBelow (Set.range fun ψ : UnitIn W => rayleigh H ψ.1) :=
  ⟨-opNorm H, by rintro _ ⟨ψ, rfl⟩; exact rayleigh_ge H ψ.2.2⟩

/-- Every unit vector of `W` bounds the ground energy above. -/
lemma groundEnergy_le (H : E →ₗ[ℂ] E) (W : Submodule ℂ E) {ψ : E} (hW : ψ ∈ W)
    (hψ : ‖ψ‖ = 1) : groundEnergy H W ≤ rayleigh H ψ :=
  ciInf_le (bddBelow_rayleigh H W) (⟨ψ, hW, hψ⟩ : UnitIn W)

/-- The ground energy is at least `-‖H‖`. -/
lemma neg_opNorm_le_groundEnergy (H : E →ₗ[ℂ] E) (W : Submodule ℂ E)
    (hne : Nonempty (UnitIn W)) : -opNorm H ≤ groundEnergy H W :=
  le_ciInf fun ψ => rayleigh_ge H ψ.2.2

omit [FiniteDimensional ℂ E] in
/-- A lower bound of the Rayleigh quotient on the unit vectors is a lower bound of the ground
energy. -/
lemma le_groundEnergy (H : E →ₗ[ℂ] E) (W : Submodule ℂ E) (hne : Nonempty (UnitIn W)) {m : ℝ}
    (h : ∀ ψ ∈ W, ‖ψ‖ = 1 → m ≤ rayleigh H ψ) : m ≤ groundEnergy H W :=
  le_ciInf fun ψ => h ψ.1 ψ.2.1 ψ.2.2

/-- A larger subspace has a lower ground energy. -/
lemma groundEnergy_anti (H : E →ₗ[ℂ] E) {W W' : Submodule ℂ E} (hW : W ≤ W')
    (hne : Nonempty (UnitIn W)) : groundEnergy H W' ≤ groundEnergy H W :=
  le_ciInf fun ψ => groundEnergy_le H W' (hW ψ.2.1) ψ.2.2

end LatticeModels
end CondensedMatter
