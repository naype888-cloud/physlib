/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Brillouin
public import PhyslibAlpha.CondensedMatter.Crystal.Inversion

/-!

# The little group of a crystal momentum and the fluctuations of a plane wave

The symmetries in the little group of a momentum `χ` fix the plane wave of momentum `χ`, so they
force entries of the covariance and bracket matrices of that plane wave to vanish.

## i. Overview

A unitary `U` with `U ψ = ψ` fixes the vector state of `ψ` under `x ↦ U x U⋆`, so an observable
fixed by this conjugation and one reversed by it have covariance zero and a bracket of
expectation zero, by `covariance_eq_zero_of_symm`.

On a lattice with one site per cell, let `s` be a bond-preserving symmetry with linear part `A`
and `Λ` a finite region with `A Λ = Λ`. The unitary `(U ψ)(n) = ψ(A⁻¹ n)` fixes the hopping
Hamiltonian `H`, and it reverses the position along `r` when `r ∘ A = -r`. If `s` is in the
little group of `χ`, then `χ ∘ A⁻¹ = χ` and `U` fixes the plane wave `n ↦ χ(n)`. In this plane
wave `H` and the position along every direction reversed by `s` are uncorrelated, with a bracket
of expectation zero. The bracket is `-1/2` times the group velocity in the limit of large cubes,
so this is the vanishing of the components of the group velocity reversed by the little group.

For instance, on the chain the inversion fixes the momentum `χ(n) = (-1)^n` at the edge of the
Brillouin zone, so there `Ω_HX = 0`, while at a generic momentum `Ω_HX ≠ 0`.

## ii. Key results

- `covariance_ofVec_eq_zero_of_unitary` : in a vector state fixed by a unitary, a fixed and a
  reversed observable are uncorrelated.
- `pointUnitary` : the unitary of a linear symmetry of a region.
- `pointUnitary_hopping`, `pointUnitary_position` : `U H U⋆ = H` and `U X U⋆ = c X`.

## iii. Table of contents

- A. Unitary symmetries of vector states
- B. The unitary of a linear symmetry of a region

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.
* M. S. Dresselhaus, G. Dresselhaus & A. Jorio, Group Theory, Chapter 10.

-/

@[expose] public section

namespace CondensedMatter.Crystal

open ProbabilisticTheory
open scoped ComplexOrder InnerProductSpace selfAdjoint

/-! ## A. Unitary symmetries of vector states -/

section Unitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : H ≃ₗᵢ[ℂ] H) {ψ : H} (h : ‖ψ‖ = 1) (hψ : U ψ = ψ)
include hψ

/-- A vector state fixed by a unitary `U` is invariant under `x ↦ U x U⋆`. -/
lemma ofVec_conjStarAlgEquiv (x : H →L[ℂ] H) :
    UnitalPositiveLinearMap.ofVec h (U.conjStarAlgEquiv x) =
      UnitalPositiveLinearMap.ofVec h x := by
  rw [UnitalPositiveLinearMap.ofVec_apply, UnitalPositiveLinearMap.ofVec_apply]
  change ⟪ψ, U (x (U.symm ψ))⟫_ℂ = ⟪ψ, x ψ⟫_ℂ
  rw [U.symm_apply_eq.mpr hψ.symm]
  calc ⟪ψ, U (x ψ)⟫_ℂ = ⟪U ψ, U (x ψ)⟫_ℂ := by rw [hψ]
    _ = ⟪ψ, x ψ⟫_ℂ := U.inner_map_map _ _

variable {a b : Observable (H →L[ℂ] H)} (ha : U.conjStarAlgEquiv a = a)
  (hb : U.conjStarAlgEquiv b = -b)
include ha hb

/-- **In a vector state fixed by a unitary, an observable fixed by it and one reversed by it are
uncorrelated.** -/
lemma covariance_ofVec_eq_zero_of_unitary :
    UnitalPositiveLinearMap.covariance (UnitalPositiveLinearMap.ofVec h) a b = 0 :=
  UnitalPositiveLinearMap.covariance_eq_zero_of_symm _ U.conjStarAlgEquiv
    (ofVec_conjStarAlgEquiv U h hψ) ha hb

/-- In a vector state fixed by a unitary, an observable fixed by it and one reversed by it have
a bracket of expectation zero. -/
lemma expectation_bracket_ofVec_eq_zero_of_unitary :
    UnitalPositiveLinearMap.expectation (UnitalPositiveLinearMap.ofVec h) ⁅a, b⁆ = 0 :=
  UnitalPositiveLinearMap.expectation_bracket_eq_zero_of_symm _ U.conjStarAlgEquiv
    (ofVec_conjStarAlgEquiv U h hψ) ha hb

end Unitary

/-! ## B. The unitary of a linear symmetry of a region -/

attribute [local instance] PeriodicGraph.decidableAdj

variable {G : Type*} [AddCommGroup G] [DecidableEq G] {Λ : Finset G}

section Region

variable {A : G ≃+ G} (hΛ : ∀ n, A n ∈ Λ ↔ n ∈ Λ)

/-- A linear map with `A Λ = Λ` permutes the sites of the region. -/
def regionPerm : Λ ≃ Λ := A.toEquiv.subtypeEquiv fun n => (hΛ n).symm

omit [DecidableEq G] in
lemma regionPerm_apply (n : Λ) : (regionPerm hΛ n : G) = A n := rfl

omit [DecidableEq G] in
lemma regionPerm_symm_apply (n : Λ) : ((regionPerm hΛ).symm n : G) = A.symm n := rfl

/-- The unitary `(U ψ)(n) = ψ(A⁻¹ n)` of a linear map with `A Λ = Λ`. -/
noncomputable def pointUnitary : EuclideanSpace ℂ Λ ≃ₗᵢ[ℂ] EuclideanSpace ℂ Λ :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (regionPerm hΛ)

omit [DecidableEq G] in
lemma pointUnitary_apply (ψ : EuclideanSpace ℂ Λ) (n : Λ) :
    pointUnitary hΛ ψ n = ψ ((regionPerm hΛ).symm n) := rfl

omit [DecidableEq G] in
lemma pointUnitary_symm_apply (ψ : EuclideanSpace ℂ Λ) (n : Λ) :
    (pointUnitary hΛ).symm ψ n = ψ (regionPerm hΛ n) := by
  rw [pointUnitary, LinearIsometryEquiv.piLpCongrLeft_symm]
  rfl

/-- A matrix with `M n m = c M (A n) (A m)` is carried to `c M` by the conjugation by `U`. -/
lemma pointUnitary_matrix (M : Matrix Λ Λ ℂ) (c : ℂ)
    (hM : ∀ n m, M n m = c * M (regionPerm hΛ n) (regionPerm hΛ m)) :
    (pointUnitary hΛ).conjStarAlgEquiv (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ) M) =
      c • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ) M := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  ext n
  obtain ⟨n, rfl⟩ := (regionPerm hΛ).surjective n
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, pointUnitary_apply,
    Equiv.symm_apply_apply, _root_.smul_apply, PiLp.smul_apply]
  change Matrix.mulVec M _ n = c • Matrix.mulVec M _ (regionPerm hΛ n)
  simp only [Matrix.mulVec, dotProduct, smul_eq_mul, Finset.mul_sum]
  refine Fintype.sum_equiv (regionPerm hΛ) _ _ fun m => ?_
  change M n m * (pointUnitary hΛ).symm ψ m = c * (M _ _ * ψ (regionPerm hΛ m))
  rw [pointUnitary_symm_apply, hM n m, mul_assoc]

variable (g : PeriodicGraph (Crystal.ofUnitCell G Unit))

/-- `U H U⋆ = H` when `A` preserves the bonds. -/
lemma pointUnitary_hopping
    (hA : ∀ n m, g.toSimpleGraph.Adj ⟨A n, ()⟩ ⟨A m, ()⟩ ↔ g.toSimpleGraph.Adj ⟨n, ()⟩ ⟨m, ()⟩)
    (t : ℝ) :
    (pointUnitary hΛ).conjStarAlgEquiv (hoppingObservable (Λ := Λ) g t) =
      (hoppingObservable (Λ := Λ) g t : EuclideanSpace ℂ Λ →L[ℂ] _) := by
  have h := pointUnitary_matrix hΛ (hoppingMatrix g t) 1 fun n m => by
    simp only [hoppingMatrix, regionPerm_apply, hA, one_mul]
  rwa [one_smul] at h

/-- `U X U⋆ = c X` for the position along a direction with `r = c (r ∘ A)`. -/
lemma pointUnitary_position (r : G →+ ℝ) (c : ℝ) (hr : ∀ n, r n = c * r (A n)) :
    (pointUnitary hΛ).conjStarAlgEquiv (positionObservable (Λ := Λ) r) =
      (c : ℂ) • (positionObservable (Λ := Λ) r : EuclideanSpace ℂ Λ →L[ℂ] _) := by
  refine pointUnitary_matrix hΛ (positionMatrix r) c fun n m => ?_
  unfold positionMatrix
  by_cases hnm : n = m
  · subst hnm
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, regionPerm_apply, hr n]
    push_cast
    rfl
  · rw [Matrix.diagonal_apply_ne _ hnm,
      Matrix.diagonal_apply_ne _ ((regionPerm hΛ).injective.ne hnm), mul_zero]

end Region

end CondensedMatter.Crystal
