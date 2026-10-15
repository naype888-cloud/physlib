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

More generally, `U X_r U⋆ = X_{r ∘ A⁻¹}`, so the little group fixes the bracket as a function
of the direction, `Ω_{H, X_{r ∘ A⁻¹}} = Ω_{H, X_r}`, and the covariances of the positions. The
group velocity lies in the subspace fixed by the little co-group: on the square lattice at a
momentum `(k, k)` the exchange of the axes fixes `χ`, so `Ω_{H, X_x} = Ω_{H, X_y}`.

For instance, on the chain the inversion fixes the momentum `χ(n) = (-1)^n` at the edge of the
Brillouin zone, so there `Ω_HX = 0`, while at a generic momentum `Ω_HX ≠ 0`.

## ii. Key results

- `covariance_ofVec_eq_zero_of_unitary` : in a vector state fixed by a unitary, a fixed and a
  reversed observable are uncorrelated.
- `pointUnitary` : the unitary of a linear symmetry of a region.
- `pointUnitary_hopping`, `pointUnitary_position` : `U H U⋆ = H` and `U X U⋆ = c X`.
- `pointUnitary_characterWave` : the little group of `χ` fixes the plane wave of momentum `χ`.
- `covariance_hopping_position_littleGroup`,
  `expectation_bracket_hopping_position_littleGroup` : `Σ_HX = Ω_HX = 0` in the plane wave of
  `χ` for every direction reversed by the little group of `χ`.
- `covariance_position_position_littleGroup` : a direction fixed and one reversed by the little
  group are uncorrelated.
- `expectation_bracket_hopping_position_of_neg` : at a momentum with `χ(-n) = χ(n)` the bracket
  vanishes along every direction.
- `expectation_bracket_hopping_position_comp_littleGroup` : the little group fixes the bracket,
  `Ω_{H, X_{r ∘ A⁻¹}} = Ω_{H, X_r}`, so it fixes the group velocity.
- `covariance_position_comp_littleGroup` : the little group fixes the covariances of the
  positions.

## iii. Table of contents

- A. Unitary symmetries of vector states
- B. The unitary of a linear symmetry of a region
- C. The little group of a plane wave
- D. The little group fixes the bracket and the covariances

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

/-- A matrix `M` is carried to `M'` by the conjugation by `U` when `M n m = M' (A n) (A m)`. -/
lemma pointUnitary_matrix_eq (M M' : Matrix Λ Λ ℂ)
    (hM : ∀ n m, M n m = M' (regionPerm hΛ n) (regionPerm hΛ m)) :
    (pointUnitary hΛ).conjStarAlgEquiv (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ) M) =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ) M' := by
  refine ContinuousLinearMap.ext fun ψ => ?_
  ext n
  obtain ⟨n, rfl⟩ := (regionPerm hΛ).surjective n
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, pointUnitary_apply,
    Equiv.symm_apply_apply]
  change Matrix.mulVec M _ n = Matrix.mulVec M' _ (regionPerm hΛ n)
  simp only [Matrix.mulVec, dotProduct]
  refine Fintype.sum_equiv (regionPerm hΛ) _ _ fun m => ?_
  change M n m * (pointUnitary hΛ).symm ψ m = M' _ _ * ψ (regionPerm hΛ m)
  rw [pointUnitary_symm_apply, hM n m]

/-- A matrix with `M n m = c M (A n) (A m)` is carried to `c M` by the conjugation by `U`. -/
lemma pointUnitary_matrix (M : Matrix Λ Λ ℂ) (c : ℂ)
    (hM : ∀ n m, M n m = c * M (regionPerm hΛ n) (regionPerm hΛ m)) :
    (pointUnitary hΛ).conjStarAlgEquiv (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ) M) =
      c • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ) M := by
  rw [← map_smul]
  exact pointUnitary_matrix_eq hΛ M (c • M) fun n m => by rw [Matrix.smul_apply, smul_eq_mul, hM]

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

/-- `U X_r U⋆ = X_{r ∘ A⁻¹}`: the unitary moves the direction of a position. -/
lemma pointUnitary_position_comp (r : G →+ ℝ) :
    (pointUnitary hΛ).conjStarAlgEquiv (positionObservable (Λ := Λ) r) =
      (positionObservable (Λ := Λ) (r.comp (A.symm : G →+ G)) : EuclideanSpace ℂ Λ →L[ℂ] _) := by
  refine pointUnitary_matrix_eq hΛ (positionMatrix r) _ fun n m => ?_
  unfold positionMatrix
  by_cases hnm : n = m
  · subst hnm
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, regionPerm_apply]
    simp
  · rw [Matrix.diagonal_apply_ne _ hnm,
      Matrix.diagonal_apply_ne _ ((regionPerm hΛ).injective.ne hnm)]

end Region

/-! ## C. The little group of a plane wave -/

variable (g : PeriodicGraph (Crystal.ofUnitCell G Unit))

namespace PeriodicGraph

omit [DecidableEq G] in
/-- The linear part of a symmetry of a lattice with one site per cell preserves the bonds. -/
lemma adj_linear {s : CellSymmetry G Unit} (hs : s ∈ g.symmetries) (n m : G) :
    g.toSimpleGraph.Adj ⟨s.linear n, ()⟩ ⟨s.linear m, ()⟩ ↔
      g.toSimpleGraph.Adj ⟨n, ()⟩ ⟨m, ()⟩ := by
  have h := (mem_symmetries_iff g s).1 hs () () (m - n)
  rw [add_sub_cancel_right, s.linear.map_sub] at h
  rw [adj_iff_bonded, adj_iff_bonded]
  exact h.symm

end PeriodicGraph

variable [TopologicalSpace G] [DiscreteTopology G]

/-- The plane wave of momentum `χ` on a finite region. -/
noncomputable def characterWave (Λ : Finset G) (χ : BrillouinZone G) : EuclideanSpace ℂ Λ :=
  WithLp.toLp 2 fun n => (χ (Multiplicative.ofAdd (n : G)) : ℂ)

omit [DecidableEq G] [DiscreteTopology G] in
lemma norm_characterWave (Λ : Finset G) (χ : BrillouinZone G) :
    ‖characterWave Λ χ‖ = √(Λ.card : ℝ) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [characterWave]

/-- The plane wave of momentum `χ`, normalized on a nonempty region. -/
noncomputable def unitCharacterWave (Λ : Finset G) (χ : BrillouinZone G) : EuclideanSpace ℂ Λ :=
  ((√(Λ.card : ℝ))⁻¹ : ℝ) • characterWave Λ χ

omit [DecidableEq G] [DiscreteTopology G] in
lemma norm_unitCharacterWave (hne : Λ.Nonempty) (χ : BrillouinZone G) :
    ‖unitCharacterWave Λ χ‖ = 1 := by
  rw [unitCharacterWave, norm_smul, norm_characterWave, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hne.card_pos))

section LittleGroup

variable {g} {s : g.symmetries} {χ : BrillouinZone G} (hs : s ∈ g.littleGroup χ)
  (hΛ : ∀ n, (s : CellSymmetry G Unit).linear n ∈ Λ ↔ n ∈ Λ)
include hs

omit [DecidableEq G] in
/-- **The little group of `χ` fixes the plane wave of momentum `χ`.** -/
lemma pointUnitary_characterWave : pointUnitary hΛ (characterWave Λ χ) = characterWave Λ χ := by
  ext n
  rw [pointUnitary_apply]
  exact congrArg (fun φ : BrillouinZone G => (φ (Multiplicative.ofAdd (n : G)) : ℂ))
    ((g.mem_littleGroup χ s).1 hs)

omit [DecidableEq G] in
lemma pointUnitary_unitCharacterWave :
    pointUnitary hΛ (unitCharacterWave Λ χ) = unitCharacterWave Λ χ := by
  rw [unitCharacterWave, ← Complex.coe_smul, map_smul, pointUnitary_characterWave hs]

variable (hne : Λ.Nonempty) (t : ℝ) {r : G →+ ℝ}
  (hr : ∀ n, r ((s : CellSymmetry G Unit).linear n) = -r n)
include hΛ hr

omit hs [TopologicalSpace G] [DiscreteTopology G] in
lemma pointUnitary_position_neg :
    (pointUnitary hΛ).conjStarAlgEquiv (positionObservable (Λ := Λ) r) =
      -(positionObservable (Λ := Λ) r : EuclideanSpace ℂ Λ →L[ℂ] _) := by
  rw [pointUnitary_position hΛ r (-1) fun n => by rw [hr]; ring, Complex.ofReal_neg,
    Complex.ofReal_one, neg_one_smul]

/-- **In the plane wave of momentum `χ`, the energy and the position along every direction
reversed by the little group of `χ` are uncorrelated.** -/
lemma covariance_hopping_position_littleGroup :
    UnitalPositiveLinearMap.covariance
      (UnitalPositiveLinearMap.ofVec (norm_unitCharacterWave hne χ))
      (hoppingObservable g t) (positionObservable r) = 0 :=
  covariance_ofVec_eq_zero_of_unitary (pointUnitary hΛ) _ (pointUnitary_unitCharacterWave hs hΛ)
    (pointUnitary_hopping hΛ g (g.adj_linear s.2) t) (pointUnitary_position_neg hΛ hr)

/-- **In the plane wave of momentum `χ`, the bracket of the energy and the position along every
direction reversed by the little group of `χ` has expectation zero.** -/
lemma expectation_bracket_hopping_position_littleGroup :
    UnitalPositiveLinearMap.expectation
      (UnitalPositiveLinearMap.ofVec (norm_unitCharacterWave hne χ))
      ⁅hoppingObservable (Λ := Λ) g t, positionObservable r⁆ = 0 :=
  expectation_bracket_ofVec_eq_zero_of_unitary (pointUnitary hΛ) _
    (pointUnitary_unitCharacterWave hs hΛ) (pointUnitary_hopping hΛ g (g.adj_linear s.2) t)
    (pointUnitary_position_neg hΛ hr)

/-- In the plane wave of momentum `χ`, the positions along a direction fixed and one reversed by
the little group of `χ` are uncorrelated. -/
lemma covariance_position_position_littleGroup {r' : G →+ ℝ}
    (hr' : ∀ n, r' ((s : CellSymmetry G Unit).linear n) = r' n) :
    UnitalPositiveLinearMap.covariance
      (UnitalPositiveLinearMap.ofVec (norm_unitCharacterWave hne χ))
      (positionObservable r') (positionObservable r) = 0 := by
  refine covariance_ofVec_eq_zero_of_unitary (pointUnitary hΛ) _
    (pointUnitary_unitCharacterWave hs hΛ) ?_ (pointUnitary_position_neg hΛ hr)
  rw [pointUnitary_position hΛ r' 1 fun n => by rw [hr', one_mul], Complex.ofReal_one, one_smul]

end LittleGroup

omit [DecidableEq G] in
/-- The inversion is in the little group of every momentum with `χ(-n) = χ(n)`. -/
lemma inversion_mem_littleGroup (g : PeriodicGraph (Crystal.ofUnitCell G Unit))
    {χ : BrillouinZone G} (hχ : ∀ n, χ (Multiplicative.ofAdd (-n)) = χ (Multiplicative.ofAdd n)) :
    (⟨PeriodicGraph.inversion, g.inversion_mem_symmetries⟩ : g.symmetries) ∈ g.littleGroup χ := by
  rw [PeriodicGraph.mem_littleGroup]
  ext n
  exact congrArg Subtype.val (hχ (Multiplicative.toAdd n))

/-- **At a momentum with `χ(-n) = χ(n)`, such as the centre or a corner of the Brillouin zone,
the bracket of the energy and the position along every direction has expectation zero** in the
plane wave on every region with `-Λ = Λ`. -/
lemma expectation_bracket_hopping_position_of_neg (g : PeriodicGraph (Crystal.ofUnitCell G Unit))
    {χ : BrillouinZone G} (hχ : ∀ n, χ (Multiplicative.ofAdd (-n)) = χ (Multiplicative.ofAdd n))
    (hΛ : ∀ n, -n ∈ Λ ↔ n ∈ Λ) (hne : Λ.Nonempty) (t : ℝ) (r : G →+ ℝ) :
    UnitalPositiveLinearMap.expectation
      (UnitalPositiveLinearMap.ofVec (norm_unitCharacterWave hne χ))
      ⁅hoppingObservable (Λ := Λ) g t, positionObservable r⁆ = 0 :=
  expectation_bracket_hopping_position_littleGroup (inversion_mem_littleGroup g hχ) hΛ hne t
    fun n => map_neg r n

/-! ## D. The little group fixes the bracket and the covariances -/

section Invariance

variable {g} {s : g.symmetries} {χ : BrillouinZone G} (hs : s ∈ g.littleGroup χ)
  (hΛ : ∀ n, (s : CellSymmetry G Unit).linear n ∈ Λ ↔ n ∈ Λ) (hne : Λ.Nonempty)
include hs hΛ

/-- **The little group of `χ` fixes the energy–position bracket of the plane wave of momentum
`χ`**: `Ω_{H, X_{r ∘ A⁻¹}} = Ω_{H, X_r}` for the linear part `A` of every element of the little
group. In the limit of large cubes this bracket is `-1/2` times the group velocity, so the group
velocity is fixed by the little co-group. -/
lemma expectation_bracket_hopping_position_comp_littleGroup (t : ℝ) (r : G →+ ℝ) :
    UnitalPositiveLinearMap.expectation
      (UnitalPositiveLinearMap.ofVec (norm_unitCharacterWave hne χ))
      ⁅hoppingObservable (Λ := Λ) g t,
        positionObservable (r.comp ((s : CellSymmetry G Unit).linear.symm : G →+ G))⁆ =
    UnitalPositiveLinearMap.expectation
      (UnitalPositiveLinearMap.ofVec (norm_unitCharacterWave hne χ))
      ⁅hoppingObservable (Λ := Λ) g t, positionObservable r⁆ :=
  UnitalPositiveLinearMap.expectation_bracket_eq_of_symm _ (pointUnitary hΛ).conjStarAlgEquiv
    (ofVec_conjStarAlgEquiv _ _ (pointUnitary_unitCharacterWave hs hΛ))
    (pointUnitary_hopping hΛ g (g.adj_linear s.2) t) (pointUnitary_position_comp hΛ r)

/-- **The little group of `χ` fixes the covariances of the positions in the plane wave of
momentum `χ`**: `Σ_{X_{r ∘ A⁻¹}, X_{r' ∘ A⁻¹}} = Σ_{X_r, X_{r'}}`. -/
lemma covariance_position_comp_littleGroup (r r' : G →+ ℝ) :
    UnitalPositiveLinearMap.covariance
      (UnitalPositiveLinearMap.ofVec (norm_unitCharacterWave hne χ))
      (positionObservable (Λ := Λ) (r.comp ((s : CellSymmetry G Unit).linear.symm : G →+ G)))
      (positionObservable (r'.comp ((s : CellSymmetry G Unit).linear.symm : G →+ G))) =
    UnitalPositiveLinearMap.covariance
      (UnitalPositiveLinearMap.ofVec (norm_unitCharacterWave hne χ))
      (positionObservable r) (positionObservable r') :=
  UnitalPositiveLinearMap.covariance_eq_of_symm _ (pointUnitary hΛ).conjStarAlgEquiv
    (ofVec_conjStarAlgEquiv _ _ (pointUnitary_unitCharacterWave hs hΛ))
    (pointUnitary_position_comp hΛ r) (pointUnitary_position_comp hΛ r')

end Invariance

end CondensedMatter.Crystal
