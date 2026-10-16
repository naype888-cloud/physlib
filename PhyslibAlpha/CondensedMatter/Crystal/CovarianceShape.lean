/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.CovarianceForm
public import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.Monoclinic
public import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.Rhombohedral

/-!

# How the point group shapes the covariance matrix

The point group of a crystal restricts the matrix of covariances of a vector of observables in a
state with that symmetry.

## i. Overview

Let `a = (a₀, a₁, a₂)` be observables along three orthonormal axes, for instance the three
components of the position or of the current. A point operation with orthogonal matrix `R` acts
by `a_i ↦ ∑ⱼ R i j aⱼ`. If a `⋆`-automorphism realises this action and fixes the state `ω`, the
matrix `M_ij = C(a_i, a_j)` of the covariance form, which contains both the covariance matrix `Σ`
and the commutator matrix `Ω` of Robertson's relation as `M = Σ + i Ω`, satisfies `Rᴴ M R = M`
(`AlgState.conjTranspose_mul_covarianceMatrixForm_mul`). The point operations used here have
integer matrices in Cartesian axes:

- **triclinic**: only the inversion, which acts on `M` trivially, so `M` is free;
- **monoclinic**: the reflection `b ↦ -b` separates the axis `b` from the plane of `a` and `c`,
  and leaves a free `2 × 2` block in that plane;
- **orthorhombic**: the reflections in the coordinate planes make `M` diagonal;
- **rhombohedral**: with primitive vectors `(p, q, q)`, `(q, p, q)`, `(q, q, p)`, the point
  operations permute the three Cartesian axes, possibly with the inversion. Then
  `M = α 1 + β (J - 1)` with `J` the matrix of ones: one value along the threefold axis
  `(1, 1, 1)` and another one across it;
- **cubic**: the cubic lattices and diamond have in addition the reflection `x ↦ -x`, which
  forces `M = α 1`.

The covariance of a symmetric observable `b`, such as the Hamiltonian, with the vector `a` is a
row `m` with `m R = m`. For a rhombohedral state it lies along the threefold axis, and when the
inversion is a symmetry it vanishes.

In the hexagonal plane of the honeycomb, the rotation by `2π / 3` alone gives
`M = [[α, β], [-β, α]]`. For a Hermitian `M` this means `Σ = α 1` and
`Ω = Im β · [[0, 1], [-1, 0]]`: the rotation leaves room for a commutator between the two
components, and a reflection kills it.

## ii. Key results

- `AlgState.conjTranspose_pointMatrix_mul` : `Rᴴ M R = M` for a point operation given by its
  integer matrix.
- `AlgState.covarianceMatrixForm_monoclinic` : the axis `b` decouples from `a` and `c`.
- `AlgState.covarianceMatrixForm_orthorhombic` : `M` is diagonal.
- `AlgState.covarianceMatrixForm_rhombohedral` : `M = α 1 + β (J - 1)`.
- `AlgState.covarianceMatrixForm_cubic` : `M = α 1`.
- `AlgState.covarianceForm_rhombohedral_vector` : the covariance of a symmetric observable with
  the vector is along `(1, 1, 1)`.
- `AlgState.covarianceForm_vector_eq_zero_of_inversion` : it vanishes under the inversion.
- `AlgState.covarianceMatrixForm_rotation` and `AlgState.covarianceMatrixForm_rotation_reflection` :
  the hexagonal plane.

## iii. Table of contents

- A. Point operations on a vector of observables
- B. Orthorhombic, rhombohedral and cubic shapes
- C. A symmetric observable against the vector
- D. The hexagonal plane

## iv. References

* E. Wigner, Group Theory and its Application to the Quantum Mechanics of Atomic Spectra,
  Chapter 21.
* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace ProbabilisticTheory

namespace AlgState

open Matrix CondensedMatter.Crystal

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A] (ω : AlgState A)

/-! ## A. Point operations on a vector of observables -/

/-- The matrix of the point operation sending the `i`-th axis to `v i`, acting on rows. -/
def pointMatrix (v : Fin 3 → Fin 3 → ℤ) : Matrix (Fin 3) (Fin 3) ℂ := of fun i j => (v j i : ℂ)

/-- The point operation `v` is realised on the vector `a` by a `⋆`-automorphism fixing `ω`. -/
def Realises (a : Fin 3 → A) (v : Fin 3 → Fin 3 → ℤ) : Prop :=
  ∃ σ : A ≃⋆ₐ[ℂ] A, (∀ x, ω (σ x) = ω x) ∧ ∀ i, σ (a i) = ∑ j, (v i j : ℂ) • a j

variable {ω}

/-- **A realised point operation preserves the covariance matrix**: `Rᴴ M R = M`. -/
lemma conjTranspose_pointMatrix_mul {a : Fin 3 → A} {v : Fin 3 → Fin 3 → ℤ}
    (h : ω.Realises a v) :
    (pointMatrix v)ᴴ * ω.covarianceMatrixForm a a * pointMatrix v = ω.covarianceMatrixForm a a := by
  obtain ⟨σ, hσ, ha⟩ := h
  exact ω.conjTranspose_mul_covarianceMatrixForm_mul σ hσ ha ha

/-- The entries of `Rᴴ M R = M` for an explicit integer matrix. -/
lemma entry_of_realises {a : Fin 3 → A} {v : Fin 3 → Fin 3 → ℤ} (h : ω.Realises a v)
    (i j : Fin 3) : ∑ k, ∑ l, (v i k : ℂ) * ω.covarianceForm (a k) (a l) * v j l =
      ω.covarianceForm (a i) (a j) := by
  have e := congrFun (congrFun (conjTranspose_pointMatrix_mul h) i) j
  simp only [mul_apply, conjTranspose_apply, pointMatrix, of_apply, covarianceMatrixForm,
    star_intCast, Finset.sum_mul] at e
  rw [← e, Finset.sum_comm]

/-! ## B. Orthorhombic, rhombohedral and cubic shapes -/

/-- **Monoclinic symmetry decouples the axis `b`**: the reflection `b ↦ -b` makes the
covariances between `b` and the plane of `a` and `c` vanish, both `Σ` and `Ω`. The block in the
plane of `a` and `c` stays free. -/
lemma covarianceMatrixForm_monoclinic {a : Fin 3 → A}
    (h : ∀ v ∈ monoclinicPointTriples, ω.Realises a v) {i : Fin 3} (hi : i ≠ 1) :
    ω.covarianceForm (a i) (a 1) = 0 ∧ ω.covarianceForm (a 1) (a i) = 0 := by
  have hm := entry_of_realises (h ![![1, 0, 0], ![0, -1, 0], ![0, 0, 1]] (by decide))
  obtain rfl | rfl : i = 0 ∨ i = 2 := by fin_cases i <;> simp_all
  · have e1 := hm 0 1
    have e2 := hm 1 0
    simp [Fin.sum_univ_three] at e1 e2
    exact ⟨by linear_combination -e1 / 2, by linear_combination -e2 / 2⟩
  · have e1 := hm 2 1
    have e2 := hm 1 2
    simp [Fin.sum_univ_three] at e1 e2
    exact ⟨by linear_combination -e1 / 2, by linear_combination -e2 / 2⟩

/-- **Orthorhombic symmetry makes the covariance matrix diagonal.** -/
lemma covarianceMatrixForm_orthorhombic {a : Fin 3 → A}
    (h : ∀ v ∈ orthorhombicPointTriples, ω.Realises a v) {i j : Fin 3} (hij : i ≠ j) :
    ω.covarianceForm (a i) (a j) = 0 := by
  have hx := entry_of_realises (h ![![-1, 0, 0], ![0, 1, 0], ![0, 0, 1]] (by decide))
  have hy := entry_of_realises (h ![![1, 0, 0], ![0, -1, 0], ![0, 0, 1]] (by decide))
  fin_cases i <;> fin_cases j <;> simp at hij
  · show ω.covarianceForm (a 0) (a 1) = 0
    have e := hx 0 1; simp [Fin.sum_univ_three] at e; linear_combination -e / 2
  · show ω.covarianceForm (a 0) (a 2) = 0
    have e := hx 0 2; simp [Fin.sum_univ_three] at e; linear_combination -e / 2
  · show ω.covarianceForm (a 1) (a 0) = 0
    have e := hx 1 0; simp [Fin.sum_univ_three] at e; linear_combination -e / 2
  · show ω.covarianceForm (a 1) (a 2) = 0
    have e := hy 1 2; simp [Fin.sum_univ_three] at e; linear_combination -e / 2
  · show ω.covarianceForm (a 2) (a 0) = 0
    have e := hx 2 0; simp [Fin.sum_univ_three] at e; linear_combination -e / 2
  · show ω.covarianceForm (a 2) (a 1) = 0
    have e := hy 2 1; simp [Fin.sum_univ_three] at e; linear_combination -e / 2

/-- **Rhombohedral symmetry makes the covariance matrix uniaxial**: all diagonal entries are
equal, and all off-diagonal entries are equal. -/
lemma covarianceMatrixForm_rhombohedral {a : Fin 3 → A}
    (h : ∀ v ∈ rhombohedralPointTriples, ω.Realises a v) :
    ∃ α β : ℂ, ∀ i j, ω.covarianceForm (a i) (a j) = if i = j then α else β := by
  have hc := entry_of_realises (h ![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]] (by decide))
  have hs := entry_of_realises (h ![![0, 1, 0], ![1, 0, 0], ![0, 0, 1]] (by decide))
  have c00 := hc 0 0; have c11 := hc 1 1; have c01 := hc 0 1; have c12 := hc 1 2
  have c10 := hc 1 0; have c21 := hc 2 1; have s01 := hs 0 1
  simp [Fin.sum_univ_three] at c00 c11 c01 c12 c10 c21 s01
  refine ⟨ω.covarianceForm (a 0) (a 0), ω.covarianceForm (a 0) (a 1), fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;> simp <;> grind

/-- **Cubic symmetry makes the covariance matrix scalar.** The point group of the cubic lattices
and of diamond contains the permutations of the axes and the reflection `x ↦ -x`. -/
lemma covarianceMatrixForm_cubic {a : Fin 3 → A}
    (h : ∀ v ∈ rhombohedralPointTriples, ω.Realises a v)
    (hx : ω.Realises a ![![-1, 0, 0], ![0, 1, 0], ![0, 0, 1]]) :
    ∃ α : ℂ, ∀ i j, ω.covarianceForm (a i) (a j) = if i = j then α else 0 := by
  obtain ⟨α, β, hαβ⟩ := covarianceMatrixForm_rhombohedral h
  have e := entry_of_realises hx 0 1
  simp [Fin.sum_univ_three, hαβ] at e
  have hβ : β = 0 := by linear_combination -e / 2
  exact ⟨α, fun i j => by rw [hαβ, hβ]⟩

/-! ## C. A symmetric observable against the vector -/

/-- A symmetric observable has the same covariance with `a i` as with its image. -/
lemma covarianceForm_vector_of_realises {a : Fin 3 → A} {b : A} {v : Fin 3 → Fin 3 → ℤ}
    (σ : A ≃⋆ₐ[ℂ] A) (hσ : ∀ x, ω (σ x) = ω x) (hb : σ b = b)
    (ha : ∀ i, σ (a i) = ∑ j, (v i j : ℂ) • a j) (i : Fin 3) :
    ∑ j, (v i j : ℂ) * ω.covarianceForm b (a j) = ω.covarianceForm b (a i) := by
  rw [← ω.covarianceForm_map σ hσ b (a i), hb, ha, covarianceForm_sum_right]
  simp only [covarianceForm_smul_right]

/-- **Under the inversion the covariance of a symmetric observable with the vector vanishes.**
This holds for both parts, `Cov(b, a i) = 0` and `ω⟨⁅b, a i⁆⟩ = 0`. -/
lemma covarianceForm_vector_eq_zero_of_inversion {a : Fin 3 → A} {b : A} (σ : A ≃⋆ₐ[ℂ] A)
    (hσ : ∀ x, ω (σ x) = ω x) (hb : σ b = b) (ha : ∀ i, σ (a i) = -a i) (i : Fin 3) :
    ω.covarianceForm b (a i) = 0 :=
  ω.covarianceForm_eq_zero_of_neg σ hσ hb (ha i)

/-- **For a rhombohedral state the covariance of a symmetric observable with the vector lies along
the threefold axis**: it is the same for the three components. The cyclic permutation of the
axes is enough. -/
lemma covarianceForm_rhombohedral_vector {a : Fin 3 → A} {b : A} (σ : A ≃⋆ₐ[ℂ] A)
    (hσ : ∀ x, ω (σ x) = ω x) (hb : σ b = b)
    (ha : ∀ i, σ (a i) = ∑ j, ((![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]] : Fin 3 → Fin 3 → ℤ) i j :
      ℂ) • a j) :
    ω.covarianceForm b (a 0) = ω.covarianceForm b (a 1) ∧
      ω.covarianceForm b (a 1) = ω.covarianceForm b (a 2) := by
  have e0 := covarianceForm_vector_of_realises σ hσ hb ha 0
  have e1 := covarianceForm_vector_of_realises σ hσ hb ha 1
  simp [Fin.sum_univ_three] at e0 e1
  exact ⟨e0.symm, e1.symm⟩

/-! ## D. The hexagonal plane -/

/-- The rotation by `2π / 3` in the plane, acting on rows. -/
noncomputable def rotationThird : Matrix (Fin 2) (Fin 2) ℂ :=
  !![-1 / 2, Real.sqrt 3 / 2; -(Real.sqrt 3 / 2), -1 / 2]

/-- **A rotation by `2π / 3` makes a `2 × 2` covariance matrix a rotation-dilation**:
`M = [[α, β], [-β, α]]`. -/
lemma covarianceMatrixForm_rotation {a : Fin 2 → A} (σ : A ≃⋆ₐ[ℂ] A)
    (hσ : ∀ x, ω (σ x) = ω x) (ha : ∀ i, σ (a i) = ∑ j, rotationThird j i • a j) :
    ω.covarianceForm (a 0) (a 0) = ω.covarianceForm (a 1) (a 1) ∧
      ω.covarianceForm (a 0) (a 1) = -ω.covarianceForm (a 1) (a 0) := by
  have e := ω.conjTranspose_mul_covarianceMatrixForm_mul σ hσ ha ha
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  simp [mul_apply, Fin.sum_univ_two, rotationThird, covarianceMatrixForm, map_ofNat] at e00 e01
  set s : ℂ := ((Real.sqrt 3 : ℝ) : ℂ)
  have h3 : s ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs : s ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  set x := ω.covarianceForm (a 1) (a 1) - ω.covarianceForm (a 0) (a 0)
  set y := ω.covarianceForm (a 0) (a 1) + ω.covarianceForm (a 1) (a 0)
  have E1 : 3 * x + s * y = 0 := by linear_combination 4 * e00 - ω.covarianceForm (a 1) (a 1) * h3
  have E2 : s * x - 3 * y = 0 := by linear_combination 4 * e01 + ω.covarianceForm (a 1) (a 0) * h3
  have hy : y = 0 := by
    have : 4 * s * y = 0 := by linear_combination E1 - s * E2 + x * h3
    simpa [hs] using this
  have hx : x = 0 := by linear_combination (E1 - s * hy) / 3
  exact ⟨by linear_combination -hx, by linear_combination hy⟩

/-- **A reflection kills the commutator part left by the rotation**: with the reflection
`a₁ ↦ -a₁` as well, the covariance matrix is scalar. -/
lemma covarianceMatrixForm_rotation_reflection {a : Fin 2 → A} (σ τ : A ≃⋆ₐ[ℂ] A)
    (hσ : ∀ x, ω (σ x) = ω x) (ha : ∀ i, σ (a i) = ∑ j, rotationThird j i • a j)
    (hτ : ∀ x, ω (τ x) = ω x) (h0 : τ (a 0) = a 0) (h1 : τ (a 1) = -a 1) :
    ω.covarianceForm (a 0) (a 0) = ω.covarianceForm (a 1) (a 1) ∧
      ω.covarianceForm (a 0) (a 1) = 0 ∧ ω.covarianceForm (a 1) (a 0) = 0 :=
  ⟨(covarianceMatrixForm_rotation σ hσ ha).1, ω.covarianceForm_eq_zero_of_neg τ hτ h0 h1,
    ω.covarianceForm_eq_zero_of_smul τ hτ (χ := -1) (χ' := 1) (by rw [h1, neg_one_smul])
      (by rw [h0, one_smul]) (by norm_num)⟩

end AlgState

end ProbabilisticTheory
