/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.Uncertainty

/-!

# Covariances and brackets in a symmetric state

A symmetry of a state fixes some entries of the matrices `Σ` and `Ω` of Robertson's relation.

## i. Overview

Let `σ` be a `⋆`-automorphism with `ω ∘ σ = ω`, and let `a` and `b` be observables with `σ a = a`
and `σ b = -b`. Then `ω(a b) = ω(σ (a b)) = -ω(a b)`, so `ω(a b) = 0`, and in the same way
`ω(b a) = 0` and `ω(b) = 0`. The covariance of `a` and `b` and the expectation of their bracket
both vanish. For a family of observables, each even or odd under `σ`, the matrices `Σ` and `Ω`
are block diagonal, with one block for the even and one for the odd observables.

Time reversal is antiunitary, `x ↦ Θ x⋆ Θ⁻¹` is a linear map that reverses products. If it fixes
`ω`, `a` and `b`, then `ω(a b) = ω(b a)`, the conjugate of `ω(a b)`, so `ω(a b)` is real and
the bracket has expectation zero. If it fixes `a` and reverses `b`, then `ω(a b)` is imaginary
and the covariance vanishes. So a unitary symmetry acts on `Σ` and `Ω` in the same way, while
time reversal removes `Ω` within each parity and `Σ` between them.

## ii. Key results

- `UnitalPositiveLinearMap.covariance_eq_zero_of_symm` : an even and an odd observable of a
  symmetric state have covariance zero.
- `UnitalPositiveLinearMap.expectation_bracket_eq_zero_of_symm` : and their bracket has
  expectation zero.
- `UnitalPositiveLinearMap.covariance_eq_of_symm`,
  `UnitalPositiveLinearMap.expectation_bracket_eq_of_symm` : a symmetry of the state preserves
  `Σ` and `Ω`.
- `UnitalPositiveLinearMap.covariance_eq_zero_of_reverse` : under time reversal, an even and an
  odd observable have covariance zero.
- `UnitalPositiveLinearMap.covariance_eq_zero_of_reverse_sub` : the same when the odd
  observable is reversed about a constant, `τ b = c - b`.
- `UnitalPositiveLinearMap.expectation_bracket_eq_zero_of_reverse` : under time reversal, two
  even observables have a bracket of expectation zero.

## iii. Table of contents

- A. Unitary symmetries
- B. Time reversal

## iv. References

* E. Wigner, Group Theory and its Application to the Quantum Mechanics of Atomic Spectra,
  Chapter 26.

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped ComplexOrder selfAdjoint

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace UnitalPositiveLinearMap

variable (ω : 𝓢[ℂ, A]) {a b : Observable A}

omit [StarOrderedRing A] in
/-- An observable reversed by a linear map that fixes the state has expectation zero. -/
lemma apply_eq_zero_of_neg (τ : A →ₗ[ℂ] A) (hω : ∀ x, ω (τ x) = ω x) (hb : τ b = -b) :
    ω (b : A) = 0 := by
  have h := hω b
  rw [hb, map_neg] at h
  linear_combination -h / 2

/-- The covariance of `a` and `b` is the real part of `ω(a b)` when `ω(b) = 0`. -/
lemma covariance_eq_re_of_apply_eq_zero (hb : ω (b : A) = 0) :
    covariance ω a b = (ω ((a : A) * b)).re := by
  have hb0 : ω⟨b⟩ = 0 := by
    rw [apply_observable_eq_expectation] at hb
    exact_mod_cast hb
  have hc : (centered ω b : A) = b := by
    simp only [centered, LinearMap.centered]
    simp [show (expectation ω).toLinearMap b = 0 from hb0]
  have ha : (centered ω a : A) = (a : A) - (ω⟨a⟩ : ℂ) • 1 := by
    simp only [centered, LinearMap.centered]
    simp [Complex.coe_smul]
    rfl
  rw [covariance_eq_re_apply_centered_mul, hc, ha, sub_mul, map_sub, smul_mul_assoc, one_mul,
    map_smul, hb, smul_zero, sub_zero]

/-- The bracket of `a` and `b` has expectation zero when `ω(a b)` is real. -/
lemma expectation_bracket_eq_zero_of_im (h : (ω ((a : A) * b)).im = 0) : ω⟨⁅a, b⁆⟩ = 0 := by
  have h' := apply_observable_eq_expectation ω ⁅a, b⁆
  rw [selfAdjoint.coe_bracket, map_smul, map_sub, apply_mul_comm_eq_star ω a b] at h'
  have h0 : ω ((a : A) * b) - star (ω ((a : A) * b)) = 0 := by
    apply Complex.ext <;> simp [h]
  rw [h0, smul_zero] at h'
  exact_mod_cast h'.symm

/-! ## A. Unitary symmetries -/

section Symm

variable (σ : A ≃⋆ₐ[ℂ] A) (hω : ∀ x, ω (σ x) = ω x) (ha : σ a = a) (hb : σ b = -b)
include hω ha hb

omit [StarOrderedRing A] in
/-- In a symmetric state, an even and an odd observable have `ω(a b) = 0`. -/
lemma apply_mul_eq_zero_of_symm : ω ((a : A) * b) = 0 := by
  have h := hω ((a : A) * b)
  rw [map_mul, ha, hb, mul_neg, map_neg] at h
  linear_combination -h / 2

/-- **The covariance of an even and an odd observable vanishes in a symmetric state.** -/
lemma covariance_eq_zero_of_symm : covariance ω a b = 0 := by
  rw [covariance_eq_re_of_apply_eq_zero ω (apply_eq_zero_of_neg ω σ.toAlgEquiv.toLinearMap hω hb),
    apply_mul_eq_zero_of_symm ω σ hω ha hb, Complex.zero_re]

/-- **The bracket of an even and an odd observable has expectation zero in a symmetric
state.** -/
lemma expectation_bracket_eq_zero_of_symm : ω⟨⁅a, b⁆⟩ = 0 :=
  expectation_bracket_eq_zero_of_im ω (by rw [apply_mul_eq_zero_of_symm ω σ hω ha hb,
    Complex.zero_im])

end Symm

section Invariance

variable (σ : A ≃⋆ₐ[ℂ] A) (hω : ∀ x, ω (σ x) = ω x) {a' b' : Observable A} (ha : σ a = a')
  (hb : σ b = b')
include hω ha hb

/-- **A symmetry of the state preserves covariances**: `Σ_{σa, σb} = Σ_{ab}`. -/
lemma covariance_eq_of_symm : covariance ω a' b' = covariance ω a b := by
  have hc : ∀ {x y : Observable A}, σ x = y → (centered ω y : A) = σ (centered ω x) := by
    intro x y h
    have he : (ω⟨y⟩ : ℂ) = ω⟨x⟩ := by
      rw [← apply_observable_eq_expectation, ← apply_observable_eq_expectation, ← h, hω]
    have hcx : ∀ z : Observable A, (centered ω z : A) = (z : A) - (ω⟨z⟩ : ℂ) • 1 := by
      intro z
      simp only [centered, LinearMap.centered]
      simp [Complex.coe_smul]
      rfl
    rw [hcx, hcx, map_sub, map_smul, map_one, h, he]
  rw [covariance_eq_re_apply_centered_mul, covariance_eq_re_apply_centered_mul, hc ha, hc hb,
    ← map_mul, hω]

/-- **A symmetry of the state preserves the expectations of brackets**: `Ω_{σa, σb} = Ω_{ab}`. -/
lemma expectation_bracket_eq_of_symm : ω⟨⁅a', b'⁆⟩ = ω⟨⁅a, b⁆⟩ := by
  have h : (ω⟨⁅a', b'⁆⟩ : ℂ) = ω⟨⁅a, b⁆⟩ := by
    rw [← apply_observable_eq_expectation, ← apply_observable_eq_expectation,
      selfAdjoint.coe_bracket, selfAdjoint.coe_bracket, ← ha, ← hb, ← map_mul, ← map_mul,
      ← map_sub, ← map_smul, hω]
  exact_mod_cast h

end Invariance

/-! ## B. Time reversal -/

section Reverse

variable (τ : A →ₗ[ℂ] A) (hτ : ∀ x y, τ (x * y) = τ y * τ x) (hω : ∀ x, ω (τ x) = ω x)
include hτ hω

/-- **The covariance of an even and an odd observable vanishes in a state invariant under time
reversal.** -/
lemma covariance_eq_zero_of_reverse (ha : τ a = a) (hb : τ b = -b) : covariance ω a b = 0 := by
  rw [covariance_eq_re_of_apply_eq_zero ω (apply_eq_zero_of_neg ω τ hω hb)]
  have h := hω ((a : A) * b)
  rw [hτ, ha, hb, neg_mul, map_neg, apply_mul_comm_eq_star] at h
  have := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.star_def, Complex.conj_re] at this
  linarith

/-- **The bracket of two even observables has expectation zero in a state invariant under time
reversal.** -/
lemma expectation_bracket_eq_zero_of_reverse (ha : τ a = a) (hb : τ b = b) : ω⟨⁅a, b⁆⟩ = 0 := by
  refine expectation_bracket_eq_zero_of_im ω ?_
  have h := hω ((a : A) * b)
  rw [hτ, ha, hb, apply_mul_comm_eq_star] at h
  have := congrArg Complex.im h
  simp only [Complex.star_def, Complex.conj_im] at this
  linarith

/-- **The covariance of an even observable and one reversed about a constant vanishes in a state
invariant under time reversal.** -/
lemma covariance_eq_zero_of_reverse_sub (hτ1 : τ 1 = 1) (ha : τ a = a) (c : ℂ)
    (hb : τ b = c • 1 - b) : covariance ω a b = 0 := by
  have hc : c = 2 * (ω⟨b⟩ : ℂ) := by
    have h := hω b
    rw [hb, map_sub, map_smul, map_one, smul_eq_mul, mul_one, apply_observable_eq_expectation] at h
    linear_combination h
  have hcoe : (centered ω b : A) = (b : A) - (ω⟨b⟩ : ℂ) • 1 := by
    simp only [centered, LinearMap.centered]
    simp [Complex.coe_smul]
    rfl
  have hb' : τ (centered ω b) = -(centered ω b : A) := by
    rw [hcoe, map_sub, map_smul, hτ1, hb, hc]
    module
  have h0 := covariance_eq_zero_of_reverse ω τ hτ hω ha hb'
  rwa [show centered ω b = b + (-ω⟨b⟩) • 1 by
    simp [centered, LinearMap.centered, sub_eq_add_neg]; rfl,
    covariance_add_smul_one_right] at h0

end Reverse

end UnitalPositiveLinearMap

end ProbabilisticTheory
