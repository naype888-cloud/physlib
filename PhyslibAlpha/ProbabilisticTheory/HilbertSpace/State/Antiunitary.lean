/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.SymmetricState
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.State.Vector

/-!

# Vector states fixed by an antiunitary involution

An antiunitary involution `f` of a Hilbert space, such as time reversal, acts on operators by
`x ↦ f x⋆ f`, a linear map reversing products. A vector state fixed by `f` is invariant under it.

## i. Overview

Let `f` be a conjugate-linear map with `f (f v) = v` and `⟪f v, f w⟫ = conj ⟪v, w⟫`. The map
`τ x = f x⋆ f` is complex linear, `τ 1 = 1`, and `τ (x y) = τ y τ x`. If `f ψ = ψ` for a unit
vector `ψ`, then `⟪ψ, τ x ψ⟫ = ⟪ψ, x ψ⟫`, so the vector state of `ψ` is invariant under `τ`. For
a self-adjoint `a`, `τ a = f a f`. By `covariance_eq_zero_of_reverse_sub`, an observable with
`f a f = a` and one with `f b f = c - b` are uncorrelated in this state, and by
`expectation_bracket_eq_zero_of_reverse` two observables with `f a f = a` and `f b f = b` have a
bracket of expectation zero.

## ii. Key results

- `antiunitaryOfInner` : a conjugate-linear map conjugating inner products, as a continuous
  map.
- `antiunitaryConj` : the map `x ↦ f x⋆ f` on operators.
- `antiunitaryConj_mul` : it reverses products.
- `ofVec_antiunitaryConj` : a vector state fixed by `f` is invariant under it.
- `UnitalPositiveLinearMap.covariance_ofVec_eq_zero_of_antiunitary` : the covariance of an even
  and an odd observable vanishes in such a state.
- `UnitalPositiveLinearMap.expectation_bracket_ofVec_eq_zero_of_antiunitary` : two even
  observables have a bracket of expectation zero in such a state.

## iii. Table of contents

- A. Conjugation by an antiunitary involution
- B. Fixed vector states

## iv. References

* E. Wigner, Group Theory and its Application to the Quantum Mechanics of Atomic Spectra,
  Chapter 26.

-/

@[expose] public section

namespace ProbabilisticTheory

open scoped ComplexOrder InnerProductSpace selfAdjoint
open UnitalPositiveLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ## A. Conjugation by an antiunitary involution -/

/-- A conjugate-linear map with `⟪g v, g w⟫ = conj ⟪v, w⟫`, as a continuous map: it preserves
norms. -/
noncomputable def antiunitaryOfInner (g : H →ₗ⋆[ℂ] H)
    (hg : ∀ v w, ⟪g v, g w⟫_ℂ = (starRingEnd ℂ) ⟪v, w⟫_ℂ) : H →L⋆[ℂ] H :=
  g.mkContinuous 1 fun v => by
    rw [one_mul, @norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ _ _ _ _ v, hg,
      RCLike.conj_re]

omit [CompleteSpace H] in
lemma antiunitaryOfInner_apply (g : H →ₗ⋆[ℂ] H)
    (hg : ∀ v w, ⟪g v, g w⟫_ℂ = (starRingEnd ℂ) ⟪v, w⟫_ℂ) (v : H) :
    antiunitaryOfInner g hg v = g v := rfl

variable (f : H →L⋆[ℂ] H)

/-- The map `x ↦ f x⋆ f` on operators, for a conjugate-linear `f`. -/
noncomputable def antiunitaryConj : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) where
  toFun x := f.comp ((star x).comp f)
  map_add' x y := ContinuousLinearMap.ext fun v => by simp [star_add]
  map_smul' c x := ContinuousLinearMap.ext fun v => by simp [star_smul]

lemma antiunitaryConj_apply (x : H →L[ℂ] H) (v : H) :
    antiunitaryConj f x v = f (star x (f v)) := rfl

variable {f} (hf : ∀ v, f (f v) = v)
include hf

lemma antiunitaryConj_mul (x y : H →L[ℂ] H) :
    antiunitaryConj f (x * y) = antiunitaryConj f y * antiunitaryConj f x :=
  ContinuousLinearMap.ext fun v => by
    change f (star (x * y) (f v)) = f (star y (f (f (star x (f v)))))
    rw [hf, star_mul]
    rfl

lemma antiunitaryConj_one : antiunitaryConj f 1 = 1 :=
  ContinuousLinearMap.ext fun v => by
    change f (star (1 : H →L[ℂ] H) (f v)) = v
    rw [star_one]
    exact hf v

/-! ## B. Fixed vector states -/

variable (hinner : ∀ v w, ⟪f v, f w⟫_ℂ = (starRingEnd ℂ) ⟪v, w⟫_ℂ) {ψ : H} (h : ‖ψ‖ = 1)
  (hψ : f ψ = ψ)
include hinner hψ

omit hf in
/-- A vector state fixed by `f` is invariant under `x ↦ f x⋆ f`. -/
lemma ofVec_antiunitaryConj (x : H →L[ℂ] H) : ofVec h (antiunitaryConj f x) = ofVec h x := by
  change ⟪ψ, f (star x (f ψ))⟫_ℂ = ⟪ψ, x ψ⟫_ℂ
  calc ⟪ψ, f (star x (f ψ))⟫_ℂ = ⟪f ψ, f (star x ψ)⟫_ℂ := by rw [hψ]
    _ = ⟪ψ, x ψ⟫_ℂ := by
      rw [hinner, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
        inner_conj_symm]

/-- **In a vector state fixed by an antiunitary involution `f`, an observable with `f a f = a`
and one with `f b f = c - b` are uncorrelated.** -/
lemma UnitalPositiveLinearMap.covariance_ofVec_eq_zero_of_antiunitary
    {a b : Observable (H →L[ℂ] H)} (ha : ∀ v, f ((a : H →L[ℂ] H) (f v)) = (a : H →L[ℂ] H) v)
    (c : ℂ) (hb : ∀ v, f ((b : H →L[ℂ] H) (f v)) = c • v - (b : H →L[ℂ] H) v) :
    covariance (ofVec h) a b = 0 := by
  refine covariance_eq_zero_of_reverse_sub (ofVec h) (antiunitaryConj f)
    (antiunitaryConj_mul hf) (ofVec_antiunitaryConj hinner h hψ) (antiunitaryConj_one hf)
    (ContinuousLinearMap.ext fun v => ?_) c (ContinuousLinearMap.ext fun v => ?_)
  · rw [antiunitaryConj_apply, a.property.star_eq, ha]
  · rw [antiunitaryConj_apply, b.property.star_eq, hb]
    rfl

/-- **In a vector state fixed by an antiunitary involution `f`, two observables with `f a f = a`
and `f b f = b` have a bracket of expectation zero.** -/
lemma UnitalPositiveLinearMap.expectation_bracket_ofVec_eq_zero_of_antiunitary
    {a b : Observable (H →L[ℂ] H)} (ha : ∀ v, f ((a : H →L[ℂ] H) (f v)) = (a : H →L[ℂ] H) v)
    (hb : ∀ v, f ((b : H →L[ℂ] H) (f v)) = (b : H →L[ℂ] H) v) :
    (ofVec h)⟨⁅a, b⁆⟩ = 0 := by
  refine expectation_bracket_eq_zero_of_reverse (ofVec h) (antiunitaryConj f)
    (antiunitaryConj_mul hf) (ofVec_antiunitaryConj hinner h hψ)
    (ContinuousLinearMap.ext fun v => ?_) (ContinuousLinearMap.ext fun v => ?_)
  · rw [antiunitaryConj_apply, a.property.star_eq, ha]
  · rw [antiunitaryConj_apply, b.property.star_eq, hb]

end ProbabilisticTheory
