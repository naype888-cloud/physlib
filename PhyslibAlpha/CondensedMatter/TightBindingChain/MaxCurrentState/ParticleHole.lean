/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentState.Basic
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.State.Antiunitary

/-!

# Particle–hole symmetry of the open tight binding chain

## i. Overview

The chain is bipartite: hopping joins the even sites to the odd ones. Conjugating the amplitudes
and changing the sign of the odd ones gives an antiunitary involution `K`, the particle–hole
conjugation. It fixes the position operator and sends `H - E0` to `-(H - E0)`.

By `covariance_ofVec_eq_zero_of_antiunitary`, the energy and position fluctuations of a state
`ψ` with `K ψ = ψ` are uncorrelated. The maximal current state, with amplitudes
`iᵐ sin ((m + 1) π / (N + 1))` up to a positive factor, is such a state.

## ii. Key results

- `particleHole` : the particle–hole conjugation `K`.
- `particleHole_position`, `particleHole_openHamiltonian` : `K X K = X` and `K H K = 2 E0 - H`.
- `covariance_eq_zero_of_particleHole` : in a state fixed by `K` the energy and position
  fluctuations are uncorrelated.
- `particleHole_maxCurrentState` : the maximal current state is fixed by `K`.

## iii. Table of contents

- A. The particle–hole conjugation
- B. Action on the energy and the position
- C. Uncorrelated fluctuations

## iv. References

* A. Altland & M. Zirnbauer, Nonstandard symmetry classes in mesoscopic normal-superconducting
  hybrid structures, Phys. Rev. B 55 (1997) 1142.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open InnerProductSpace QuantumMechanics.FiniteHilbertSpace ProbabilisticTheory
open UnitalPositiveLinearMap
open scoped selfAdjoint
variable (T : TightBindingChain)

/-!

## A. The particle–hole conjugation

-/

/-- The particle–hole conjugation: complex conjugation of the amplitudes, with the sign of the
odd sites changed. -/
noncomputable def particleHole (ψ : T.HilbertSpace) : T.HilbertSpace :=
  ⟨WithLp.toLp 2 fun n => (-1) ^ (n : ℕ) * (starRingEnd ℂ) (ψ.val n)⟩

lemma particleHole_val (ψ : T.HilbertSpace) (n : Fin T.N) :
    (T.particleHole ψ).val n = (-1) ^ (n : ℕ) * (starRingEnd ℂ) (ψ.val n) := rfl

lemma inner_localizedState (ψ : T.HilbertSpace) (m : Fin T.N) : ⟪|m⟩, ψ⟫_ℂ = ψ.val m := by
  change ⟪basisFun (Fin T.N) m, ψ⟫_ℂ = _
  rw [inner_eq_val, basisFun_apply, EuclideanSpace.inner_single_left, map_one, one_mul]

lemma inner_particleHole (ψ : T.HilbertSpace) (m : Fin T.N) :
    ⟪|m⟩, T.particleHole ψ⟫_ℂ = (-1) ^ (m : ℕ) * (starRingEnd ℂ) ⟪|m⟩, ψ⟫_ℂ := by
  rw [inner_localizedState, inner_localizedState, particleHole_val]

lemma particleHole_add (ψ φ : T.HilbertSpace) :
    T.particleHole (ψ + φ) = T.particleHole ψ + T.particleHole φ := by
  ext n
  change (-1) ^ (n : ℕ) * (starRingEnd ℂ) (ψ.val n + φ.val n) =
    (-1) ^ (n : ℕ) * (starRingEnd ℂ) (ψ.val n) + (-1) ^ (n : ℕ) * (starRingEnd ℂ) (φ.val n)
  rw [map_add, mul_add]

lemma particleHole_smul (c : ℂ) (ψ : T.HilbertSpace) :
    T.particleHole (c • ψ) = (starRingEnd ℂ) c • T.particleHole ψ := by
  ext n
  change (-1) ^ (n : ℕ) * (starRingEnd ℂ) (c * ψ.val n) = _ * ((-1) ^ (n : ℕ) * _)
  rw [map_mul]
  ring

lemma particleHole_real_smul (r : ℝ) (ψ : T.HilbertSpace) :
    T.particleHole (r • ψ) = r • T.particleHole ψ := by
  rw [← Complex.coe_smul, particleHole_smul, Complex.conj_ofReal, Complex.coe_smul]

lemma particleHole_particleHole (ψ : T.HilbertSpace) : T.particleHole (T.particleHole ψ) = ψ := by
  ext n
  change (-1) ^ (n : ℕ) * (starRingEnd ℂ) ((-1) ^ (n : ℕ) * (starRingEnd ℂ) (ψ.val n)) = _
  rw [map_mul, Complex.conj_conj, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]
  simp

lemma inner_particleHole_particleHole (ψ φ : T.HilbertSpace) :
    ⟪T.particleHole ψ, T.particleHole φ⟫_ℂ = (starRingEnd ℂ) ⟪ψ, φ⟫_ℂ := by
  simp only [inner_eq_val, PiLp.inner_apply, map_sum, RCLike.inner_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  change (-1) ^ (n : ℕ) * (starRingEnd ℂ) (φ.val n) *
    (starRingEnd ℂ) ((-1) ^ (n : ℕ) * (starRingEnd ℂ) (ψ.val n)) = _
  simp only [map_mul, map_pow, map_neg, map_one, Complex.conj_conj]
  rw [show ((-1 : ℂ) ^ (n : ℕ)) * (starRingEnd ℂ) (φ.val n) * ((-1) ^ (n : ℕ) * ψ.val n) =
    ((-1) ^ (n : ℕ) * (-1) ^ (n : ℕ)) * ((starRingEnd ℂ) (φ.val n) * ψ.val n) by ring,
    ← mul_pow]
  simp [mul_comm]

/-!

## B. Action on the energy and the position

-/

private lemma neg_one_pow_mul_self (k : ℕ) : (-1 : ℂ) ^ k * (-1) ^ k = 1 := by
  rw [← mul_pow]; simp

/-- The components of `K A K ψ`: the matrix elements of `A` conjugated, with the signs of
both sites. -/
lemma inner_particleHole_apply_particleHole (A : T.HilbertSpace →ₗ[ℂ] T.HilbertSpace)
    (ψ : T.HilbertSpace) (m : Fin T.N) :
    ⟪|m⟩, T.particleHole (A (T.particleHole ψ))⟫_ℂ =
      ∑ n : Fin T.N, (-1) ^ (m : ℕ) * (-1) ^ (n : ℕ) * (starRingEnd ℂ) ⟪|m⟩, A |n⟩⟫_ℂ *
        ⟪|n⟩, ψ⟫_ℂ := by
  rw [inner_particleHole, T.inner_apply_eq_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [inner_particleHole, map_mul, map_mul, Complex.conj_conj, map_pow, map_neg, map_one]
  ring

/-- `K X K = X`. -/
lemma particleHole_position (ψ : T.HilbertSpace) :
    T.particleHole (T.position (T.particleHole ψ)) = T.position ψ := by
  refine T.ext_localizedState fun m => ?_
  rw [inner_particleHole_apply_particleHole, T.inner_apply_eq_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [position_apply_localizedState, inner_smul_right, localizedState_orthonormal_eq_ite]
  split_ifs with h
  · subst h
    rw [mul_one, Complex.conj_ofReal, neg_one_pow_mul_self, one_mul]
  · simp

/-- `K H K = 2 E0 - H`: the particle–hole conjugation reverses the energy about the band
centre. -/
lemma particleHole_openHamiltonian (ψ : T.HilbertSpace) :
    T.particleHole (T.openHamiltonian (T.particleHole ψ)) =
      (2 * T.E0 : ℂ) • ψ - T.openHamiltonian ψ := by
  refine T.ext_localizedState fun m => ?_
  rw [inner_particleHole_apply_particleHole, inner_sub_right, inner_smul_right,
    T.inner_apply_eq_sum, eq_sub_iff_add_eq, ← Finset.sum_add_distrib,
    show (2 * T.E0 : ℂ) * ⟪|m⟩, ψ⟫_ℂ =
      ∑ n : Fin T.N, if m = n then (2 * T.E0 : ℂ) * ⟪|n⟩, ψ⟫_ℂ else 0 by simp]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [inner_openHamiltonian]
  split_ifs with h1 h2
  · subst h1
    rw [Complex.conj_ofReal, neg_one_pow_mul_self]
    ring
  · have hs : (-1 : ℂ) ^ (m : ℕ) * (-1) ^ (n : ℕ) = -1 := by
      rcases h2 with h | h <;> rw [← h, pow_succ] <;>
        linear_combination (-1 : ℂ) * neg_one_pow_mul_self _
    rw [hs, map_neg, Complex.conj_ofReal]
    ring
  · simp

/-!

## C. Uncorrelated fluctuations

-/

/-- The particle–hole conjugation as a continuous conjugate-linear map. -/
noncomputable def particleHoleCLM : T.HilbertSpace →L⋆[ℂ] T.HilbertSpace :=
  antiunitaryOfInner
    { toFun := T.particleHole
      map_add' := T.particleHole_add
      map_smul' := T.particleHole_smul }
    T.inner_particleHole_particleHole

/-- **In a state fixed by the particle–hole conjugation the energy and position fluctuations
are uncorrelated.** -/
lemma covariance_eq_zero_of_particleHole {ψ : T.HilbertSpace} (h : ‖ψ‖ = 1)
    (hψ : T.particleHole ψ = ψ) :
    covariance (ofVec h) T.openHamiltonianObservable T.positionObservable = 0 := by
  rw [covariance_comm]
  exact covariance_ofVec_eq_zero_of_antiunitary (f := T.particleHoleCLM)
    T.particleHole_particleHole T.inner_particleHole_particleHole h hψ
    T.particleHole_position _ T.particleHole_openHamiltonian

/-- The maximal current state is fixed by the particle–hole conjugation. -/
lemma particleHole_maxCurrentState : T.particleHole T.maxCurrentState = T.maxCurrentState := by
  refine T.ext_localizedState fun m => ?_
  rw [inner_particleHole, inner_maxCurrentState]
  simp only [map_mul, Complex.conj_ofReal, map_pow, Complex.conj_I]
  rw [mul_left_comm, ← mul_assoc ((-1 : ℂ) ^ (m : ℕ)), ← mul_pow, neg_one_mul, neg_neg]

end TightBindingChain
end CondensedMatter
