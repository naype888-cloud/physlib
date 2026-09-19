/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathModeInner
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.State.VectorUncertainty

/-!

# The Robertson–Schrödinger defect of the path observables

-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace
open ContinuousLinearMap UnitalPositiveLinearMap

namespace PathObservables

/-- The closed form of `C_Nava (d) ^ 2`, with `N = d + 1` and `θ = π / N`. -/
noncomputable def CNavaSq (d : ℕ) : ℝ :=
  2 * ((d : ℝ) - 1) / (((d : ℝ) + 1) * Real.cos (angle d) ^ 2) *
    ((((d : ℝ) + 1) ^ 2 + 2) / 6 * Real.sin (angle d) ^ 2 - 1)

/-- The expectation of an observable vanishes in the extremal state when `⟪v, a v⟫ = 0`. -/
lemma expectation_extremalState_eq_zero {d : ℕ} (hd : 2 ≤ d)
    (a : Observable (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)))
    (ha : inner ℂ (sineMode d) ((a : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
      (sineMode d)) = 0) :
    (UnitalPositiveLinearMap.ofVec (norm_extremalState d (by omega)))⟨a⟩ = 0 := by
  have h := UnitalPositiveLinearMap.apply_observable_eq_expectation
    (UnitalPositiveLinearMap.ofVec (norm_extremalState d (by omega))) a
  rw [UnitalPositiveLinearMap.ofVec_apply] at h
  have h0 : inner ℂ (extremalState d) ((a : EuclideanSpace ℂ (Fin d) →L[ℂ]
      EuclideanSpace ℂ (Fin d)) (extremalState d)) = 0 := by
    rw [extremalState, map_smul, inner_smul_left, inner_smul_right, ha]
    simp
  exact Complex.ofReal_eq_zero.mp (h.symm.trans h0)

/-- The Cauchy–Schwarz defect of the fluctuation vectors of the path observables in the extremal
state is `(C_Nava (d) ^ 2 - 1) / (d - 1) ^ 2`. -/
lemma nava_robertson_defect {d : ℕ} (hd : 2 ≤ d) :
    centeredGramDefect (UnitalPositiveLinearMap.ofVec (norm_extremalState d (by omega)))
        (transportObservable d) (positionObservable d) =
      (CNavaSq d - 1) / ((d : ℝ) - 1) ^ 2 := by
  have hT := expectation_extremalState_eq_zero hd (transportObservable d)
    (inner_sineMode_transport hd)
  have hP := expectation_extremalState_eq_zero hd (positionObservable d)
    (inner_sineMode_position hd)
  rw [centeredGramDefect_ofVec, hT, hP]
  simp only [zero_smul, sub_zero]
  have hTψ : (transportObservable d : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
      (extremalState d) = ((Real.sqrt (2 / ((d : ℝ) + 1)) : ℝ) : ℂ) •
        Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (transport d) (sineMode d) :=
    map_smul _ _ _
  have hPψ : (positionObservable d : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
      (extremalState d) = ((Real.sqrt (2 / ((d : ℝ) + 1)) : ℝ) : ℂ) •
        Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (position d) (sineMode d) :=
    map_smul _ _ _
  have hpos : (0 : ℝ) < 2 / ((d : ℝ) + 1) := by positivity
  have hs2 : Real.sqrt (2 / ((d : ℝ) + 1)) ^ 2 = 2 / ((d : ℝ) + 1) := Real.sq_sqrt hpos.le
  have hcp : ‖((Real.sqrt (2 / ((d : ℝ) + 1)) : ℝ) : ℂ) *
      ((Real.sqrt (2 / ((d : ℝ) + 1)) : ℝ) : ℂ)‖ = 2 / ((d : ℝ) + 1) := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (mul_self_nonneg _), ← sq, hs2]
  have hnw : ‖(-Complex.I) * ((((d : ℝ) + 1) / (2 * ((d : ℝ) - 1)) : ℝ) : ℂ)‖ ^ 2 =
      (((d : ℝ) + 1) / (2 * ((d : ℝ) - 1))) ^ 2 := by
    have hd1 : (0 : ℝ) < (d : ℝ) - 1 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
  rw [hTψ, hPψ, inner_smul_left, inner_smul_right, norm_smul, norm_smul, ← mul_assoc,
    Complex.conj_ofReal]
  have hin : ‖(((Real.sqrt (2 / ((d : ℝ) + 1)) : ℝ) : ℂ) *
      ((Real.sqrt (2 / ((d : ℝ) + 1)) : ℝ) : ℂ)) *
      inner ℂ (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (transport d) (sineMode d))
        (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (position d) (sineMode d))‖ ^ 2 =
      (2 / ((d : ℝ) + 1)) ^ 2 * (((d : ℝ) + 1) / (2 * ((d : ℝ) - 1))) ^ 2 := by
    rw [norm_mul, mul_pow, hcp, inner_transport_position hd, hnw]
  rw [hin]
  simp only [mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hs2]
  rw [norm_sq_transport_sineMode hd, norm_sq_position_sineMode hd]
  have hc := (cos_angle_pos hd).ne'
  have hs := (sin_angle_pos (by omega : 1 ≤ d)).ne'
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  have hN : (d : ℝ) + 1 ≠ 0 := by positivity
  unfold CNavaSq
  rw [Real.tan_eq_sin_div_cos]
  field_simp

end PathObservables
