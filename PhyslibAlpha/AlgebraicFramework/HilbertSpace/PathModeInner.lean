/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathModeNorms

/-!

# Inner products of the path observables on the extremal vector

For `v = sineMode d`: `⟪v, T v⟫ = ⟪v, P v⟫ = 0` and `⟪T v, P v⟫ = -i (d + 1) / (2 (d - 1))`.

-/

@[expose] public section

open Finset Matrix

namespace PathObservables

lemma inner_sineMode_transport {d : ℕ} (hd : 2 ≤ d) :
    inner ℂ (sineMode d)
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (transport d) (sineMode d)) = 0 := by
  have hterm : ∀ j : Fin d,
      inner ℂ ((sineMode d).ofLp j)
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (transport d) (sineMode d)).ofLp j) =
      -Complex.I * (Real.tan (angle d) : ℂ) *
        ((Real.sin (2 * ((((j : ℕ) : ℝ) + 1) * angle d)) / 2 : ℝ) : ℂ) := by
    intro j
    rw [RCLike.inner_apply, transport_sineMode_apply hd, sineMode_apply, map_mul,
      Complex.conj_ofReal, Real.sin_two_mul]
    generalize Real.sin ((((j : ℕ) : ℝ) + 1) * angle d) = a
    generalize Real.cos ((((j : ℕ) : ℝ) + 1) * angle d) = b
    generalize Real.tan (angle d) = t
    push_cast
    linear_combination (-Complex.I * (t : ℂ) * (b : ℂ) * (a : ℂ)) * phase_mul_conj (j : ℕ)
  rw [PiLp.inner_apply]
  simp_rw [hterm]
  rw [← mul_sum, ← Complex.ofReal_sum, ← sum_div, sum_fin_sin_two (by omega : 1 ≤ d)]
  simp

lemma inner_sineMode_position {d : ℕ} (hd : 2 ≤ d) :
    inner ℂ (sineMode d)
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (position d) (sineMode d)) = 0 := by
  have hterm : ∀ j : Fin d,
      inner ℂ ((sineMode d).ofLp j)
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (position d) (sineMode d)).ofLp j) =
      (((2 * (((j : ℕ) : ℝ) + 1) - ((d : ℝ) + 1)) *
        Real.sin ((((j : ℕ) : ℝ) + 1) * angle d) ^ 2 / ((d : ℝ) - 1) : ℝ) : ℂ) := by
    intro j
    rw [RCLike.inner_apply, position_sineMode_apply, sineMode_apply, map_mul, Complex.conj_ofReal,
      coordinate]
    generalize Real.sin ((((j : ℕ) : ℝ) + 1) * angle d) = a
    push_cast
    linear_combination ((2 * (((j : ℕ) : ℂ) + 1) - ((d : ℂ) + 1)) / ((d : ℂ) - 1) *
      (a : ℂ) ^ 2) * phase_mul_conj (j : ℕ)
  rw [PiLp.inner_apply]
  simp_rw [hterm]
  rw [← Complex.ofReal_sum, ← sum_div, sum_fin_pos_sin_sq (by omega : 1 ≤ d)]
  simp

lemma sum_coordinate_sin_cos {d : ℕ} (hd : 2 ≤ d) :
    ∑ j : Fin d, coordinate d j *
      (Real.sin ((((j : ℕ) : ℝ) + 1) * angle d) * Real.cos ((((j : ℕ) : ℝ) + 1) * angle d)) =
        -(((d : ℝ) + 1) * Real.cos (angle d)) / (2 * ((d : ℝ) - 1) * Real.sin (angle d)) := by
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  have hs := (sin_angle_pos (by omega : 1 ≤ d)).ne'
  have hterm : ∀ j : Fin d, coordinate d j *
      (Real.sin ((((j : ℕ) : ℝ) + 1) * angle d) * Real.cos ((((j : ℕ) : ℝ) + 1) * angle d)) =
        (2 * (((j : ℕ) : ℝ) + 1) - ((d : ℝ) + 1)) *
          Real.sin (2 * ((((j : ℕ) : ℝ) + 1) * angle d)) / (2 * ((d : ℝ) - 1)) := by
    intro j
    rw [coordinate, Real.sin_two_mul]
    field_simp
  simp_rw [hterm]
  rw [← sum_div, sum_fin_pos_sin_two (by omega : 1 ≤ d)]
  field_simp

/-- `⟪T v, P v⟫ = -i (d + 1) / (2 (d - 1))`. -/
lemma inner_transport_position {d : ℕ} (hd : 2 ≤ d) :
    inner ℂ (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (transport d) (sineMode d))
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (position d) (sineMode d)) =
        -Complex.I * ((((d : ℝ) + 1) / (2 * ((d : ℝ) - 1)) : ℝ) : ℂ) := by
  have hterm : ∀ j : Fin d,
      inner ℂ ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (transport d) (sineMode d)).ofLp j)
        ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (position d) (sineMode d)).ofLp j) =
      Complex.I * (Real.tan (angle d) : ℂ) * ((coordinate d j *
        (Real.sin ((((j : ℕ) : ℝ) + 1) * angle d) *
          Real.cos ((((j : ℕ) : ℝ) + 1) * angle d)) : ℝ) : ℂ) := by
    intro j
    rw [RCLike.inner_apply, transport_sineMode_apply hd, position_sineMode_apply, sineMode_apply,
      map_mul, map_mul, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal,
      Complex.conj_ofReal]
    generalize Real.sin ((((j : ℕ) : ℝ) + 1) * angle d) = a
    generalize Real.cos ((((j : ℕ) : ℝ) + 1) * angle d) = b
    generalize Real.tan (angle d) = t
    generalize coordinate d j = q
    push_cast
    linear_combination (Complex.I * (t : ℂ) * (q : ℂ) * (a : ℂ) * (b : ℂ)) * phase_mul_conj (j : ℕ)
  have hc := (cos_angle_pos hd).ne'
  have hs := (sin_angle_pos (by omega : 1 ≤ d)).ne'
  have hd1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    intro h
    linarith
  rw [PiLp.inner_apply]
  simp_rw [hterm]
  rw [← mul_sum, ← Complex.ofReal_sum, sum_coordinate_sin_cos hd, Real.tan_eq_sin_div_cos]
  have hd1' : ((d : ℂ) - 1) ≠ 0 := by exact_mod_cast hd1
  generalize Real.cos (angle d) = b at hc ⊢
  generalize Real.sin (angle d) = a at hs ⊢
  have hc' : (b : ℂ) ≠ 0 := by exact_mod_cast hc
  have hs' : (a : ℂ) ≠ 0 := by exact_mod_cast hs
  push_cast
  field_simp

end PathObservables
