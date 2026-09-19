/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathTransportAction
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathAngleSums

/-!

# Norms of the path observables on the extremal vector

For `v = sineMode d`: the coordinates of `T v` and `P v`, `‖T v‖²` and `‖P v‖²`.

-/

@[expose] public section

open Finset Matrix

namespace PathObservables

/-! ## The vectors `T v` and `P v` for `v = sineMode d` -/

lemma transport_sineMode_apply {d : ℕ} (hd : 2 ≤ d) (j : Fin d) :
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (transport d) (sineMode d)).ofLp j =
      -Complex.I * (Real.tan (angle d) : ℂ) * (Real.cos (((j : ℕ) + 1) * angle d) : ℂ) *
        (-Complex.I) ^ (j : ℕ) := by
  rw [ofLp_toEuclideanCLM]
  exact transport_mulVec_sineMode hd j

lemma position_sineMode_apply (d : ℕ) (j : Fin d) :
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (position d) (sineMode d)).ofLp j =
      (coordinate d j : ℂ) * (sineMode d).ofLp j := by
  rw [ofLp_toEuclideanCLM, position, mulVec_diagonal]

lemma norm_sq_phase_mul (i : ℕ) (z : ℂ) : ‖(-Complex.I) ^ i * z‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [norm_mul, norm_pow, norm_neg, Complex.norm_I, one_pow, one_mul]

lemma phase_mul_conj (i : ℕ) :
    (-Complex.I) ^ i * (starRingEnd ℂ) ((-Complex.I) ^ i) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, norm_neg, Complex.norm_I]
  simp

/-- `‖T v‖² = tan² θ (d - 1) / 2`. -/
lemma norm_sq_transport_sineMode {d : ℕ} (hd : 2 ≤ d) :
    ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (transport d) (sineMode d)‖ ^ 2 =
      Real.tan (angle d) ^ 2 * (((d : ℝ) - 1) / 2) := by
  rw [EuclideanSpace.norm_sq_eq, ← sum_cos_sq_angle (by omega : 1 ≤ d), mul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [transport_sineMode_apply hd, mul_comm, norm_sq_phase_mul]
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, sq_abs, sq_abs]

/-! ## Sums over `Fin d` -/

lemma sum_fin_pos_sin_sq {d : ℕ} (hd : 1 ≤ d) :
    ∑ j : Fin d, (2 * (((j : ℕ) : ℝ) + 1) - ((d : ℝ) + 1)) *
      Real.sin ((((j : ℕ) : ℝ) + 1) * angle d) ^ 2 = 0 := by
  have h := sum_fin_succ d (fun k => (2 * (k : ℝ) - ((d : ℝ) + 1)) * Real.sin (k * angle d) ^ 2)
    (by simp)
  have h2 := sum_range_pos_sin_sq hd
  rw [← h] at h2
  push_cast at h2
  exact h2

lemma sum_fin_pos_sq_sin_sq {d : ℕ} (hd : 1 ≤ d) :
    ∑ j : Fin d, (2 * (((j : ℕ) : ℝ) + 1) - ((d : ℝ) + 1)) ^ 2 *
      Real.sin ((((j : ℕ) : ℝ) + 1) * angle d) ^ 2 =
        ((d : ℝ) + 1) * (((d : ℝ) + 1) ^ 2 + 2) / 6 - ((d : ℝ) + 1) / Real.sin (angle d) ^ 2 := by
  have h := sum_fin_succ d
    (fun k => (2 * (k : ℝ) - ((d : ℝ) + 1)) ^ 2 * Real.sin (k * angle d) ^ 2) (by simp)
  have h2 := sum_range_pos_sq_sin_sq hd
  rw [← h] at h2
  push_cast at h2
  exact h2

lemma sum_fin_pos_sin_two {d : ℕ} (hd : 1 ≤ d) :
    ∑ j : Fin d, (2 * (((j : ℕ) : ℝ) + 1) - ((d : ℝ) + 1)) *
      Real.sin (2 * ((((j : ℕ) : ℝ) + 1) * angle d)) =
        -(((d : ℝ) + 1) * Real.cos (angle d)) / Real.sin (angle d) := by
  have h := sum_fin_succ d
    (fun k => (2 * (k : ℝ) - ((d : ℝ) + 1)) * Real.sin (2 * (k * angle d))) (by simp)
  have h2 := sum_range_pos_sin_two hd
  rw [← h] at h2
  push_cast at h2
  exact h2

lemma sum_fin_sin_two {d : ℕ} (hd : 1 ≤ d) :
    ∑ j : Fin d, Real.sin (2 * ((((j : ℕ) : ℝ) + 1) * angle d)) = 0 := by
  have h := sum_fin_succ d (fun k => Real.sin (2 * (k * angle d))) (by simp)
  have h2 := sum_sin_two_angle hd
  rw [← h] at h2
  push_cast at h2
  exact h2

/-- `‖P v‖² = (N (N² + 2) / 6 - N / sin² θ) / (d - 1)²`, `N = d + 1`. -/
lemma norm_sq_position_sineMode {d : ℕ} (hd : 2 ≤ d) :
    ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) (position d) (sineMode d)‖ ^ 2 =
      (((d : ℝ) + 1) * (((d : ℝ) + 1) ^ 2 + 2) / 6 - ((d : ℝ) + 1) / Real.sin (angle d) ^ 2) /
        ((d : ℝ) - 1) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, ← sum_fin_pos_sq_sin_sq (by omega : 1 ≤ d), sum_div]
  refine sum_congr rfl fun j _ => ?_
  rw [position_sineMode_apply, sineMode_apply, mul_left_comm, norm_sq_phase_mul, norm_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, sq_abs,
    sq_abs, coordinate, div_pow]
  ring

end PathObservables
