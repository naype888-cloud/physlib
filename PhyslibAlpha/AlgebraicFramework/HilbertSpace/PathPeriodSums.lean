/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathRootSums

/-!

# Weighted trigonometric sums over a period

For `N ≥ 2` and `φ = 2π / N`, the sums `∑_{k<N} k cos (k φ)`, `∑_{k<N} k sin (k φ)`,
`∑_{k<N} sin (k φ)` and `∑_{k<N} k² cos (k φ)`.

-/

@[expose] public section

open Finset

namespace PathObservables

/-! ## Real and imaginary parts -/

lemma root_re (N : ℕ) : (root N).re = Real.cos (2 * Real.pi / N) := by
  simpa using root_pow_re N 1

lemma root_im (N : ℕ) : (root N).im = Real.sin (2 * Real.pi / N) := by
  simpa using root_pow_im N 1

lemma one_sub_cos_ne_zero {N : ℕ} (hN : 2 ≤ N) : 1 - Real.cos (2 * Real.pi / N) ≠ 0 := by
  intro h
  have hc : Real.cos (2 * Real.pi / N) = 1 := by linarith
  have hs : Real.sin (2 * Real.pi / N) = 0 := by
    have := Real.sin_sq_add_cos_sq (2 * Real.pi / N)
    rw [hc] at this
    nlinarith [sq_nonneg (Real.sin (2 * Real.pi / N))]
  exact root_ne_one hN (Complex.ext (by simp [root_re, hc]) (by simp [root_im, hs]))

/-- The two real equations of `(∑ k zᵏ) (z - 1) = N`, in terms of the real sums. -/
private lemma eqs_mul {N : ℕ} (hN : 2 ≤ N) :
    (∑ k ∈ range N, (k : ℝ) * Real.cos (2 * Real.pi * k / N)) *
        (Real.cos (2 * Real.pi / N) - 1) -
      (∑ k ∈ range N, (k : ℝ) * Real.sin (2 * Real.pi * k / N)) * Real.sin (2 * Real.pi / N) =
        N ∧
    (∑ k ∈ range N, (k : ℝ) * Real.cos (2 * Real.pi * k / N)) * Real.sin (2 * Real.pi / N) +
      (∑ k ∈ range N, (k : ℝ) * Real.sin (2 * Real.pi * k / N)) *
        (Real.cos (2 * Real.pi / N) - 1) = 0 := by
  have h := sum_mul_root hN
  have e1 := congrArg Complex.re h
  have e2 := congrArg Complex.im h
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.re_sum,
    Complex.im_sum, root_re, root_im, root_pow_re, root_pow_im, Complex.natCast_re,
    Complex.natCast_im, Complex.one_re, Complex.one_im, zero_mul, sub_zero, add_zero] at e1 e2
  exact ⟨e1, e2⟩

/-- `∑ k cos (2π k / N) = -N / 2`. -/
lemma sum_mul_cos {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ range N, (k : ℝ) * Real.cos (2 * Real.pi * k / N) = -(N : ℝ) / 2 := by
  obtain ⟨e1, e2⟩ := eqs_mul hN
  have pyth := Real.sin_sq_add_cos_sq (2 * Real.pi / N)
  refine mul_right_cancel₀ (one_sub_cos_ne_zero hN) ?_
  set A := ∑ k ∈ range N, (k : ℝ) * Real.cos (2 * Real.pi * k / N)
  set c := Real.cos (2 * Real.pi / N)
  set s := Real.sin (2 * Real.pi / N)
  linear_combination (1 / 2) * ((c - 1) * e1 + s * e2 - A * pyth)

/-- `∑ k sin (2π k / N) = -N sin (2π / N) / (2 (1 - cos (2π / N)))`. -/
lemma sum_mul_sin {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ range N, (k : ℝ) * Real.sin (2 * Real.pi * k / N) =
      -((N : ℝ) * Real.sin (2 * Real.pi / N)) / (2 * (1 - Real.cos (2 * Real.pi / N))) := by
  obtain ⟨e1, e2⟩ := eqs_mul hN
  have pyth := Real.sin_sq_add_cos_sq (2 * Real.pi / N)
  have h1c := one_sub_cos_ne_zero hN
  rw [eq_div_iff (mul_ne_zero two_ne_zero h1c)]
  set B := ∑ k ∈ range N, (k : ℝ) * Real.sin (2 * Real.pi * k / N)
  set c := Real.cos (2 * Real.pi / N)
  set s := Real.sin (2 * Real.pi / N)
  linear_combination (-s) * e1 + (c - 1) * e2 - B * pyth

/-- `∑ sin (2π k / N) = 0`. -/
lemma sum_sin_two_pi_div {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ range N, Real.sin (2 * Real.pi * k / N) = 0 := by
  have h : ∑ k ∈ range N, root N ^ k = 0 :=
    (Complex.isPrimitiveRoot_exp N (by omega)).geom_sum_eq_zero hN
  have := congrArg Complex.im h
  simpa [Complex.im_sum, root_pow_im] using this

/-- `∑ k² cos (2π k / N) = -N² / 2 + N / (1 - cos (2π / N))`. -/
lemma sum_sq_mul_cos {N : ℕ} (hN : 2 ≤ N) :
    ∑ k ∈ range N, (k : ℝ) ^ 2 * Real.cos (2 * Real.pi * k / N) =
      -(N : ℝ) ^ 2 / 2 + N / (1 - Real.cos (2 * Real.pi / N)) := by
  have h := sum_sq_mul_root hN
  have e3 := congrArg Complex.re h
  have e4 := congrArg Complex.im h
  simp only [pow_two (root N - 1), Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.re_sum, Complex.im_sum, root_re, root_im, root_pow_re, root_pow_im, Complex.natCast_re,
    Complex.natCast_im, Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
    zero_mul, sub_zero, add_zero] at e3 e4
  push_cast at e3 e4
  have pyth := Real.sin_sq_add_cos_sq (2 * Real.pi / N)
  have h1c := one_sub_cos_ne_zero hN
  set A := ∑ k ∈ range N, (k : ℝ) ^ 2 * Real.cos (2 * Real.pi * k / N)
  set B := ∑ k ∈ range N, (k : ℝ) ^ 2 * Real.sin (2 * Real.pi * k / N)
  set c := Real.cos (2 * Real.pi / N)
  set s := Real.sin (2 * Real.pi / N)
  have key : A * (1 - c) = N - (N : ℝ) ^ 2 * (1 - c) / 2 := by
    refine mul_right_cancel₀ (mul_ne_zero (four_ne_zero) h1c) ?_
    linear_combination ((c - 1) * (c - 1) - s * s) * e3 + (2 * (c - 1) * s) * e4 +
      (-A * c ^ 2 + 4 * A * c - A * s ^ 2 - 3 * A + (N : ℝ) ^ 2 * c - (N : ℝ) ^ 2 -
        2 * N * c + 4 * N) * pyth
  have hA : A = (N - (N : ℝ) ^ 2 * (1 - c) / 2) / (1 - c) := by
    rw [eq_div_iff h1c]
    exact key
  rw [hA]
  field_simp
  ring

end PathObservables
