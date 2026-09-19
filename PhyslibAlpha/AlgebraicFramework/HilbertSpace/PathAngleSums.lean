/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathExtremalState
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathPeriodSums

/-!

# Sums over the basis in terms of `θ = π / (d + 1)`

The period sums at `N = d + 1`, and the sums over `Fin d` of the squared sines, weighted by the
centered coordinate, that the extremal state needs.

-/

@[expose] public section

open Finset

namespace PathObservables

/-! ## Sums over the basis, in terms of `θ = π / (d + 1)` -/

/-- Shifting the index `j ↦ j + 1` from `Fin d` to `range (d + 1)`, when the summand vanishes at
`0`. -/
lemma sum_fin_succ (d : ℕ) (g : ℕ → ℝ) (h0 : g 0 = 0) :
    ∑ j : Fin d, g ((j : ℕ) + 1) = ∑ k ∈ range (d + 1), g k := by
  rw [Fin.sum_univ_eq_sum_range (fun j => g (j + 1)) d, sum_range_succ', h0, add_zero]

lemma two_pi_div_eq (d k : ℕ) : 2 * Real.pi * k / ((d : ℝ) + 1) = 2 * (k * angle d) := by
  unfold angle
  ring

lemma two_pi_div_one (d : ℕ) : 2 * Real.pi / ((d : ℝ) + 1) = 2 * angle d := by
  unfold angle
  ring

lemma sum_range_id_real (n : ℕ) : ∑ k ∈ range n, (k : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

lemma sum_range_sq_real (n : ℕ) :
    ∑ k ∈ range n, (k : ℝ) ^ 2 = (n : ℝ) * ((n : ℝ) - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- `∑ cos² ((j + 1) θ) = (d - 1) / 2`. -/
lemma sum_cos_sq_angle {d : ℕ} (hd : 1 ≤ d) :
    ∑ j : Fin d, Real.cos (((j : ℕ) + 1) * angle d) ^ 2 = ((d : ℝ) - 1) / 2 := by
  have h := sum_sin_sq_angle d hd
  have h1 : ∀ j : Fin d, Real.cos (((j : ℕ) + 1) * angle d) ^ 2 =
      1 - Real.sin (((j : ℕ) + 1) * angle d) ^ 2 := fun j => Real.cos_sq' _
  simp_rw [h1, sum_sub_distrib, h]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

lemma sin_angle_pos {d : ℕ} (hd : 1 ≤ d) : 0 < Real.sin (angle d) := by
  have h : 0 < angle d := by unfold angle; positivity
  have h2 : angle d < Real.pi := by
    unfold angle
    rw [div_lt_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith [Real.pi_pos]
  exact Real.sin_pos_of_pos_of_lt_pi h h2

lemma one_sub_cos_two_angle (d : ℕ) :
    1 - Real.cos (2 * angle d) = 2 * Real.sin (angle d) ^ 2 := by
  rw [Real.cos_two_mul, Real.cos_sq']
  ring

/-- The period sums of `PathExtremalState` and `PathPeriodSums`, at `N = d + 1` and in terms of
`θ`. -/
lemma sum_cos_two_angle {d : ℕ} (hd : 1 ≤ d) :
    ∑ k ∈ range (d + 1), Real.cos (2 * (k * angle d)) = 0 := by
  have := sum_cos_two_pi_div (n := d + 1) (by omega)
  simpa only [Nat.cast_add, Nat.cast_one, two_pi_div_eq] using this

lemma sum_sin_two_angle {d : ℕ} (hd : 1 ≤ d) :
    ∑ k ∈ range (d + 1), Real.sin (2 * (k * angle d)) = 0 := by
  have := sum_sin_two_pi_div (N := d + 1) (by omega)
  simpa only [Nat.cast_add, Nat.cast_one, two_pi_div_eq] using this

lemma sum_mul_cos_angle {d : ℕ} (hd : 1 ≤ d) :
    ∑ k ∈ range (d + 1), (k : ℝ) * Real.cos (2 * (k * angle d)) = -((d : ℝ) + 1) / 2 := by
  have := sum_mul_cos (N := d + 1) (by omega)
  simpa only [Nat.cast_add, Nat.cast_one, two_pi_div_eq] using this

lemma sum_mul_sin_angle {d : ℕ} (hd : 1 ≤ d) :
    ∑ k ∈ range (d + 1), (k : ℝ) * Real.sin (2 * (k * angle d)) =
      -(((d : ℝ) + 1) * Real.cos (angle d)) / (2 * Real.sin (angle d)) := by
  have h := sum_mul_sin (N := d + 1) (by omega)
  simp only [Nat.cast_add, Nat.cast_one, two_pi_div_eq, two_pi_div_one] at h
  rw [h, Real.sin_two_mul, one_sub_cos_two_angle]
  have hs := (sin_angle_pos hd).ne'
  field_simp

lemma sum_sq_mul_cos_angle {d : ℕ} (hd : 1 ≤ d) :
    ∑ k ∈ range (d + 1), (k : ℝ) ^ 2 * Real.cos (2 * (k * angle d)) =
      -((d : ℝ) + 1) ^ 2 / 2 + ((d : ℝ) + 1) / (2 * Real.sin (angle d) ^ 2) := by
  have h := sum_sq_mul_cos (N := d + 1) (by omega)
  simp only [Nat.cast_add, Nat.cast_one, two_pi_div_eq, two_pi_div_one] at h
  rw [h, one_sub_cos_two_angle]

/-- `∑ (2k - N) sin² (kθ) = 0` over a period, `N = d + 1`. -/
lemma sum_range_pos_sin_sq {d : ℕ} (hd : 1 ≤ d) :
    ∑ k ∈ range (d + 1), (2 * (k : ℝ) - ((d : ℝ) + 1)) * Real.sin (k * angle d) ^ 2 = 0 := by
  have hterm : ∀ k : ℕ, (2 * (k : ℝ) - ((d : ℝ) + 1)) * Real.sin (k * angle d) ^ 2 =
      (k : ℝ) - ((d : ℝ) + 1) / 2 - ((k : ℝ) * Real.cos (2 * (k * angle d)) -
        ((d : ℝ) + 1) / 2 * Real.cos (2 * (k * angle d))) := by
    intro k
    rw [Real.sin_sq_eq_half_sub]
    ring
  rw [sum_congr rfl fun k _ => hterm k, sum_sub_distrib, sum_sub_distrib, sum_sub_distrib,
    ← mul_sum, sum_mul_cos_angle hd, sum_cos_two_angle hd, sum_range_id_real]
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, sum_const, card_range,
    nsmul_eq_mul, neg_add_rev, mul_zero, sub_zero]
  ring

/-- `∑ (2k - N)² sin² (kθ) = N (N² + 2) / 6 - N / sin² θ`, `N = d + 1`. -/
lemma sum_range_pos_sq_sin_sq {d : ℕ} (hd : 1 ≤ d) :
    ∑ k ∈ range (d + 1), (2 * (k : ℝ) - ((d : ℝ) + 1)) ^ 2 * Real.sin (k * angle d) ^ 2 =
      ((d : ℝ) + 1) * (((d : ℝ) + 1) ^ 2 + 2) / 6 - ((d : ℝ) + 1) / Real.sin (angle d) ^ 2 := by
  have hterm : ∀ k : ℕ, (2 * (k : ℝ) - ((d : ℝ) + 1)) ^ 2 * Real.sin (k * angle d) ^ 2 =
      2 * (k : ℝ) ^ 2 - 2 * ((d : ℝ) + 1) * k + ((d : ℝ) + 1) ^ 2 / 2 -
        (2 * ((k : ℝ) ^ 2 * Real.cos (2 * (k * angle d))) -
          2 * ((d : ℝ) + 1) * ((k : ℝ) * Real.cos (2 * (k * angle d))) +
          ((d : ℝ) + 1) ^ 2 / 2 * Real.cos (2 * (k * angle d))) := by
    intro k
    rw [Real.sin_sq_eq_half_sub]
    ring
  rw [sum_congr rfl fun k _ => hterm k, sum_sub_distrib, sum_add_distrib, sum_sub_distrib,
    sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum, ← mul_sum,
    sum_sq_mul_cos_angle hd, sum_mul_cos_angle hd, sum_cos_two_angle hd, sum_range_id_real,
    sum_range_sq_real]
  have hs := (sin_angle_pos hd).ne'
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, sum_const, card_range,
    nsmul_eq_mul, neg_add_rev, mul_zero, add_zero]
  field_simp
  ring

/-- `∑ (2k - N) sin (2kθ) = -N cos θ / sin θ`, `N = d + 1`. -/
lemma sum_range_pos_sin_two {d : ℕ} (hd : 1 ≤ d) :
    ∑ k ∈ range (d + 1), (2 * (k : ℝ) - ((d : ℝ) + 1)) * Real.sin (2 * (k * angle d)) =
      -(((d : ℝ) + 1) * Real.cos (angle d)) / Real.sin (angle d) := by
  have hterm : ∀ k : ℕ, (2 * (k : ℝ) - ((d : ℝ) + 1)) * Real.sin (2 * (k * angle d)) =
      2 * ((k : ℝ) * Real.sin (2 * (k * angle d))) -
        ((d : ℝ) + 1) * Real.sin (2 * (k * angle d)) := by
    intro k
    ring
  rw [sum_congr rfl fun k _ => hterm k, sum_sub_distrib, ← mul_sum, ← mul_sum,
    sum_mul_sin_angle hd, sum_sin_two_angle hd]
  have hs := (sin_angle_pos hd).ne'
  field_simp
  ring

end PathObservables
