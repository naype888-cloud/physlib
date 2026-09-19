/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.NavaCoherenceLowDim
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.NavaCoherenceThreshold

/-!

# `1 < C_Nava (d) ^ 2` for `d ≥ 4`

For `d ≥ 6` and `N = d + 1`, the bound `cos (π / N) ^ 2 < 1 - s ^ 2` with
`s = (3.14 / N) (1 - (3.15 / N) ^ 2 / 6)` lies below the threshold `thrCNava d`, because
`s ^ 2 ≥ 3.14 ^ 2 / N ^ 2 * (1 - 3.15 ^ 2 / (3 N ^ 2))` and `1 - thrCNava d = (9 N - 12) / (N ^ 3
- 2 N ^ 2 + 5 N - 4)`. The cases `d = 4, 5` are the explicit values of `NavaCoherenceLowDim`.

-/

@[expose] public section

open Real

namespace PathObservables

/-! ## A lower bound for the square of the sine bound -/

/-- `(3.14 / N (1 - (3.15 / N) ^ 2 / 6)) ^ 2 ≥ 3.14 ^ 2 / N ^ 2 * (1 - 3.15 ^ 2 / (3 N ^ 2))`. -/
lemma sq_sinBound_ge {N : ℝ} (hN : 0 < N) :
    ((314 : ℝ) / 100) ^ 2 / N ^ 2 * (1 - ((315 : ℝ) / 100) ^ 2 / (3 * N ^ 2)) ≤
      (((314 : ℝ) / 100 / N) * (1 - ((315 : ℝ) / 100 / N) ^ 2 / 6)) ^ 2 := by
  have hleft : (((314 : ℝ) / 100 / N) * (1 - ((315 : ℝ) / 100 / N) ^ 2 / 6)) ^ 2 =
      ((314 : ℝ) / 100) ^ 2 / N ^ 2 * (1 - ((315 : ℝ) / 100 / N) ^ 2 / 6) ^ 2 := by
    rw [mul_pow, div_pow]
  have hsq : (1 - ((315 : ℝ) / 100 / N) ^ 2 / 6) ^ 2 ≥
      1 - 2 * (((315 : ℝ) / 100 / N) ^ 2 / 6) := by
    nlinarith [sq_nonneg (((315 : ℝ) / 100 / N) ^ 2 / 6)]
  have h2u : 2 * (((315 : ℝ) / 100 / N) ^ 2 / 6) = ((315 : ℝ) / 100) ^ 2 / (3 * N ^ 2) := by
    field_simp [hN.ne']
    ring
  rw [hleft]
  nlinarith [hsq, show (0 : ℝ) ≤ ((314 : ℝ) / 100) ^ 2 / N ^ 2 by positivity, h2u]

/-! ## The complement of the threshold -/

/-- `1 - thrCNava d = (9 N - 12) / (N ^ 3 - 2 N ^ 2 + 5 N - 4)` for `N = d + 1` and `2 ≤ d`. -/
lemma one_sub_thr_eq (d : ℕ) (hd : 2 ≤ d) :
    1 - thrCNava d =
      (9 * ((d : ℝ) + 1) - 12) /
        (((d : ℝ) + 1) ^ 3 - 2 * ((d : ℝ) + 1) ^ 2 + 5 * ((d : ℝ) + 1) - 4) := by
  set N := (d : ℝ) + 1
  have hd1 : (d : ℝ) - 1 = N - 2 := by ring
  have hden0 : (N - 2) * (N ^ 2 + 2) + 3 * N ≠ 0 := by
    have : 0 < N - 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    positivity
  have hthr : thrCNava d = (N - 2) * (N ^ 2 - 4) / ((N - 2) * (N ^ 2 + 2) + 3 * N) := by
    unfold thrCNava
    rw [hd1]
  have hD : (N - 2) * (N ^ 2 + 2) + 3 * N = N ^ 3 - 2 * N ^ 2 + 5 * N - 4 := by ring
  rw [hthr, hD]
  have hden : N ^ 3 - 2 * N ^ 2 + 5 * N - 4 ≠ 0 := by
    rw [← hD]
    exact hden0
  rw [one_sub_div hden]
  congr 1
  ring

/-- For `6 ≤ d`, `1 - thrCNava d` is below the square of the sine bound at `N = d + 1`. -/
lemma one_sub_thr_lt_sq {d : ℕ} (hd : 6 ≤ d) :
    1 - thrCNava d <
      (((314 : ℝ) / 100 / ((d : ℝ) + 1)) *
        (1 - ((315 : ℝ) / 100 / ((d : ℝ) + 1)) ^ 2 / 6)) ^ 2 := by
  set N := (d : ℝ) + 1
  have hN : (7 : ℝ) ≤ N := by
    have : (6 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hNpos : 0 < N := by positivity
  have hN2pos : 0 < N ^ 2 := sq_pos_of_pos hNpos
  have hden_pos : 0 < N ^ 3 - 2 * N ^ 2 + 5 * N - 4 := by nlinarith [hN, hNpos]
  have hkey : ((314 : ℝ) / 100) ^ 2 * (1 - ((315 : ℝ) / 100) ^ 2 / (3 * N ^ 2)) *
      (N ^ 3 - 2 * N ^ 2 + 5 * N - 4) > (9 * N - 12) * N ^ 2 := by
    simpa [N] using polynomial_bound_of_seven_le (d + 1) (by omega)
  have h1 : 1 - thrCNava d = (9 * N - 12) / (N ^ 3 - 2 * N ^ 2 + 5 * N - 4) := by
    simpa [N] using one_sub_thr_eq d (by omega)
  have hlo : ((314 : ℝ) / 100) ^ 2 / N ^ 2 * (1 - ((315 : ℝ) / 100) ^ 2 / (3 * N ^ 2)) *
      (N ^ 3 - 2 * N ^ 2 + 5 * N - 4) > 9 * N - 12 := by
    have hL : ((314 : ℝ) / 100) ^ 2 / N ^ 2 * (1 - ((315 : ℝ) / 100) ^ 2 / (3 * N ^ 2)) *
        (N ^ 3 - 2 * N ^ 2 + 5 * N - 4) =
        (((314 : ℝ) / 100) ^ 2 * (1 - ((315 : ℝ) / 100) ^ 2 / (3 * N ^ 2)) *
          (N ^ 3 - 2 * N ^ 2 + 5 * N - 4)) / N ^ 2 := by
      field_simp
    have hdiv := div_lt_div_of_pos_right hkey hN2pos
    have hR : ((9 * N - 12) * N ^ 2) / N ^ 2 = 9 * N - 12 := by
      field_simp
    rw [hL]
    rwa [hR] at hdiv
  have hmul : 9 * N - 12 <
      (((314 : ℝ) / 100 / N) * (1 - ((315 : ℝ) / 100 / N) ^ 2 / 6)) ^ 2 *
        (N ^ 3 - 2 * N ^ 2 + 5 * N - 4) := by
    nlinarith [sq_sinBound_ge hNpos, hlo, hden_pos]
  rw [h1]
  exact (div_lt_iff₀ hden_pos).mpr hmul

/-! ## Positivity of the defect for `d ≥ 4` -/

/-- `1 < C_Nava d ^ 2` for `6 ≤ d`. -/
lemma one_lt_CNavaSq_of_six_le {d : ℕ} (hd : 6 ≤ d) : 1 < CNavaSq d := by
  have hN : (7 : ℝ) ≤ (d : ℝ) + 1 := by
    have : (6 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hcos_ub := cos_sq_bound_of_seven_le ((d : ℝ) + 1) hN
  have hcos_thr : cos (angle d) ^ 2 < thrCNava d := by
    have h := one_sub_thr_lt_sq hd
    change cos (π / ((d : ℝ) + 1)) ^ 2 < _ at hcos_ub
    change cos (π / ((d : ℝ) + 1)) ^ 2 < _
    linarith
  exact one_lt_CNavaSq_of_cos_lt_thr d (by omega) (cos_angle_pos (by omega)) hcos_thr

/-- `1 < C_Nava d ^ 2` for every `d ≥ 4`. -/
lemma one_lt_CNavaSq {d : ℕ} (hd : 4 ≤ d) : 1 < CNavaSq d := by
  match d with
  | 0 | 1 | 2 | 3 => omega
  | 4 => exact one_lt_CNavaSq_four
  | 5 => exact one_lt_CNavaSq_five
  | n + 6 => exact one_lt_CNavaSq_of_six_le (by omega)

end PathObservables
