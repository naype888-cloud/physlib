/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.NavaRobertsonDefect

/-!

# A threshold criterion for `1 < C_Nava (d) ^ 2`

Write `N = d + 1` and `c = cos (π / N) ^ 2`. Since `sin ^ 2 = 1 - c`,
`C_Nava d ^ 2 = (d - 1) / (3 N c) * ((N ^ 2 - 4) - (N ^ 2 + 2) c)`. For `2 ≤ d`, this is greater
than one whenever `c` lies below an explicit rational threshold `thrCNava d`.

We also prove a polynomial inequality for `n ≥ 7`, which is used to compare that threshold with the
bound on `cos (π / N) ^ 2` for `N ≥ 7`.

-/

@[expose] public section

open Real

namespace PathObservables

/-! ## `C_Nava (d) ^ 2` in terms of the cosine -/

/-- `C_Nava d ^ 2` in terms of `cos (π / (d + 1)) ^ 2` only. -/
lemma CNavaSq_eq_cos_form (d : ℕ) (hcos_ne : cos (angle d) ≠ 0) :
    CNavaSq d =
      ((d : ℝ) - 1) / (3 * ((d : ℝ) + 1) * cos (angle d) ^ 2) *
        ((((d : ℝ) + 1) ^ 2 - 4) - (((d : ℝ) + 1) ^ 2 + 2) * cos (angle d) ^ 2) := by
  have hs : sin (angle d) ^ 2 = 1 - cos (angle d) ^ 2 := by
    rw [← sin_sq_add_cos_sq (angle d)]
    ring
  have hN0 : ((d : ℝ) + 1) ≠ 0 := by positivity
  unfold CNavaSq
  rw [hs]
  field_simp
  ring

/-! ## The threshold -/

/-- The threshold `((d - 1) (N ^ 2 - 4)) / ((d - 1) (N ^ 2 + 2) + 3 N)` for `N = d + 1`. -/
noncomputable def thrCNava (d : ℕ) : ℝ :=
  ((d : ℝ) - 1) * (((d : ℝ) + 1) ^ 2 - 4) /
    (((d : ℝ) - 1) * (((d : ℝ) + 1) ^ 2 + 2) + 3 * ((d : ℝ) + 1))

/-- If `cos (π / (d + 1)) ^ 2` is below `thrCNava d`, then `1 < C_Nava d ^ 2`. -/
lemma one_lt_CNavaSq_of_cos_lt_thr (d : ℕ) (hd : 2 ≤ d) (hcos_pos : 0 < cos (angle d))
    (hthr : cos (angle d) ^ 2 < thrCNava d) : 1 < CNavaSq d := by
  set N := (d : ℝ) + 1
  set c := cos (angle d) ^ 2
  have hcpos : 0 < c := sq_pos_of_pos hcos_pos
  have hform : CNavaSq d = ((d : ℝ) - 1) / (3 * N * c) * ((N ^ 2 - 4) - (N ^ 2 + 2) * c) :=
    CNavaSq_eq_cos_form d hcos_pos.ne'
  have hNpos : 0 < N := by positivity
  have hden : 0 < 3 * N * c := by positivity
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have ha : 0 < (d : ℝ) - 1 := by linarith
  have hthr' : c < ((d : ℝ) - 1) * (N ^ 2 - 4) / (((d : ℝ) - 1) * (N ^ 2 + 2) + 3 * N) := by
    simpa [c, N, thrCNava] using hthr
  have hden' : 0 < ((d : ℝ) - 1) * (N ^ 2 + 2) + 3 * N := by positivity
  have hN2 : 0 < N ^ 2 - 4 := by
    have : (3 : ℝ) ≤ N := by linarith
    nlinarith
  have hthr_mul : c * (((d : ℝ) - 1) * (N ^ 2 + 2) + 3 * N) < ((d : ℝ) - 1) * (N ^ 2 - 4) :=
    (lt_div_iff₀ hden').mp hthr'
  have he : 0 < (N ^ 2 - 4) - (N ^ 2 + 2) * c := by
    have hcmp : ((d : ℝ) - 1) * (N ^ 2 - 4) / (((d : ℝ) - 1) * (N ^ 2 + 2) + 3 * N) <
        (N ^ 2 - 4) / (N ^ 2 + 2) := by
      rw [div_lt_div_iff₀ hden' (by positivity)]
      nlinarith [hN2, ha, hNpos]
    have hc_mid : c < (N ^ 2 - 4) / (N ^ 2 + 2) := lt_trans hthr' hcmp
    have : c * (N ^ 2 + 2) < N ^ 2 - 4 := (lt_div_iff₀ (by positivity)).mp hc_mid
    linarith
  have hmul : ((d : ℝ) - 1) * ((N ^ 2 - 4) - (N ^ 2 + 2) * c) > 3 * N * c := by
    nlinarith [hthr_mul]
  have hgt : ((d : ℝ) - 1) / (3 * N * c) * ((N ^ 2 - 4) - (N ^ 2 + 2) * c) > 1 := by
    have : ((d : ℝ) - 1) * ((N ^ 2 - 4) - (N ^ 2 + 2) * c) / (3 * N * c) > 1 :=
      (one_lt_div hden).mpr hmul
    convert this using 1
    ring
  rwa [hform]

/-! ## A polynomial inequality -/

/-- For `7 ≤ n`, `3.14 ^ 2 * (1 - 3.15 ^ 2 / (3 n ^ 2)) * (n ^ 3 - 2 n ^ 2 + 5 n - 4)` is larger
than `(9 n - 12) n ^ 2`. We check `n ≤ 40` by computation and handle `n > 40` by linear bounds. -/
lemma polynomial_bound_of_seven_le (n : ℕ) (hn : 7 ≤ n) :
    ((314 : ℝ) / 100) ^ 2 * (1 - ((315 : ℝ) / 100) ^ 2 / (3 * (n : ℝ) ^ 2)) *
        ((n : ℝ) ^ 3 - 2 * (n : ℝ) ^ 2 + 5 * (n : ℝ) - 4) >
      (9 * (n : ℝ) - 12) * (n : ℝ) ^ 2 := by
  by_cases hle : n ≤ 40
  · interval_cases n <;> norm_num
  · have hnR : (41 : ℝ) ≤ n := by exact_mod_cast (show 41 ≤ n by omega)
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 41) hnR
    have h314 : ((314 : ℝ) / 100) ^ 2 ≥ (985 : ℝ) / 100 := by norm_num
    have hfac : 1 - ((315 : ℝ) / 100) ^ 2 / (3 * (n : ℝ) ^ 2) ≥ (99 : ℝ) / 100 := by
      have hle' : ((315 : ℝ) / 100) ^ 2 / (3 * (n : ℝ) ^ 2) ≤
          ((315 : ℝ) / 100) ^ 2 / (3 * 41 ^ 2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [hnR]
      have : ((315 : ℝ) / 100) ^ 2 / (3 * 41 ^ 2) ≤ (1 : ℝ) / 100 := by norm_num
      linarith
    have hden : (n : ℝ) ^ 3 - 2 * (n : ℝ) ^ 2 + 5 * (n : ℝ) - 4 ≥
        (n : ℝ) ^ 3 - 2 * (n : ℝ) ^ 2 := by
      nlinarith [hnpos]
    have hden' : (n : ℝ) ^ 3 - 2 * (n : ℝ) ^ 2 = (n : ℝ) ^ 2 * ((n : ℝ) - 2) := by ring
    have hmain : ((985 : ℝ) / 100) * ((99 : ℝ) / 100) * ((n : ℝ) - 2) > 9 * (n : ℝ) - 12 := by
      nlinarith [hnR]
    have hfacpos : (0 : ℝ) < 1 - ((315 : ℝ) / 100) ^ 2 / (3 * (n : ℝ) ^ 2) := by
      linarith [hfac]
    have hdenpos : (0 : ℝ) < (n : ℝ) ^ 3 - 2 * (n : ℝ) ^ 2 + 5 * (n : ℝ) - 4 := by
      nlinarith [hnR]
    nlinarith [h314, hfac, hden, hden', hmain, hfacpos, hdenpos,
      show (0 : ℝ) ≤ (n : ℝ) ^ 2 by positivity]

end PathObservables
