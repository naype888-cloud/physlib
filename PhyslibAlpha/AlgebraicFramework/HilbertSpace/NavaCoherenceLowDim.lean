/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.NavaRobertsonDefect

/-!

# The constant `C_Nava (d) ^ 2` in dimensions two to six

`CNavaSq d = 1` for `d = 2` and `d = 3`, and `1 < CNavaSq d` for `d = 4, 5, 6`.

For `d = 2, 3, 5` the angle `π / (d + 1)` is one of `π / 3, π / 4, π / 6`, and for `d = 4` it is
`π / 5`, where `cos` and `sin` have closed forms in Mathlib. For `d = 6` the angle is `π / 7`, and
we use an upper bound on `cos (π / N) ^ 2` for all `N ≥ 7`, obtained from the Taylor bound
`x - x ^ 3 / 6 < sin x` together with the bounds on `π`.

-/

@[expose] public section

open Real

namespace PathObservables

/-! ## The values in dimensions two and three -/

/-- `C_Nava 2 ^ 2 = 1`. -/
lemma CNavaSq_two : CNavaSq 2 = 1 := by
  simp only [CNavaSq, angle, Nat.cast_ofNat]
  rw [show (2 : ℝ) + 1 = 3 by norm_num, show (2 : ℝ) - 1 = 1 by norm_num]
  rw [cos_pi_div_three, sin_pi_div_three]
  have h3 : (√3) ^ 2 = (3 : ℝ) := sq_sqrt (by norm_num)
  have hs : (√3 / 2) ^ 2 = (3 : ℝ) / 4 := by rw [div_pow, h3]; norm_num
  simp [hs]
  norm_num

/-- `C_Nava 3 ^ 2 = 1`. -/
lemma CNavaSq_three : CNavaSq 3 = 1 := by
  simp only [CNavaSq, angle, Nat.cast_ofNat]
  rw [show (3 : ℝ) + 1 = 4 by norm_num, show (3 : ℝ) - 1 = 2 by norm_num]
  rw [cos_pi_div_four, sin_pi_div_four]
  have h2 : (√2) ^ 2 = (2 : ℝ) := sq_sqrt (by norm_num)
  have hs : (√2 / 2) ^ 2 = (2 : ℝ) / 4 := by rw [div_pow, h2]; norm_num
  simp [hs]
  norm_num

/-! ## The values in dimensions four and five -/

/-- `C_Nava 4 ^ 2 = (99 - 42 √5) / 5`. -/
lemma CNavaSq_four : CNavaSq 4 = (99 - 42 * √5) / 5 := by
  simp only [CNavaSq, angle, Nat.cast_ofNat]
  rw [show (4 : ℝ) + 1 = 5 by norm_num, show (4 : ℝ) - 1 = 3 by norm_num]
  have hc0 : cos (π / 5) = (1 + √5) / 4 := cos_pi_div_five
  have hs5 : (√5) ^ 2 = (5 : ℝ) := sq_sqrt (by norm_num)
  have hcos2 : cos (π / 5) ^ 2 = (3 + √5) / 8 := by
    rw [hc0]
    ring_nf
    simp [hs5]
    ring
  have hsin2 : sin (π / 5) ^ 2 = (5 - √5) / 8 := by
    have : sin (π / 5) ^ 2 = 1 - cos (π / 5) ^ 2 := by
      rw [← sin_sq_add_cos_sq (π / 5)]
      ring
    rw [this, hcos2]
    ring
  rw [hcos2, hsin2]
  ring_nf
  field_simp
  ring_nf
  simp [hs5]
  ring

/-- `1 < C_Nava 4 ^ 2`. -/
lemma one_lt_CNavaSq_four : 1 < CNavaSq 4 := by
  rw [CNavaSq_four]
  have h5 : (0 : ℝ) < 5 := by norm_num
  rw [one_lt_div h5]
  have h : √5 < (47 : ℝ) / 21 := by
    rw [sqrt_lt (by norm_num : (0 : ℝ) ≤ 5) (by positivity)]
    norm_num
  have hs : (√5) ^ 2 = (5 : ℝ) := sq_sqrt (by norm_num)
  nlinarith [hs, h, sqrt_nonneg 5]

/-- `C_Nava 5 ^ 2 = 28 / 27`. -/
lemma CNavaSq_five : CNavaSq 5 = (28 : ℝ) / 27 := by
  simp only [CNavaSq, angle, Nat.cast_ofNat]
  rw [show (5 : ℝ) + 1 = 6 by norm_num, show (5 : ℝ) - 1 = 4 by norm_num]
  rw [cos_pi_div_six, sin_pi_div_six]
  have h3 : (√3) ^ 2 = (3 : ℝ) := sq_sqrt (by norm_num)
  have hc : (√3 / 2) ^ 2 = (3 : ℝ) / 4 := by rw [div_pow, h3]; norm_num
  simp [hc]
  norm_num

/-- `1 < C_Nava 5 ^ 2`. -/
lemma one_lt_CNavaSq_five : 1 < CNavaSq 5 := by
  rw [CNavaSq_five]
  norm_num

/-! ## The bound on the cosine for `N ≥ 7` -/

/-- For `7 ≤ N`, an upper bound on `cos (π / N) ^ 2`, from `sin x > x - x ^ 3 / 6` and
`3.14 < π < 3.15`. -/
lemma cos_sq_bound_of_seven_le (N : ℝ) (hN : (7 : ℝ) ≤ N) :
    cos (π / N) ^ 2 <
      1 - (((314 : ℝ) / 100 / N) * (1 - ((315 : ℝ) / 100 / N) ^ 2 / 6)) ^ 2 := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7) hN
  set θ := π / N
  have hθpos : 0 < θ := div_pos pi_pos hNpos
  have hπlo : (314 : ℝ) / 100 < π := by
    have := pi_gt_d2
    norm_num at this ⊢
    linarith
  have hπhi : π < (315 : ℝ) / 100 := by
    have := pi_lt_d2
    norm_num at this ⊢
    linarith
  have hθle : θ ≤ π / 7 := by
    rw [div_le_div_iff₀ hNpos (by norm_num : (0 : ℝ) < 7)]
    nlinarith [pi_pos, hN]
  have hθlt1 : θ < 1 := by
    have h1 : π / 7 < (315 : ℝ) / 100 / 7 := div_lt_div_of_pos_right hπhi (by norm_num)
    have h2 : ((315 : ℝ) / 100 / 7) < 1 := by norm_num
    exact lt_of_le_of_lt hθle (lt_trans h1 h2)
  have hs0pos : 0 < θ - θ ^ 3 / 6 := by
    have : θ ^ 2 < 6 := by nlinarith [hθpos, hθlt1]
    nlinarith [hθpos, this]
  have hsin : θ - θ ^ 3 / 6 < sin θ := sin_gt_sub_cube hθpos
  set s0 := θ - θ ^ 3 / 6
  set s0lo := ((314 : ℝ) / 100 / N) * (1 - ((315 : ℝ) / 100 / N) ^ 2 / 6)
  have hcos2 : cos θ ^ 2 < 1 - s0 ^ 2 := by
    have hsq : s0 ^ 2 < sin θ ^ 2 := pow_lt_pow_left₀ hsin hs0pos.le (by norm_num)
    have : cos θ ^ 2 = 1 - sin θ ^ 2 := by
      rw [← sin_sq_add_cos_sq θ]
      ring
    linarith
  have hfac_s0lo_pos : 0 ≤ 1 - ((315 : ℝ) / 100 / N) ^ 2 / 6 := by
    have hle : ((315 : ℝ) / 100 / N) ^ 2 / 6 ≤ ((315 : ℝ) / 100 / 7) ^ 2 / 6 := by
      have : (315 : ℝ) / 100 / N ≤ (315 : ℝ) / 100 / 7 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hN
      nlinarith [this, show (0 : ℝ) ≤ 315 / 100 / N by positivity]
    have : ((315 : ℝ) / 100 / 7) ^ 2 / 6 < 1 := by norm_num
    linarith
  have hs0_ge : s0 ≥ s0lo := by
    have hs0θ : s0 = θ * (1 - θ ^ 2 / 6) := by ring
    have hθlo : (314 : ℝ) / 100 / N ≤ θ := by
      change (314 : ℝ) / 100 / N ≤ π / N
      exact div_le_div_of_nonneg_right hπlo.le hNpos.le
    have hθhi2 : θ ≤ (315 : ℝ) / 100 / N := by
      change π / N ≤ (315 : ℝ) / 100 / N
      exact div_le_div_of_nonneg_right hπhi.le hNpos.le
    have hfac : 1 - θ ^ 2 / 6 ≥ 1 - ((315 : ℝ) / 100 / N) ^ 2 / 6 := by
      nlinarith [hθpos, hθhi2]
    have hfacθ : 0 ≤ 1 - θ ^ 2 / 6 := by
      have : θ ^ 2 ≤ 1 := by nlinarith [hθpos, hθlt1]
      nlinarith
    have ha : (0 : ℝ) ≤ (314 : ℝ) / 100 / N := by positivity
    rw [hs0θ]
    calc
      θ * (1 - θ ^ 2 / 6)
          ≥ ((314 : ℝ) / 100 / N) * (1 - θ ^ 2 / 6) := mul_le_mul_of_nonneg_right hθlo hfacθ
      _ ≥ ((314 : ℝ) / 100 / N) * (1 - ((315 : ℝ) / 100 / N) ^ 2 / 6) :=
          mul_le_mul_of_nonneg_left hfac ha
  have hpos_lo : 0 ≤ s0lo := by positivity
  have hs0sq : s0 ^ 2 ≥ s0lo ^ 2 := pow_le_pow_left₀ hpos_lo hs0_ge 2
  linarith [hcos2, hs0sq]

/-- `cos (π / 7) ^ 2` is positive and below `75 / 92`. -/
lemma cos_sq_pi_div_seven_bounds :
    0 < cos (π / 7) ^ 2 ∧ cos (π / 7) ^ 2 < (75 : ℝ) / 92 := by
  refine ⟨sq_pos_of_pos (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith [pi_pos]⟩), ?_⟩
  exact lt_trans (cos_sq_bound_of_seven_le 7 le_rfl) (by norm_num)

/-- `1 < C_Nava 6 ^ 2`. -/
lemma one_lt_CNavaSq_six : 1 < CNavaSq 6 := by
  simp only [CNavaSq, angle, Nat.cast_ofNat]
  rw [show (6 : ℝ) + 1 = 7 by norm_num, show (6 : ℝ) - 1 = 5 by norm_num]
  obtain ⟨hcpos, hc_thr⟩ := cos_sq_pi_div_seven_bounds
  have hs : sin (π / 7) ^ 2 = 1 - cos (π / 7) ^ 2 := by
    rw [← sin_sq_add_cos_sq (π / 7)]
    ring
  rw [hs]
  set c := cos (π / 7) ^ 2
  have hsimp : 2 * 5 / (7 * c) * (((7 : ℝ) ^ 2 + 2) / 6 * (1 - c) - 1) =
      5 * (15 - 17 * c) / (7 * c) := by
    field_simp
    ring
  rw [hsimp]
  have hden : 0 < 7 * c := by positivity
  rw [one_lt_div hden]
  nlinarith [hc_thr, hcpos]

end PathObservables
