/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.Basic
public import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentState.LongChainMonotonicity

/-!

# The defect of the cube lies in a band that does not depend on its size

## i. Overview

In the maximal current state of the cube, Robertson's relation reads
`det Σ = R · |det Ω|` with `R = (C(x) C(y) C(z))²` (`det_covarianceMatrix_maxCurrentCubeState`).
The excess `R - 1` is the defect of the cube: it is the part of `det Σ` that the relation does
not account for, and it multiplies `|det Ω|`. From four sites on every axis it is positive, it
is at least the defect of the `4 × 4 × 4` cube, and it stays below the long chain limit
`(π² / 3 - 2)³ - 1`. So the defect of any cube of matter that moves with the maximal current
lies in a band that depends on no size.

## ii. Key results

- `cubeRatio` : `R = (C(x) C(y) C(z))²`.
- `uncertaintyRatio_le_of_le` : `C` is monotone in the number of sites, from four on.
- `defect_eq` : `det Σ - |det Ω| = (R - 1) |det Ω|` in the maximal current state of the cube.
- `one_lt_cubeRatio` : from `4 × 4 × 4` on, `1 < R`.
- `cubeRatio_ge` : `R` is at least that of the `4 × 4 × 4` cube.
- `cubeRatio_lt` : `R < (π² / 3 - 2)³`.

## iii. Table of contents

- A. Monotonicity of `C`
- B. The ratio of the cube
- C. The defect

## iv. References

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open ProbabilisticTheory UnitalPositiveLinearMap Matrix

/-!

## A. Monotonicity of `C`

-/

/-- `C` does not decrease with the number of sites, from four sites on. -/
lemma uncertaintyRatio_le_of_le {T T' : TightBindingChain} (ht : T.t ≠ 0) (ht' : T'.t ≠ 0)
    (hN : 4 ≤ T.N) (hNN' : T.N ≤ T'.N) : T.uncertaintyRatio ≤ T'.uncertaintyRatio := by
  rcases hNN'.lt_or_eq with h | h
  · exact (uncertaintyRatio_lt_uncertaintyRatio ht ht' hN h).le
  · have e := T.uncertaintyRatio_sq_eq_uncertaintyRatioSqForm ht (by omega)
    have e' := T'.uncertaintyRatio_sq_eq_uncertaintyRatioSqForm ht' (by omega)
    rw [← h] at e'
    have n := T.one_le_uncertaintyRatio ht (by omega)
    have n' := T'.one_le_uncertaintyRatio ht' (by omega)
    exact (pow_left_inj₀ (by linarith) (by linarith) two_ne_zero).mp (e.trans e'.symm) |>.le

/-!

## B. The ratio of the cube

-/

/-- The ratio `det Σ / |det Ω|` of the maximal current state of the cube. -/
noncomputable def cubeRatio (Tx Ty Tz : TightBindingChain) : ℝ :=
  (Tx.uncertaintyRatio * Ty.uncertaintyRatio * Tz.uncertaintyRatio) ^ 2

variable {Tx Ty Tz : TightBindingChain}

/-- From `4 × 4 × 4` on, the ratio exceeds one. -/
lemma one_lt_cubeRatio (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) : 1 < cubeRatio Tx Ty Tz :=
  one_lt_pow₀ (one_lt_mul_of_lt_of_le
    (one_lt_mul_of_lt_of_le (Tx.one_lt_uncertaintyRatio hx hNx)
      (Ty.one_le_uncertaintyRatio hy (by omega)))
    (Tz.one_le_uncertaintyRatio hz (by omega))) two_ne_zero

/-- **The ratio is at least that of the `4 × 4 × 4` cube.** -/
lemma cubeRatio_ge {Tx₀ Ty₀ Tz₀ : TightBindingChain} (hx₀ : Tx₀.t ≠ 0) (hy₀ : Ty₀.t ≠ 0)
    (hz₀ : Tz₀.t ≠ 0) (hNx₀ : Tx₀.N = 4) (hNy₀ : Ty₀.N = 4) (hNz₀ : Tz₀.N = 4)
    (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    cubeRatio Tx₀ Ty₀ Tz₀ ≤ cubeRatio Tx Ty Tz := by
  have ax := uncertaintyRatio_le_of_le hx₀ hx (by omega) (by omega)
  have ay := uncertaintyRatio_le_of_le hy₀ hy (by omega) (by omega)
  have az := uncertaintyRatio_le_of_le hz₀ hz (by omega) (by omega)
  have bx := Tx₀.one_le_uncertaintyRatio hx₀ (by omega)
  have by' := Ty₀.one_le_uncertaintyRatio hy₀ (by omega)
  have bz := Tz₀.one_le_uncertaintyRatio hz₀ (by omega)
  have px : 0 ≤ Tx.uncertaintyRatio := by linarith
  have py : 0 ≤ Ty.uncertaintyRatio := by linarith
  have pz : 0 ≤ Tz.uncertaintyRatio := by linarith
  have qx : 0 ≤ Tx₀.uncertaintyRatio := by linarith
  have qy : 0 ≤ Ty₀.uncertaintyRatio := by linarith
  have qz : 0 ≤ Tz₀.uncertaintyRatio := by linarith
  unfold cubeRatio
  gcongr

/-- **The ratio stays below the long chain limit**: `R < (π² / 3 - 2)³`. -/
lemma cubeRatio_lt (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    cubeRatio Tx Ty Tz < (Real.pi ^ 2 / 3 - 2) ^ 3 := by
  have ax := Tx.uncertaintyRatio_lt_sqrt_pi_sq_div_three_sub_two hx hNx
  have ay := Ty.uncertaintyRatio_lt_sqrt_pi_sq_div_three_sub_two hy hNy
  have az := Tz.uncertaintyRatio_lt_sqrt_pi_sq_div_three_sub_two hz hNz
  have hpos : 0 ≤ Real.pi ^ 2 / 3 - 2 := by nlinarith [Real.pi_gt_three]
  have b1 := Tx.one_le_uncertaintyRatio hx (by omega)
  have b2 := Ty.one_le_uncertaintyRatio hy (by omega)
  have b3 := Tz.one_le_uncertaintyRatio hz (by omega)
  unfold cubeRatio
  calc (Tx.uncertaintyRatio * Ty.uncertaintyRatio * Tz.uncertaintyRatio) ^ 2
      < (√(Real.pi ^ 2 / 3 - 2) * √(Real.pi ^ 2 / 3 - 2) * √(Real.pi ^ 2 / 3 - 2)) ^ 2 := by
        gcongr
    _ = (Real.pi ^ 2 / 3 - 2) ^ 3 := by
        rw [show √(Real.pi ^ 2 / 3 - 2) * √(Real.pi ^ 2 / 3 - 2) * √(Real.pi ^ 2 / 3 - 2) =
          √(Real.pi ^ 2 / 3 - 2) ^ 3 by ring, ← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul,
          Real.sq_sqrt hpos]

/-!

## C. The defect

-/

/-- **The defect of the cube**: in the maximal current state,
`det Σ - |det Ω| = (R - 1) |det Ω|`. -/
lemma defect_eq (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) :
    (covarianceMatrix (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.cubePairs Ty Tz)).det -
        |(bracketMatrix (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.cubePairs Ty Tz)).det| =
      (cubeRatio Tx Ty Tz - 1) *
        |(bracketMatrix (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.cubePairs Ty Tz)).det| := by
  have h := Tx.det_covarianceMatrix_maxCurrentCubeState Ty Tz hx hy hz hNx hNy hNz
  have hΩ : |(bracketMatrix (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.cubePairs Ty Tz)).det| =
      (Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 0 *
        Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 1 *
        Tx.axisBracket Ty Tz (Tx.maxCurrentCubeVectorState Ty Tz) 2) ^ 2 := by
    rw [bracketMatrix_cubePairs, det_blockDiagonal, Fin.prod_univ_three]
    simp only [det_fin_two_of, zero_mul, zero_sub, mul_neg, neg_neg]
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
      (mul_self_nonneg _))]
    ring
  rw [h, hΩ, cubeRatio]
  ring

end TightBindingChain
end CondensedMatter
