/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
/-!

# Sums over the roots of the Chebyshev polynomials of the second kind

This file may eventually be upstreamed to Mathlib.

## i. Overview

The Chebyshev polynomial of the second kind `U n` has the `n` real roots `cos (k π / (n + 1))`,
`k = 1, …, n`, so it splits over `ℝ`. Its logarithmic derivative at `x` is `∑ 1 / (x - z)` over
the roots `z`. Evaluated at `x = 1` and `x = -1`, with the values of `U n` and its derivative
there, it gives the sums of `1 / (1 - z)` and `1 / (1 + z)`, and from
`1 / (1 - z ^ 2) = (1 / (1 - z) + 1 / (1 + z)) / 2` the sum
`∑ 1 / (1 - z ^ 2) = ((n + 1)² - 1) / 3`.

## ii. Key results

- `Polynomial.Chebyshev.splits_U_real` : `U n` splits over `ℝ`.
- `Polynomial.Chebyshev.sum_one_div_one_sub_roots_U_real` : `∑ 1 / (1 - z)`.
- `Polynomial.Chebyshev.sum_one_div_one_add_roots_U_real` : `∑ 1 / (1 + z)`.
- `Polynomial.Chebyshev.sum_one_div_one_sub_sq_roots_U_real` : `∑ 1 / (1 - z ^ 2)`.

## iii. Table of contents

- A. `U n` splits over `ℝ`
- B. The derivative of `U n` at `±1`
- C. Sums over the roots

## iv. References

* A. L. Cauchy, *Cours d'analyse de l'École royale polytechnique* (1821).

-/

@[expose] public section

open Polynomial Polynomial.Chebyshev Real

noncomputable section

namespace Polynomial.Chebyshev

/-!

## A. `U n` splits over `ℝ`

-/

/-- The Chebyshev polynomial of the second kind `U n` splits over `ℝ`: all `n` of its roots are
real (they are `cos ((k + 1) * π / (n + 1))` for `k < n`). -/
theorem splits_U_real (n : ℕ) : (U ℝ n).Splits := by
  rw [splits_iff_card_roots]
  cases n with
  | zero => simp [U_zero]
  | succ m =>
    set N := m + 1 with hN
    have hdeg : (U ℝ N).natDegree = N := natDegree_U_natCast (R := ℝ) N
    rw [roots_U_real N]
    have hinj :
        Set.InjOn (fun k : ℕ ↦ cos ((k + 1) * π / (N + 1))) (Finset.range N) :=
      (Finset.range N).nodup_map_iff_injOn.mp (roots_U_real_nodup N)
    have hcard :
        ((Finset.range N).image fun k : ℕ ↦
            cos ((k + 1) * π / (N + 1))).card = N := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    show (Multiset.card _) = _
    rw [hdeg]
    exact hcard

/-!

## B. The derivative of `U n` at `±1`

-/

private theorem derivative_U_natCast_eval_one (n : ℕ) :
    (derivative (U ℝ (n : ℤ))).eval (1 : ℝ) =
      ((n : ℝ) + 2) * ((n : ℝ) + 1) * (n : ℝ) / 3 := by
  have h := derivative_U_eval_one (R := ℝ) (n : ℤ)
  push_cast at h
  linarith

private theorem derivative_U_natCast_eval_neg_one (n : ℕ) :
    (derivative (U ℝ (n : ℤ))).eval (-1 : ℝ) =
      -((-1 : ℝ) ^ n) *
        (((n : ℝ) + 2) * ((n : ℝ) + 1) * (n : ℝ) / 3) := by
  have hfun :
      (fun x : ℝ ↦ (U ℝ (n : ℤ)).eval (-x)) =
        fun x ↦ (-1 : ℝ) ^ n * (U ℝ (n : ℤ)).eval x := by
    funext x
    rw [U_eval_neg (R := ℝ) n x, Int.cast_negOnePow_natCast]
  have hL : HasDerivAt (fun x : ℝ ↦ (U ℝ (n : ℤ)).eval (-x))
      (-(derivative (U ℝ (n : ℤ))).eval (-1)) 1 := by
    have h := (U ℝ (n : ℤ)).hasDerivAt (-1 : ℝ)
    have hc := h.comp 1 (hasDerivAt_id' 1).neg
    rw [mul_neg_one] at hc
    exact hc
  have hR : HasDerivAt
      (fun x : ℝ ↦ (-1 : ℝ) ^ n * (U ℝ (n : ℤ)).eval x)
      ((-1 : ℝ) ^ n * (derivative (U ℝ (n : ℤ))).eval 1) 1 :=
    ((U ℝ (n : ℤ)).hasDerivAt (1 : ℝ)).const_mul _
  have heq : HasDerivAt (fun x : ℝ ↦ (U ℝ (n : ℤ)).eval (-x))
      ((-1 : ℝ) ^ n * (derivative (U ℝ (n : ℤ))).eval 1) 1 :=
    hfun ▸ hR
  have hder := HasDerivAt.unique hL heq
  have hUd1 := derivative_U_natCast_eval_one n
  rw [hUd1] at hder
  linarith

/-!

## C. Sums over the roots

-/

/-- `∑ 1 / (1 - z)` over the real roots `z` of `U n` equals `((n + 1) ^ 2 - 1) / 3`. -/
theorem sum_one_div_one_sub_roots_U_real (n : ℕ) (hn : 1 ≤ n) :
    ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 - z)).sum =
      (((n : ℝ) + 1) ^ 2 - 1) / 3 := by
  have hsplit : (U ℝ (n : ℤ)).Splits := splits_U_real n
  have hne : (U ℝ (n : ℤ)).eval (1 : ℝ) ≠ 0 := by
    rw [U_eval_one]; positivity
  have hlog := hsplit.eval_derivative_div_eval_of_ne_zero hne
  have hU1 : (U ℝ (n : ℤ)).eval (1 : ℝ) = (n : ℝ) + 1 := by
    simp [U_eval_one]
  have hUd := derivative_U_natCast_eval_one n
  have hratio :
      (derivative (U ℝ (n : ℤ))).eval (1 : ℝ) / (U ℝ (n : ℤ)).eval (1 : ℝ) =
        (((n : ℝ) + 1) ^ 2 - 1) / 3 := by
    rw [hUd, hU1]
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [this]; ring
  rw [← hratio, hlog]

/-- `∑ 1 / (1 + z)` over the real roots `z` of `U n` equals `((n + 1) ^ 2 - 1) / 3`. -/
theorem sum_one_div_one_add_roots_U_real (n : ℕ) (hn : 1 ≤ n) :
    ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 + z)).sum =
      (((n : ℝ) + 1) ^ 2 - 1) / 3 := by
  have hsplit : (U ℝ (n : ℤ)).Splits := splits_U_real n
  have hU : (U ℝ (n : ℤ)).eval (-1 : ℝ) = (-1 : ℝ) ^ n * ((n : ℝ) + 1) := by
    rw [U_eval_neg_one (R := ℝ) (n : ℤ), Int.cast_negOnePow_natCast]
    push_cast; ring
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hpow : (-1 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hne : (U ℝ (n : ℤ)).eval (-1 : ℝ) ≠ 0 := by
    rw [hU]; exact mul_ne_zero hpow hn1
  have hlog := hsplit.eval_derivative_div_eval_of_ne_zero hne
  have hUd := derivative_U_natCast_eval_neg_one n
  have hratio :
      (derivative (U ℝ (n : ℤ))).eval (-1 : ℝ) / (U ℝ (n : ℤ)).eval (-1 : ℝ) =
        -((((n : ℝ) + 1) ^ 2 - 1) / 3) := by
    rw [hUd, hU]
    field_simp [hpow, hn1]; ring
  have hmap :
      ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (-1 - z)).sum =
        -((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 + z)).sum := by
    have hpt :
        ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (-1 - z)) =
          (U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ -((1 : ℝ) / (1 + z)) := by
      refine Multiset.map_congr rfl fun z _ => ?_
      have : (-1 - z : ℝ) = -(1 + z) := by ring
      rw [this, div_neg]
    rw [hpt, Multiset.sum_map_neg]
  have : -((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 + z)).sum =
      -((((n : ℝ) + 1) ^ 2 - 1) / 3) := by
    rwa [← hmap, ← hlog]
  linarith

private theorem abs_root_U_real_lt_one {n : ℕ} {z : ℝ}
    (hz : z ∈ (U ℝ (n : ℤ)).roots) (hn : 1 ≤ n) : |z| < 1 := by
  have hroots := roots_U_real n
  rw [hroots, Finset.mem_val, Finset.mem_image] at hz
  obtain ⟨k, hk, rfl⟩ := hz
  have hklt : k < n := Finset.mem_range.mp hk
  have hθpos : 0 < (k + 1 : ℝ) * π / (n + 1) := by positivity
  have hθlt : (k + 1 : ℝ) * π / (n + 1) < π := by
    have : (k + 1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hklt
    calc
      (k + 1 : ℝ) * π / (n + 1) ≤ n * π / (n + 1) := by gcongr
      _ < π := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [pi_pos]
  have hsin : 0 < sin ((k + 1 : ℝ) * π / (n + 1)) :=
    sin_pos_of_pos_of_lt_pi hθpos hθlt
  have hpyth := sin_sq_add_cos_sq ((k + 1 : ℝ) * π / (n + 1))
  have hsq : cos ((k + 1 : ℝ) * π / (n + 1)) ^ 2 < 1 := by
    nlinarith [mul_pos hsin hsin]
  exact (sq_lt_one_iff_abs_lt_one _).mp hsq

/-- `∑ 1 / (1 - z ^ 2)` over the real roots `z` of `U n` equals `((n + 1) ^ 2 - 1) / 3`. -/
theorem sum_one_div_one_sub_sq_roots_U_real (n : ℕ) (hn : 1 ≤ n) :
    ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 - z ^ 2)).sum =
      (((n : ℝ) + 1) ^ 2 - 1) / 3 := by
  have h1 := sum_one_div_one_sub_roots_U_real n hn
  have h2 := sum_one_div_one_add_roots_U_real n hn
  have hpoint (z : ℝ) (hz : z ∈ (U ℝ (n : ℤ)).roots) :
      (1 : ℝ) / (1 - z ^ 2) =
        (1 / 2 : ℝ) * ((1 : ℝ) / (1 - z) + (1 : ℝ) / (1 + z)) := by
    have habs := abs_root_U_real_lt_one hz hn
    have hz1 : z ≠ 1 := by
      intro h; rw [h, abs_one] at habs; linarith
    have hzm1 : z ≠ -1 := by
      intro h; rw [h, abs_neg, abs_one] at habs; linarith
    have hden : (1 - z ^ 2 : ℝ) ≠ 0 := by
      intro h
      have : z ^ 2 = 1 := by linarith
      have : |z| = 1 := (sq_eq_one_iff.mp this).elim (by intro; simp [*]) (by intro; simp [*])
      linarith [habs]
    have hz1' : (1 - z : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
    have hzm : (1 + z : ℝ) ≠ 0 := by
      intro h; exact hzm1 (by linarith)
    field_simp [hz1', hzm, hden]
    ring
  have hdecomp :
      ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 - z ^ 2)).sum =
        (1 / 2 : ℝ) *
          (((U ℝ (n : ℤ)).roots.map fun z ↦ (1 : ℝ) / (1 - z)).sum +
            ((U ℝ (n : ℤ)).roots.map fun z ↦ (1 : ℝ) / (1 + z)).sum) := by
    classical
    calc
      ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 - z ^ 2)).sum
          = ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦
              (1 / 2 : ℝ) * ((1 : ℝ) / (1 - z) + (1 : ℝ) / (1 + z))).sum := by
            refine congr_arg Multiset.sum (Multiset.map_congr rfl fun z hz => hpoint z hz)
      _ = (1 / 2 : ℝ) *
            ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦
              ((1 : ℝ) / (1 - z) + (1 : ℝ) / (1 + z))).sum := by
            simp [Multiset.sum_map_mul_left]
      _ = (1 / 2 : ℝ) *
            (((U ℝ (n : ℤ)).roots.map fun z ↦ (1 : ℝ) / (1 - z)).sum +
              ((U ℝ (n : ℤ)).roots.map fun z ↦ (1 : ℝ) / (1 + z)).sum) := by
            simp [Multiset.sum_map_add]
  rw [hdecomp, h1, h2]
  ring

end Polynomial.Chebyshev
