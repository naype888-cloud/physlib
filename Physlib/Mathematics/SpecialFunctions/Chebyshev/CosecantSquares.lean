/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Physlib.Mathematics.SpecialFunctions.Chebyshev.RootSums
/-!

# The cosecant- and cotangent-squared sums

This file may eventually be upstreamed to Mathlib.

## i. Overview

The roots of the Chebyshev polynomial `U (N - 1)` are `cos (k π / N)`, and `1 - cos² = sin²`, so
the sum of `1 / (1 - z ^ 2)` over them is the classical cosecant-squared sum
`∑_{k=1}^{N-1} csc² (k π / N) = (N² - 1) / 3`. Termwise `cot² = csc² - 1` gives the full
cotangent sum `(N - 1)(N - 2) / 3`, and for odd `N = 2m + 1` the involution `k ↦ N - k` halves it
to `∑_{k=1}^{m} cot² (k π / (2m + 1)) = m (2m - 1) / 3`, the arithmetic core of the elementary
evaluation of `∑ 1 / k² = π² / 6`.

## ii. Key results

- `Real.sum_inv_sin_sq_pi_mul_div` : the cosecant-squared sum.
- `Real.sum_cot_sq_pi_mul_div` : the cotangent-squared sum.
- `Real.sum_cot_sq_pi_mul_div_two_mul_add_one` : its half for odd denominators.

## iii. Table of contents

- A. The cosecant-squared sum
- B. The cotangent-squared sums

## iv. References

* A. L. Cauchy, *Cours d'analyse de l'École royale polytechnique* (1821).
* M. Aigner, G. M. Ziegler, *Proofs from THE BOOK*, Springer, chapter on `π² / 6`.

-/

@[expose] public section

open Polynomial Polynomial.Chebyshev Real

noncomputable section

/-!

## A. The cosecant-squared sum

-/

/-- **The cosecant-squared identity.**
`∑_{k=1}^{N-1} csc²(kπ/N) = (N² - 1) / 3`, stated over `Real.sin`. -/
theorem Real.sum_inv_sin_sq_pi_mul_div (N : ℕ) (hN : 2 ≤ N) :
    ∑ k ∈ Finset.Ico 1 N, (Real.sin ((k : ℝ) * π / N))⁻¹ ^ 2 =
      ((N : ℝ) ^ 2 - 1) / 3 := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hsum := Polynomial.Chebyshev.sum_one_div_one_sub_sq_roots_U_real n hn
  classical
  have hinj :
      Set.InjOn (fun k : ℕ ↦ Real.cos ((k + 1) * π / (n + 1))) (Finset.range n) :=
    (Finset.range n).nodup_map_iff_injOn.mp (Polynomial.Chebyshev.roots_U_real_nodup n)
  have hfin :
      ((U ℝ (n : ℤ)).roots.map fun z : ℝ ↦ (1 : ℝ) / (1 - z ^ 2)).sum =
        ∑ k ∈ Finset.range n,
          (1 : ℝ) / (1 - Real.cos ((k + 1 : ℝ) * π / (n + 1)) ^ 2) := by
    rw [Polynomial.Chebyshev.roots_U_real n, Finset.image_val_of_injOn hinj, Multiset.map_map]
    rfl
  have hsin :
      ∑ k ∈ Finset.range n,
          (1 : ℝ) / (1 - Real.cos ((k + 1 : ℝ) * π / (n + 1)) ^ 2) =
        ∑ k ∈ Finset.range n, (Real.sin ((k + 1 : ℝ) * π / (n + 1)))⁻¹ ^ 2 := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have h1 : (1 : ℝ) - Real.cos ((k + 1 : ℝ) * π / (n + 1)) ^ 2 =
        Real.sin ((k + 1 : ℝ) * π / (n + 1)) ^ 2 := by
      linarith [sin_sq_add_cos_sq ((k + 1 : ℝ) * π / (n + 1))]
    rw [h1, one_div, inv_pow]
  have himg :
      Finset.Ico 1 (n + 1) = (Finset.range n).image (fun k ↦ k + 1) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨k - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [himg, Finset.sum_image (fun x _ y _ h => by simpa using h)]
  push_cast
  rw [← hsin, ← hfin]
  exact hsum

/-!

## B. The cotangent-squared sums

-/

/-- **The full cotangent-squared identity.**
`∑_{k=1}^{N-1} cot²(kπ/N) = (N-1)(N-2)/3`.

This is the cosecant-squared identity with `1` subtracted from each of its `N - 1` terms,
using `cot² x = csc² x - 1`. -/
theorem Real.sum_cot_sq_pi_mul_div (N : ℕ) (hN : 2 ≤ N) :
    ∑ k ∈ Finset.Ico 1 N, Real.cot ((k : ℝ) * π / N) ^ 2 =
      ((N : ℝ) - 1) * ((N : ℝ) - 2) / 3 := by
  have hpoint (k : ℕ) (hk : k ∈ Finset.Ico 1 N) :
      Real.cot ((k : ℝ) * π / N) ^ 2 =
        (Real.sin ((k : ℝ) * π / N))⁻¹ ^ 2 - 1 := by
    have hk' := Finset.mem_Ico.mp hk
    have hkpos : 0 < k := by omega
    have hklt : k < N := by omega
    have hNpos : (0 : ℝ) < N := by positivity
    have hθpos : 0 < (k : ℝ) * π / N := by positivity
    have hθlt : (k : ℝ) * π / N < π := by
      rw [div_lt_iff₀ hNpos]
      have hklt' : (k : ℝ) < N := by exact_mod_cast hklt
      nlinarith [pi_pos]
    have hsin : Real.sin ((k : ℝ) * π / N) ≠ 0 :=
      ne_of_gt (sin_pos_of_pos_of_lt_pi hθpos hθlt)
    rw [Real.cot_eq_cos_div_sin]
    field_simp [hsin]
    nlinarith [Real.sin_sq_add_cos_sq ((k : ℝ) * π / N)]
  calc
    ∑ k ∈ Finset.Ico 1 N, Real.cot ((k : ℝ) * π / N) ^ 2 =
        ∑ k ∈ Finset.Ico 1 N,
          ((Real.sin ((k : ℝ) * π / N))⁻¹ ^ 2 - 1) := by
      exact Finset.sum_congr rfl hpoint
    _ = (∑ k ∈ Finset.Ico 1 N,
          (Real.sin ((k : ℝ) * π / N))⁻¹ ^ 2) -
        ∑ _k ∈ Finset.Ico 1 N, (1 : ℝ) := by
      rw [Finset.sum_sub_distrib]
    _ = ((N : ℝ) - 1) * ((N : ℝ) - 2) / 3 := by
      rw [Real.sum_inv_sin_sq_pi_mul_div N hN]
      simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
      rw [Nat.cast_sub (by omega : 1 ≤ N)]
      push_cast
      ring

/-- **The cotangent-squared identity for an odd denominator.**
`∑_{k=1}^{m} cot²(kπ/(2m+1)) = m(2m-1)/3`.

Split the full sum at `m + 1`. The change of variables `k ↦ 2m + 1 - k` sends its upper
half to its lower half, and `cot² (π - x) = cot² x` makes the two sums equal. -/
theorem Real.sum_cot_sq_pi_mul_div_two_mul_add_one (m : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Ico 1 (m + 1),
        Real.cot ((k : ℝ) * π / (2 * m + 1)) ^ 2 =
      (m : ℝ) * (2 * (m : ℝ) - 1) / 3 := by
  let N := 2 * m + 1
  let f : ℕ → ℝ := fun k => Real.cot ((k : ℝ) * π / N) ^ 2
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hfull := Real.sum_cot_sq_pi_mul_div N hN
  have hsplit :
      (∑ k ∈ Finset.Ico 1 (m + 1), f k) +
          ∑ k ∈ Finset.Ico (m + 1) N, f k =
        ∑ k ∈ Finset.Ico 1 N, f k :=
    Finset.sum_Ico_consecutive f (by omega) (by dsimp [N]; omega)
  have hsymm (k : ℕ) (hk : k ∈ Finset.Ico (m + 1) N) : f (N - k) = f k := by
    have hk' := Finset.mem_Ico.mp hk
    have hkN : k ≤ N := by omega
    have hangle :
        ((N - k : ℕ) : ℝ) * π / N = π - (k : ℝ) * π / N := by
      rw [Nat.cast_sub hkN]
      have hN0 : (N : ℝ) ≠ 0 := by positivity
      field_simp [hN0]
    dsimp [f]
    rw [hangle]
    simp [Real.cot_eq_cos_div_sin, Real.sin_pi_sub, Real.cos_pi_sub]
    ring
  have himage :
      (Finset.Ico (m + 1) N).image (fun k => N - k) = Finset.Ico 1 (m + 1) := by
    dsimp [N]
    rw [Nat.Ico_image_const_sub_eq_Ico (by omega)]
    congr <;> omega
  have hinj : Set.InjOn (fun k => N - k) (Finset.Ico (m + 1) N) := by
    intro a ha b hb hab
    have ha' := Finset.mem_Ico.mp ha
    have hb' := Finset.mem_Ico.mp hb
    dsimp [N] at ha' hb' hab ⊢
    omega
  have hupper :
      (∑ k ∈ Finset.Ico (m + 1) N, f k) =
        ∑ k ∈ Finset.Ico 1 (m + 1), f k := by
    rw [← himage, Finset.sum_image hinj]
    exact Finset.sum_congr rfl fun k hk => (hsymm k hk).symm
  rw [hupper] at hsplit
  rw [← hsplit] at hfull
  dsimp [f, N] at hfull ⊢
  push_cast at hfull
  nlinarith
