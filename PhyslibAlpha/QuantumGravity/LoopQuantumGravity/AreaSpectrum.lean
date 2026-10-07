/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-!

# The area spectrum and the puncture entropy of loop quantum gravity

## i. Overview

In loop quantum gravity a surface pierced by a link of spin `j` carries the area
`A(j) = 8 π γ ℓ_P² √(j (j + 1))`, with `ℓ_P` the Planck length and `γ` the Immirzi parameter.
The levels are separated and have a lowest value `A(1/2) = 4 π √3 γ ℓ_P²`: a surface with `n`
punctures has area at least `n A(1/2)`, with no fraction of the lowest quantum.

Each puncture of spin `j` has `2 j + 1` states, so `n` of them have the entropy
`n log (2 j + 1)`. With all punctures at spin `1/2` the entropy is proportional to the area,
and it equals the Bekenstein–Hawking value `A / (4 ℓ_P²)` exactly when
`γ = log 2 / (π √3)`.

## ii. Key results

- `areaSpectrum` : the area `A(j) = 8 π γ ℓ_P² √(j (j + 1))` of one puncture.
- `areaSpectrum_strictMono`, `areaSpectrum_half`, `areaSpectrum_min` : separated levels with the
  lowest value `A(1/2) = 4 π √3 γ ℓ_P²`.
- `surfaceArea_ge` : `n` punctures have area at least `n A(1/2)`.
- `punctureEntropy` : the entropy `n log (2 j + 1)` of `n` punctures of spin `j`.
- `entropy_proportional_to_area` : at spin `1/2` the entropy is proportional to the area.
- `bekensteinHawking_iff_immirzi` : `S = A / (4 ℓ_P²)` iff `γ = log 2 / (π √3)`.

## iii. Table of contents

- A. The area spectrum
- B. The puncture entropy

## iv. References

* C. Rovelli and L. Smolin, *Discreteness of area and volume in quantum gravity*,
  Nucl. Phys. B 442 (1995) 593–619.
* A. Ashtekar, J. Baez, A. Corichi and K. Krasnov, *Quantum geometry and black hole entropy*,
  Phys. Rev. Lett. 80 (1998) 904–907.

-/

@[expose] public section

namespace LoopQuantumGravity

open Real

/-!

## A. The area spectrum

-/

/-- The area `A(j) = 8 π γ ℓ_P² √(j (j + 1))` of a puncture of spin `j`, for the Planck length
`lp` and the Immirzi parameter `γ`. -/
noncomputable def areaSpectrum (lp γ j : ℝ) : ℝ := 8 * π * γ * lp ^ 2 * √(j * (j + 1))

/-- The area of a surface pierced by punctures of spins `js`. -/
noncomputable def surfaceArea (lp γ : ℝ) (js : List ℝ) : ℝ := (js.map (areaSpectrum lp γ)).sum

/-- `j (j + 1) ≥ 3 / 4` for every spin `j ≥ 1/2`. -/
lemma three_quarters_le_mul {j : ℝ} (h : 1 / 2 ≤ j) : 3 / 4 ≤ j * (j + 1) := by
  nlinarith [sq_nonneg (j - 1 / 2)]

lemma eight_pi_mul_nonneg {lp γ : ℝ} (hγ : 0 ≤ γ * lp ^ 2) : 0 ≤ 8 * π * γ * lp ^ 2 := by
  have := pi_pos
  calc (0 : ℝ) ≤ 8 * π * (γ * lp ^ 2) := by positivity
    _ = _ := by ring

/-- **Separated levels.** For `γ ℓ_P² > 0` and `0 ≤ j < k`, `A(j) < A(k)`. -/
theorem areaSpectrum_strictMono {lp γ : ℝ} (hγ : 0 < γ * lp ^ 2) {j k : ℝ} (hj : 0 ≤ j)
    (hjk : j < k) : areaSpectrum lp γ j < areaSpectrum lp γ k := by
  have h8 : 0 < 8 * π * γ * lp ^ 2 := by
    have := pi_pos
    calc (0 : ℝ) < 8 * π * (γ * lp ^ 2) := by positivity
      _ = _ := by ring
  exact mul_lt_mul_of_pos_left (Real.sqrt_lt_sqrt (by positivity) (by nlinarith)) h8

/-- The lowest level: `A(1/2) = 4 π √3 γ ℓ_P²`. -/
theorem areaSpectrum_half (lp γ : ℝ) : areaSpectrum lp γ (1 / 2) = 4 * π * √3 * γ * lp ^ 2 := by
  have h : √((1 / 2 : ℝ) * (1 / 2 + 1)) = √3 / 2 := by
    rw [show (1 / 2 : ℝ) * (1 / 2 + 1) = 3 / 2 ^ 2 by norm_num, Real.sqrt_div' _ (by norm_num),
      Real.sqrt_sq (by norm_num)]
  rw [areaSpectrum, h]
  ring

/-- **The lowest quantum.** For `γ ℓ_P² ≥ 0` and `j ≥ 1/2`, `A(1/2) ≤ A(j)`. -/
theorem areaSpectrum_min {lp γ : ℝ} (hγ : 0 ≤ γ * lp ^ 2) {j : ℝ} (hj : 1 / 2 ≤ j) :
    areaSpectrum lp γ (1 / 2) ≤ areaSpectrum lp γ j :=
  mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by nlinarith [three_quarters_le_mul hj]))
    (eight_pi_mul_nonneg hγ)

/-- **No fraction of a quantum.** A surface with `n` punctures, all of spin at least `1/2`, has
area at least `n A(1/2)`. -/
theorem surfaceArea_ge {lp γ : ℝ} (hγ : 0 ≤ γ * lp ^ 2) (js : List ℝ)
    (hjs : ∀ j ∈ js, 1 / 2 ≤ j) :
    js.length * areaSpectrum lp γ (1 / 2) ≤ surfaceArea lp γ js := by
  induction js with
  | nil => simp [surfaceArea]
  | cons j js ih =>
    have h1 := areaSpectrum_min hγ (hjs j (by simp))
    have h2 := ih (fun k hk => hjs k (by simp [hk]))
    simp only [surfaceArea, List.map_cons, List.sum_cons, List.length_cons] at h2 ⊢
    push_cast
    linarith

/-- With all punctures at the lowest spin the area is exactly `n A(1/2)`. -/
lemma surfaceArea_replicate (lp γ : ℝ) (n : ℕ) :
    surfaceArea lp γ (List.replicate n (1 / 2)) = n * areaSpectrum lp γ (1 / 2) := by
  simp [surfaceArea, List.map_replicate, List.sum_replicate]

/-!

## B. The puncture entropy

-/

/-- The entropy `n log (2 j + 1)` of `n` punctures of spin `j`. -/
noncomputable def punctureEntropy (n : ℕ) (j : ℝ) : ℝ := n * Real.log (2 * j + 1)

/-- The entropy is the logarithm of the number `(2 j + 1)ⁿ` of puncture states. -/
lemma punctureEntropy_eq_log (n : ℕ) (j : ℝ) :
    punctureEntropy n j = Real.log ((2 * j + 1) ^ n) := by
  rw [punctureEntropy, Real.log_pow]

/-- The entropy is additive: `S(n + m) = S(n) + S(m)`. -/
lemma punctureEntropy_add (n m : ℕ) (j : ℝ) :
    punctureEntropy (n + m) j = punctureEntropy n j + punctureEntropy m j := by
  simp only [punctureEntropy]
  push_cast
  ring

/-- **Entropy proportional to area.** With `n` punctures of spin `1/2`, the entropy is
`log 2 / A(1/2)` times the area of the surface. -/
theorem entropy_proportional_to_area {lp γ : ℝ} (h : areaSpectrum lp γ (1 / 2) ≠ 0) (n : ℕ) :
    punctureEntropy n (1 / 2) =
      Real.log 2 / areaSpectrum lp γ (1 / 2) * surfaceArea lp γ (List.replicate n (1 / 2)) := by
  rw [surfaceArea_replicate, punctureEntropy]
  field_simp
  norm_num

/-- **Bekenstein–Hawking fixes the Immirzi parameter.** For `n ≥ 1` punctures of spin `1/2` and
`ℓ_P ≠ 0`, `S = A / (4 ℓ_P²)` holds exactly when `γ = log 2 / (π √3)`. -/
theorem bekensteinHawking_iff_immirzi {lp γ : ℝ} (hlp : lp ≠ 0) {n : ℕ} (hn : 0 < n) :
    punctureEntropy n (1 / 2) = surfaceArea lp γ (List.replicate n (1 / 2)) / (4 * lp ^ 2) ↔
      γ = Real.log 2 / (π * √3) := by
  have hπ : π * √3 ≠ 0 := by positivity
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [surfaceArea_replicate, areaSpectrum_half, punctureEntropy, eq_div_iff hπ]
  constructor
  · intro h
    field_simp at h
    norm_num at h
    linear_combination -h
  · intro h
    field_simp
    norm_num
    rw [← h]
    ring

end LoopQuantumGravity
