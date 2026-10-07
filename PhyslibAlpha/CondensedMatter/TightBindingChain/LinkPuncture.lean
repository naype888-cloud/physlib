/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.HorizonCount
public import PhyslibAlpha.QuantumGravity.LoopQuantumGravity.AreaSpectrum
/-!

# A bond across the cut is a puncture

## i. Overview

`HorizonCount` gives `k` quanta on the `M` bonds across a cut of the open tight binding chain
the entropy `k log M`. A loop quantum gravity puncture of spin `j` has `2 j + 1` states, so when
`M = 2 j + 1` the cut has exactly the entropy of `k` punctures of spin `j`. On four sites the
cut after the first site has `M = 2` bonds: each one is a puncture of spin `1/2`.

At the Immirzi parameter `γ = log 2 / (π √3)` fixed by Bekenstein–Hawking, the cosmological
constant counted on that cut is `12 π / A`, with `A = k A(1/2)` the area of `k` lowest loop
quantum gravity quanta: the de Sitter horizon is made of `k` quanta of area.

## ii. Key results

- `cutEntropy_eq_punctureEntropy` : with `M = 2 j + 1`, the cut has the entropy of `k`
  punctures of spin `j`.
- `card_cutBonds_zero_of_four` : on four sites the first cut has two bonds.
- `cutEntropy_spin_half` : there each bond is a puncture of spin `1/2`.
- `countCosmologicalConstant_eq_div_surfaceArea` : at the Bekenstein–Hawking value of `γ`,
  `Λ = 12 π / A` for the area `A` of `k` lowest quanta.

## iii. Table of contents

- A. Bonds and punctures
- B. The horizon made of quanta of area

## iv. References

* A. Ashtekar, J. Baez, A. Corichi and K. Krasnov, *Quantum geometry and black hole entropy*,
  Phys. Rev. Lett. 80 (1998) 904–907.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain

open Real LoopQuantumGravity Cosmology.FLRW.FriedmannEquation

variable (T : TightBindingChain)

/-!

## A. Bonds and punctures

-/

/-- **A bond is a puncture.** With `M = 2 j + 1` bonds across the cut, `k` quanta on the cut have
the entropy of `k` punctures of spin `j`. -/
theorem cutEntropy_eq_punctureEntropy {c k : ℕ} {j : ℝ}
    (hM : ((T.cutBonds c).card : ℝ) = 2 * j + 1) : T.cutEntropy c k = punctureEntropy k j := by
  rw [cutEntropy, punctureEntropy, hM]

/-- On four sites the cut after the first site has two bonds. -/
lemma card_cutBonds_zero_of_four (hN : T.N = 4) : (T.cutBonds 0).card = 2 := by
  rw [T.card_cutBonds (by omega), hN]

/-- On four sites each bond across the first cut is a puncture of spin `1/2`. -/
theorem cutEntropy_spin_half (hN : T.N = 4) (k : ℕ) :
    T.cutEntropy 0 k = punctureEntropy k (1 / 2) :=
  T.cutEntropy_eq_punctureEntropy (by rw [T.card_cutBonds_zero_of_four hN]; norm_num)

/-!

## B. The horizon made of quanta of area

-/

/-- **The de Sitter horizon is made of quanta of area.** On four sites, at the Immirzi parameter
`γ = log 2 / (π √3)`, the cosmological constant counted with `k ≥ 1` quanta on the first cut is
`12 π / A`, with `A = k A(1/2)` the area of `k` lowest loop quantum gravity quanta. -/
theorem countCosmologicalConstant_eq_div_surfaceArea (hN : T.N = 4) {k : ℕ} (hk : 1 ≤ k)
    {lp : ℝ} (hlp : lp ≠ 0) :
    T.countCosmologicalConstant 0 k lp =
      12 * π / surfaceArea lp (Real.log 2 / (π * √3)) (List.replicate k (1 / 2)) := by
  have hBH := (bekensteinHawking_iff_immirzi hlp (n := k) (by omega)).mpr rfl
  rw [countCosmologicalConstant, T.cutEntropy_spin_half hN, hBH, entropyCosmologicalConstant]
  have hA : 0 < surfaceArea lp (Real.log 2 / (π * √3)) (List.replicate k (1 / 2)) := by
    rw [surfaceArea_replicate, areaSpectrum_half]
    have : (0 : ℝ) < k := by exact_mod_cast hk
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have := pi_pos
    positivity
  field_simp
  ring

end TightBindingChain
end CondensedMatter
