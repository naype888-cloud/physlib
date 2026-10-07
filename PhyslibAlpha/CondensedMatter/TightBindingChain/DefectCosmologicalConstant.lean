/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.CosmologicalConstantChain
public import PhyslibAlpha.CondensedMatter.TightBindingChain.VolumetricQuantum
/-!

# The counted cosmological constant and the uncertainty defect of the cube

## i. Overview

`HorizonCount` counts `W = M^k` states of `k` quanta on the `M` bonds across a cut and gives
`Λ = 3 π / (ℓ² log W)`. Here each quantum carries the dimensional quantum `δ = C_Nava - 1` of a
chain, the excess of its energy–position uncertainty over saturation (`VolumetricQuantum`), so
`k` quanta carry the defect `Ω = k δ`.

For `2` or `3` sites `δ = 0`: every configuration carries no defect, and the defect does not see
the count. From `4` sites on `0 < Ω < k (√(π² / 3 - 2) - 1)`, the entropy is proportional to the
defect, `S = (log M / δ) Ω`, and the counted constant is `Λ = 3 π δ / (ℓ² log M Ω)`.

On the cube, the quanta of the `x` axis carry the excess of the uncertainty relation of that axis
in the maximal current state: their defect vanishes exactly when that relation is an equality.
From `4 × 4 × 4` on, the relation is strict on the three axes and the counted constant on a cut of
the `x` axis is `Λ = 3 π δ_x / (ℓ² log M Ω_x)`.

## ii. Key results

- `quantumDefect` : the defect `Ω = k δ` of `k` quanta of a chain.
- `quantumDefect_eq_zero` : for `2` or `3` sites every configuration has `Ω = 0`.
- `quantumDefect_pos`, `quantumDefect_lt` : from `4` sites on,
  `0 < Ω < k (√(π² / 3 - 2) - 1)`.
- `cutEntropy_eq_mul_quantumDefect` : `S = (log M / δ) Ω`.
- `countCosmologicalConstant_eq_quantumDefect` : `Λ = 3 π δ / (ℓ² log M Ω)`.
- `quantumDefect_alongX_eq_zero_iff` : on the cube, `Ω_x = 0` iff `k = 0` or the uncertainty
  relation of the `x` axis is an equality.
- `countCosmologicalConstant_cube` : from `4 × 4 × 4` on, strict on the three axes,
  `Ω_x > 0` and `Λ = 3 π δ_x / (ℓ² log M Ω_x)`.

## iii. Table of contents

- A. The defect of the quanta
- B. The constant and the defect
- C. On the cube

## iv. References

* G. W. Gibbons and S. W. Hawking, *Cosmological event horizons, thermodynamics, and particle
  creation*, Phys. Rev. D 15 (1977) 2738.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain

open Real ProbabilisticTheory UnitalPositiveLinearMap Cosmology.FLRW.FriedmannEquation

variable (T D : TightBindingChain)

/-!

## A. The defect of the quanta

-/

/-- The defect `Ω = k δ` of `k` quanta, each carrying the dimensional quantum `δ` of `D`. -/
noncomputable def quantumDefect (k : ℕ) : ℝ := k * D.dimQuantum

/-- For `2` or `3` sites every configuration of the quanta carries no defect. -/
theorem quantumDefect_eq_zero (ht : D.t ≠ 0) (hD : D.N = 2 ∨ D.N = 3) (k : ℕ) :
    D.quantumDefect k = 0 := by
  rw [quantumDefect, (D.dimQuantum_eq_zero_iff ht (by omega)).mpr hD, mul_zero]

/-- From `4` sites on, `k ≥ 1` quanta carry a positive defect. -/
theorem quantumDefect_pos (ht : D.t ≠ 0) (hD : 4 ≤ D.N) {k : ℕ} (hk : 1 ≤ k) :
    0 < D.quantumDefect k :=
  mul_pos (by exact_mod_cast hk) (D.dimQuantum_pos ht hD)

/-- From `4` sites on, the defect stays below `k (√(π² / 3 - 2) - 1)`. -/
theorem quantumDefect_lt (ht : D.t ≠ 0) (hD : 4 ≤ D.N) {k : ℕ} (hk : 1 ≤ k) :
    D.quantumDefect k < k * (√(π ^ 2 / 3 - 2) - 1) :=
  mul_lt_mul_of_pos_left (D.dimQuantum_lt ht hD) (by exact_mod_cast hk)

/-- **The entropy is proportional to the defect**: from `4` sites on, `S = (log M / δ) Ω`. -/
theorem cutEntropy_eq_mul_quantumDefect (ht : D.t ≠ 0) (hD : 4 ≤ D.N) (c k : ℕ) :
    T.cutEntropy c k = Real.log (T.cutBonds c).card / D.dimQuantum * D.quantumDefect k := by
  rw [cutEntropy, quantumDefect]
  field_simp [(D.dimQuantum_pos ht hD).ne']

/-!

## B. The constant and the defect

-/

/-- **The counted constant from the defect**: from `4` sites on,
`Λ = 3 π δ / (ℓ² log M Ω)`. -/
theorem countCosmologicalConstant_eq_quantumDefect (ht : D.t ≠ 0) (hD : 4 ≤ D.N) (c k : ℕ)
    (ℓ : ℝ) :
    T.countCosmologicalConstant c k ℓ =
      3 * π * D.dimQuantum /
        (ℓ ^ 2 * Real.log (T.cutBonds c).card * D.quantumDefect k) := by
  rw [countCosmologicalConstant, entropyCosmologicalConstant,
    T.cutEntropy_eq_mul_quantumDefect D ht hD]
  rw [div_mul_eq_mul_div, mul_div_assoc', div_div_eq_mul_div]
  ring

/-!

## C. On the cube

-/

variable (Tx Ty Tz : TightBindingChain)

/-- On the cube, the quanta of the `x` axis carry no defect iff there are none or the uncertainty
relation of the `x` axis is an equality in the maximal current state. -/
theorem quantumDefect_alongX_eq_zero_iff (ht : Tx.t ≠ 0) (hN : 2 ≤ Tx.N) (k : ℕ) :
    Tx.quantumDefect k = 0 ↔ k = 0 ∨
      centeredGramDefect (Tx.maxCurrentCubeVectorState Ty Tz)
        (Tx.alongX Ty Tz Tx.openHamiltonianObservable)
        (Tx.alongX Ty Tz Tx.positionObservable) = 0 := by
  rw [quantumDefect, mul_eq_zero, Nat.cast_eq_zero, Tx.dimQuantum_eq_zero_iff ht hN,
    Tx.centeredGramDefect_alongX_eq_zero_iff Ty Tz ht hN]

/-- **The counted constant on the cube.** From `4 × 4 × 4` on, the uncertainty relation of the
maximal current state is strict on the three axes, `k ≥ 1` quanta of the `x` axis carry a
positive defect `Ω_x`, and the constant counted on a cut of the `x` axis is
`Λ = 3 π δ_x / (ℓ² log M Ω_x)`. -/
theorem countCosmologicalConstant_cube (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) {k : ℕ} (hk : 1 ≤ k) (c : ℕ) (ℓ : ℝ) :
    (0 < centeredGramDefect (Tx.maxCurrentCubeVectorState Ty Tz)
        (Tx.alongX Ty Tz Tx.openHamiltonianObservable) (Tx.alongX Ty Tz Tx.positionObservable) ∧
      0 < centeredGramDefect (Tx.maxCurrentCubeVectorState Ty Tz)
        (Tx.alongY Ty Tz Ty.openHamiltonianObservable) (Tx.alongY Ty Tz Ty.positionObservable) ∧
      0 < centeredGramDefect (Tx.maxCurrentCubeVectorState Ty Tz)
        (Tx.alongZ Ty Tz Tz.openHamiltonianObservable) (Tx.alongZ Ty Tz Tz.positionObservable)) ∧
      0 < Tx.quantumDefect k ∧
      Tx.countCosmologicalConstant c k ℓ =
        3 * π * Tx.dimQuantum /
          (ℓ ^ 2 * Real.log (Tx.cutBonds c).card * Tx.quantumDefect k) :=
  ⟨Tx.nava_robertson_schrodinger_cube Ty Tz hx hy hz hNx hNy hNz,
    Tx.quantumDefect_pos hx hNx hk,
    Tx.countCosmologicalConstant_eq_quantumDefect Tx hx hNx c k ℓ⟩

end TightBindingChain
end CondensedMatter
