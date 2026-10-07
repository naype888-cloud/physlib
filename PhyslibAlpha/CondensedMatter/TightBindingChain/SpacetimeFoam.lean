/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.CausalCone
public import PhyslibAlpha.CondensedMatter.TightBindingChain.VolumetricQuantum
/-!

# The spacetime foam of the open tight binding cube

## i. Overview

In the maximal current state, the proper time of the energy–position uncertainty vector of a
chain, in units of its bracket `|a t cos (π / (N + 1))|`, is `√(δ (δ + 2))`, where
`δ = C_Nava - 1` is the dimensional quantum. Saturation, `δ = 0`, is proper time zero; the excess
is the first time.

A cube `Nx × Ny × Nz` carries one proper time per axis. Their product, the foam time, satisfies
`foamTime² = volQuantum · (δx + 2)(δy + 2)(δz + 2)`: it vanishes exactly when the volumetric
quantum does, that is when some axis has `2` or `3` sites. From `4 × 4 × 4` on every axis has
positive proper time and the cell has positive volumetric quantum and foam time; the foam time
grows strictly in each axis, so no refinement lowers it, and it stays below `√(π² / 3 - 3)³`.

## ii. Key results

- `properTimeQuantum` : the proper time of a chain in units of its bracket.
- `properTimeQuantum_eq` : `properTimeQuantum = √(δ (δ + 2))`.
- `foamTime` : the product of the proper time quanta of the three axes.
- `foamTime_sq` : `foamTime² = volQuantum · (δx + 2)(δy + 2)(δz + 2)`.
- `foamTime_eq_zero_iff` : the foam time vanishes iff the volumetric quantum does.
- `foamTime_lt_foamTime_x` (and `y`, `z`), `foamTime_lt` : strict growth in each axis, below its
  limit.
- `properTime_alongX` (and `Y`, `Z`) : the proper time of an axis of the cube is that of its
  chain.
- `spacetimeFoam` : from `4 × 4 × 4` on, the three proper times, the volumetric quantum and the
  foam time are positive, and `foamTime² = volQuantum · (δx + 2)(δy + 2)(δz + 2)`.

## iii. Table of contents

- A. The proper time quantum of a chain
- B. The foam time of the cube
- C. The spacetime foam

## iv. References

* H. P. Robertson, *A general formulation of the uncertainty principle and its classical
  interpretation*, Phys. Rev. 35 (1930) 667.
* J. A. Wheeler, *Geons*, Phys. Rev. 97 (1955) 511.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain

open scoped ComplexOrder
open ProbabilisticTheory UnitalPositiveLinearMap

variable (T : TightBindingChain)

/-!

## A. The proper time quantum of a chain

-/

/-- The proper time of the maximal current state in units of the bracket
`|a t cos (π / (N + 1))|`. -/
noncomputable def properTimeQuantum : ℝ :=
  SpaceTime.properTime 0 (T.energyPositionVector T.maxCurrentVectorState) /
    |T.a * T.t * Real.cos (Real.pi / (T.N + 1))|

/-- The proper time quantum is `√(δ (δ + 2))`. -/
lemma properTimeQuantum_eq (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.properTimeQuantum = √(T.dimQuantum * (T.dimQuantum + 2)) := by
  rw [properTimeQuantum, T.properTime_maxCurrentState_div ht hN, dimQuantum]
  congr 1
  ring

lemma properTimeQuantum_nonneg : 0 ≤ T.properTimeQuantum :=
  div_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)

lemma properTimeQuantum_sq (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    T.properTimeQuantum ^ 2 = T.dimQuantum * (T.dimQuantum + 2) := by
  have := T.dimQuantum_nonneg ht hN
  rw [T.properTimeQuantum_eq ht hN, Real.sq_sqrt (by positivity)]

/-- From four sites on, the proper time quantum is positive. -/
lemma properTimeQuantum_pos (ht : T.t ≠ 0) (hN : 4 ≤ T.N) : 0 < T.properTimeQuantum := by
  have := T.dimQuantum_pos ht hN
  rw [T.properTimeQuantum_eq ht (by omega)]
  positivity

/-!

## B. The foam time of the cube

-/

variable (Tx Ty Tz : TightBindingChain)

/-- The foam time of the cube: the product of the proper time quanta of its three axes. -/
noncomputable def foamTime : ℝ :=
  Tx.properTimeQuantum * Ty.properTimeQuantum * Tz.properTimeQuantum

variable {Tx Ty Tz}

lemma foamTime_nonneg : 0 ≤ foamTime Tx Ty Tz :=
  mul_nonneg (mul_nonneg Tx.properTimeQuantum_nonneg Ty.properTimeQuantum_nonneg)
    Tz.properTimeQuantum_nonneg

/-- **The foam time squared is the volumetric quantum** times `(δx + 2)(δy + 2)(δz + 2)`. -/
theorem foamTime_sq (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) :
    foamTime Tx Ty Tz ^ 2 = volQuantum Tx Ty Tz *
      ((Tx.dimQuantum + 2) * (Ty.dimQuantum + 2) * (Tz.dimQuantum + 2)) := by
  rw [foamTime, mul_pow, mul_pow, Tx.properTimeQuantum_sq hx hNx, Ty.properTimeQuantum_sq hy hNy,
    Tz.properTimeQuantum_sq hz hNz, volQuantum]
  ring

/-- The foam time vanishes exactly when the volumetric quantum does. -/
theorem foamTime_eq_zero_iff (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) :
    foamTime Tx Ty Tz = 0 ↔ volQuantum Tx Ty Tz = 0 := by
  have := Tx.dimQuantum_nonneg hx hNx
  have := Ty.dimQuantum_nonneg hy hNy
  have := Tz.dimQuantum_nonneg hz hNz
  have hP : (Tx.dimQuantum + 2) * (Ty.dimQuantum + 2) * (Tz.dimQuantum + 2) ≠ 0 := by
    positivity
  rw [← pow_eq_zero_iff two_ne_zero, foamTime_sq hx hy hz hNx hNy hNz, mul_eq_zero,
    or_iff_left hP]

/-- From `4 × 4 × 4` on, the foam time grows strictly along `x`. -/
theorem foamTime_lt_foamTime_x {Tx' : TightBindingChain} (hx : Tx.t ≠ 0) (hx' : Tx'.t ≠ 0)
    (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0) (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N)
    (h : Tx.N < Tx'.N) : foamTime Tx Ty Tz < foamTime Tx' Ty Tz := by
  have := Ty.properTimeQuantum_pos hy hNy
  have := Tz.properTimeQuantum_pos hz hNz
  unfold foamTime
  gcongr
  exact properTime_maxCurrentState_div_lt hx hx' hNx h

/-- From `4 × 4 × 4` on, the foam time grows strictly along `y`. -/
theorem foamTime_lt_foamTime_y {Ty' : TightBindingChain} (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0)
    (hy' : Ty'.t ≠ 0) (hz : Tz.t ≠ 0) (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N)
    (h : Ty.N < Ty'.N) : foamTime Tx Ty Tz < foamTime Tx Ty' Tz := by
  have := Tx.properTimeQuantum_pos hx hNx
  have := Tz.properTimeQuantum_pos hz hNz
  unfold foamTime
  gcongr
  exact properTime_maxCurrentState_div_lt hy hy' hNy h

/-- From `4 × 4 × 4` on, the foam time grows strictly along `z`. -/
theorem foamTime_lt_foamTime_z {Tz' : TightBindingChain} (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0)
    (hz : Tz.t ≠ 0) (hz' : Tz'.t ≠ 0) (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N)
    (h : Tz.N < Tz'.N) : foamTime Tx Ty Tz < foamTime Tx Ty Tz' := by
  have := Tx.properTimeQuantum_pos hx hNx
  have := Ty.properTimeQuantum_pos hy hNy
  unfold foamTime
  gcongr
  exact properTime_maxCurrentState_div_lt hz hz' hNz h

/-- From `4 × 4 × 4` on, the foam time stays below `√(π² / 3 - 3)³`. -/
theorem foamTime_lt (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    foamTime Tx Ty Tz < √(Real.pi ^ 2 / 3 - 3) ^ 3 := by
  have := Tx.properTimeQuantum_pos hx hNx
  have := Ty.properTimeQuantum_pos hy hNy
  have := Tz.properTimeQuantum_pos hz hNz
  rw [foamTime, pow_three, ← mul_assoc]
  gcongr
  · exact Tx.properTime_maxCurrentState_div_lt_sqrt hx hNx
  · exact Ty.properTime_maxCurrentState_div_lt_sqrt hy hNy
  · exact Tz.properTime_maxCurrentState_div_lt_sqrt hz hNz

/-!

## C. The spacetime foam

-/

variable (Tx Ty Tz)

/-- The proper time of the `x` axis of the cube is the proper time of its chain. -/
lemma properTime_alongX :
    SpaceTime.properTime 0 (uncertaintyVector (Tx.maxCurrentCubeVectorState Ty Tz)
      (Tx.alongX Ty Tz Tx.openHamiltonianObservable) (Tx.alongX Ty Tz Tx.positionObservable)) =
      SpaceTime.properTime 0 (Tx.energyPositionVector Tx.maxCurrentVectorState) := by
  rw [properTime_energyPositionVector, SpaceTime.properTime, sub_zero,
    minkowskiProduct_uncertaintyVector, centeredGramDefect_alongX]

/-- The proper time of the `y` axis of the cube is the proper time of its chain. -/
lemma properTime_alongY :
    SpaceTime.properTime 0 (uncertaintyVector (Tx.maxCurrentCubeVectorState Ty Tz)
      (Tx.alongY Ty Tz Ty.openHamiltonianObservable) (Tx.alongY Ty Tz Ty.positionObservable)) =
      SpaceTime.properTime 0 (Ty.energyPositionVector Ty.maxCurrentVectorState) := by
  rw [properTime_energyPositionVector, SpaceTime.properTime, sub_zero,
    minkowskiProduct_uncertaintyVector, centeredGramDefect_alongY]

/-- The proper time of the `z` axis of the cube is the proper time of its chain. -/
lemma properTime_alongZ :
    SpaceTime.properTime 0 (uncertaintyVector (Tx.maxCurrentCubeVectorState Ty Tz)
      (Tx.alongZ Ty Tz Tz.openHamiltonianObservable) (Tx.alongZ Ty Tz Tz.positionObservable)) =
      SpaceTime.properTime 0 (Tz.energyPositionVector Tz.maxCurrentVectorState) := by
  rw [properTime_energyPositionVector, SpaceTime.properTime, sub_zero,
    minkowskiProduct_uncertaintyVector, centeredGramDefect_alongZ]

variable {Tx Ty Tz}

/-- **The spacetime foam of the cube.** From `4 × 4 × 4` on, in the maximal current state of the
cube every axis has positive proper time, the cell has positive volumetric quantum and positive
foam time, and the foam time squared is the volumetric quantum times
`(δx + 2)(δy + 2)(δz + 2)`. -/
theorem spacetimeFoam (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    (0 < SpaceTime.properTime 0 (uncertaintyVector (Tx.maxCurrentCubeVectorState Ty Tz)
        (Tx.alongX Ty Tz Tx.openHamiltonianObservable) (Tx.alongX Ty Tz Tx.positionObservable)) ∧
      0 < SpaceTime.properTime 0 (uncertaintyVector (Tx.maxCurrentCubeVectorState Ty Tz)
        (Tx.alongY Ty Tz Ty.openHamiltonianObservable) (Tx.alongY Ty Tz Ty.positionObservable)) ∧
      0 < SpaceTime.properTime 0 (uncertaintyVector (Tx.maxCurrentCubeVectorState Ty Tz)
        (Tx.alongZ Ty Tz Tz.openHamiltonianObservable)
        (Tx.alongZ Ty Tz Tz.positionObservable))) ∧
    0 < volQuantum Tx Ty Tz ∧ 0 < foamTime Tx Ty Tz ∧
    foamTime Tx Ty Tz ^ 2 = volQuantum Tx Ty Tz *
      ((Tx.dimQuantum + 2) * (Ty.dimQuantum + 2) * (Tz.dimQuantum + 2)) := by
  refine ⟨Tx.properTime_cube_pos Ty Tz hx hy hz hNx hNy hNz, volQuantum_pos hx hy hz hNx hNy hNz,
    ?_, foamTime_sq hx hy hz (by omega) (by omega) (by omega)⟩
  have := Tx.properTimeQuantum_pos hx hNx
  have := Ty.properTimeQuantum_pos hy hNy
  have := Tz.properTimeQuantum_pos hz hNz
  unfold foamTime
  positivity

end TightBindingChain
end CondensedMatter
