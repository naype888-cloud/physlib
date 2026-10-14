/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.Basic
public import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentState.FluctuationAngle
/-!

# The uncertainty excess of the open tight binding cube

## i. Overview

A cube `Nx × Ny × Nz` carries one uncertainty ratio `C` per axis (`uncertaintyRatio_alongX`,
`uncertaintyRatio_alongY`, `uncertaintyRatio_alongZ`), so it carries the product
`δ(Nx) δ(Ny) δ(Nz)` of the uncertainty excesses `δ = C - 1` of its axes. This product vanishes
iff some axis has `2` or `3` sites, is positive from `4 × 4 × 4` on, grows strictly in each axis
and stays below `(√(π² / 3 - 2) - 1)³`.

## ii. Key results

- `cubeUncertaintyExcess` : the product `δ(Nx) δ(Ny) δ(Nz)` of the uncertainty excesses.
- `cubeUncertaintyExcess_eq_zero_iff`, `cubeUncertaintyExcess_pos` : it vanishes iff some axis
  has `2` or `3` sites.
- `cubeUncertaintyExcess_lt_cubeUncertaintyExcess_x` (and `y`, `z`), `cubeUncertaintyExcess_lt` :
  strict growth in each axis, below its limit.

## iii. Table of contents

- A. The uncertainty excess of the cube

## iv. References

* H. P. Robertson, *A general formulation of the uncertainty principle and its classical
  interpretation*, Phys. Rev. 35 (1930) 667.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open ProbabilisticTheory UnitalPositiveLinearMap

/-!

## A. The uncertainty excess of the cube

-/

variable (Tx Ty Tz : TightBindingChain)

/-- The uncertainty excess of the cube `Nx × Ny × Nz`: the product of the uncertainty excesses of
its axes, each axis carrying its own `C` (`uncertaintyRatio_alongX`, `uncertaintyRatio_alongY`,
`uncertaintyRatio_alongZ`). -/
noncomputable def cubeUncertaintyExcess : ℝ :=
  Tx.uncertaintyExcess * Ty.uncertaintyExcess * Tz.uncertaintyExcess

variable {Tx Ty Tz}

/-- The uncertainty excess of the cube vanishes iff some axis has `2` or `3` sites. -/
lemma cubeUncertaintyExcess_eq_zero_iff (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 2 ≤ Tx.N) (hNy : 2 ≤ Ty.N) (hNz : 2 ≤ Tz.N) :
    cubeUncertaintyExcess Tx Ty Tz = 0 ↔
      (Tx.N = 2 ∨ Tx.N = 3) ∨ (Ty.N = 2 ∨ Ty.N = 3) ∨ (Tz.N = 2 ∨ Tz.N = 3) := by
  rw [cubeUncertaintyExcess, mul_eq_zero, mul_eq_zero, Tx.uncertaintyExcess_eq_zero_iff hx hNx,
    Ty.uncertaintyExcess_eq_zero_iff hy hNy, Tz.uncertaintyExcess_eq_zero_iff hz hNz, or_assoc]

/-- From `4 × 4 × 4` on, the uncertainty excess of the cube is positive. -/
lemma cubeUncertaintyExcess_pos (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) : 0 < cubeUncertaintyExcess Tx Ty Tz :=
  mul_pos (mul_pos (Tx.uncertaintyExcess_pos hx hNx) (Ty.uncertaintyExcess_pos hy hNy))
    (Tz.uncertaintyExcess_pos hz hNz)

/-- From `4 × 4 × 4` on, the uncertainty excess of the cube grows strictly along `x`. -/
lemma cubeUncertaintyExcess_lt_cubeUncertaintyExcess_x {Tx' : TightBindingChain} (hx : Tx.t ≠ 0)
    (hx' : Tx'.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) (h : Tx.N < Tx'.N) :
    cubeUncertaintyExcess Tx Ty Tz < cubeUncertaintyExcess Tx' Ty Tz := by
  have := Ty.uncertaintyExcess_pos hy hNy
  have := Tz.uncertaintyExcess_pos hz hNz
  unfold cubeUncertaintyExcess
  gcongr
  exact uncertaintyExcess_lt_uncertaintyExcess hx hx' hNx h

/-- From `4 × 4 × 4` on, the uncertainty excess of the cube grows strictly along `y`. -/
lemma cubeUncertaintyExcess_lt_cubeUncertaintyExcess_y {Ty' : TightBindingChain} (hx : Tx.t ≠ 0)
    (hy : Ty.t ≠ 0) (hy' : Ty'.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) (h : Ty.N < Ty'.N) :
    cubeUncertaintyExcess Tx Ty Tz < cubeUncertaintyExcess Tx Ty' Tz := by
  have := Tx.uncertaintyExcess_pos hx hNx
  have := Tz.uncertaintyExcess_pos hz hNz
  unfold cubeUncertaintyExcess
  gcongr
  exact uncertaintyExcess_lt_uncertaintyExcess hy hy' hNy h

/-- From `4 × 4 × 4` on, the uncertainty excess of the cube grows strictly along `z`. -/
lemma cubeUncertaintyExcess_lt_cubeUncertaintyExcess_z {Tz' : TightBindingChain} (hx : Tx.t ≠ 0)
    (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0) (hz' : Tz'.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) (h : Tz.N < Tz'.N) :
    cubeUncertaintyExcess Tx Ty Tz < cubeUncertaintyExcess Tx Ty Tz' := by
  have := Tx.uncertaintyExcess_pos hx hNx
  have := Ty.uncertaintyExcess_pos hy hNy
  unfold cubeUncertaintyExcess
  gcongr
  exact uncertaintyExcess_lt_uncertaintyExcess hz hz' hNz h

/-- From `4 × 4 × 4` on, the uncertainty excess of the cube stays below
`(√(π² / 3 - 2) - 1)³`. -/
lemma cubeUncertaintyExcess_lt (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0) (hz : Tz.t ≠ 0)
    (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    cubeUncertaintyExcess Tx Ty Tz < (√(Real.pi ^ 2 / 3 - 2) - 1) ^ 3 := by
  have := Tx.uncertaintyExcess_pos hx hNx
  have := Ty.uncertaintyExcess_pos hy hNy
  have := Tz.uncertaintyExcess_pos hz hNz
  rw [cubeUncertaintyExcess, pow_three, ← mul_assoc]
  gcongr
  · exact Tx.uncertaintyExcess_lt hx hNx
  · exact Ty.uncertaintyExcess_lt hy hNy
  · exact Tz.uncertaintyExcess_lt hz hNz

end TightBindingChain
end CondensedMatter
