/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.VolumetricQuantum
/-!

# Conjugate pairs on the open tight binding chain

## i. Overview

A conjugate pair realized on the chain is `A = α H + β`, `B = γ X + ε` with real `α, γ ≠ 0`: the
units and origins of the pair (position–momentum, number–phase, charge–flux, …). Units and
origins scale the fluctuations of `H` and `X` and leave the Robertson–Schrödinger ratio
`σ_A σ_B / ‖ω(δA δB)‖` unchanged. In the maximal current state this ratio is `C_Nava` for every
pair: every pair saturates exactly for `N = 2, 3`, is strict from four sites on, and grows
strictly with `N` below `√(π² / 3 - 2)`. A pair only sets its floor `|α γ| |a t cos (π / (N + 1))|`.

On the cube each axis carries its own pair in its own units, and the product of the excesses of
the three pairs is the volumetric quantum.

## ii. Key results

- `robertsonSchrodingerRatio_maxCurrentState` : the ratio of `(H, X)` is `C_Nava`.
- `robertsonSchrodingerRatio_pair` : **the ratio of every pair is `C_Nava`.**
- `centeredGramDefect_pair_eq_zero_iff` : every pair saturates iff `N = 2, 3`.
- `one_lt_robertsonSchrodingerRatio_pair`, `robertsonSchrodingerRatio_pair_lt_pair`,
  `robertsonSchrodingerRatio_pair_lt` : strict from `N = 4`, strictly growing, below the limit.
- `robertsonSchrodingerRatio_pairX` (and `Y`, `Z`) : each axis of the cube carries its own pair.
- `volQuantum_pairs` : the excesses of the three pairs multiply to the volumetric quantum.

## iii. Table of contents

- A. One pair on the chain
- B. Three pairs on the cube

## iv. References

* H. P. Robertson, *A general formulation of the uncertainty principle and its classical
  interpretation*, Phys. Rev. 35 (1930) 667.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open ProbabilisticTheory UnitalPositiveLinearMap

variable (T : TightBindingChain)

/-!

## A. One pair on the chain

-/

/-- The pair `(α H + β, γ X + ε)`: energy and position in units `α`, `γ` with origins `β`, `ε`. -/
noncomputable abbrev energyPair (α β : ℝ) : Observable (T.HilbertSpace →L[ℂ] T.HilbertSpace) :=
  affineObservable α β T.openHamiltonianObservable

/-- The position member `γ X + ε` of a pair. -/
noncomputable abbrev positionPair (γ ε : ℝ) : Observable (T.HilbertSpace →L[ℂ] T.HilbertSpace) :=
  affineObservable γ ε T.positionObservable

/-- In the maximal current state the ratio of `(H, X)` is `C_Nava`. -/
lemma robertsonSchrodingerRatio_maxCurrentState :
    robertsonSchrodingerRatio T.maxCurrentVectorState T.openHamiltonianObservable
      T.positionObservable = T.CNava := by
  rw [robertsonSchrodingerRatio, ← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm,
    normSq_centered_pairing, covariance_maxCurrentState, expectation_bracket_maxCurrentState,
    CNava, sq, zero_mul, zero_add, neg_sq, Real.sqrt_sq_eq_abs]

variable {T} {α β γ ε : ℝ}

/-- **The ratio of every pair is `C_Nava`** in the maximal current state. -/
theorem robertsonSchrodingerRatio_pair (hα : α ≠ 0) (hγ : γ ≠ 0) :
    robertsonSchrodingerRatio T.maxCurrentVectorState (T.energyPair α β) (T.positionPair γ ε) =
      T.CNava := by
  rw [robertsonSchrodingerRatio_affineObservable _ _ _ _ _ hα hγ,
    robertsonSchrodingerRatio_maxCurrentState]

/-- **Every pair saturates exactly for `N = 2` and `N = 3`.** -/
theorem centeredGramDefect_pair_eq_zero_iff (hα : α ≠ 0) (hγ : γ ≠ 0) (ht : T.t ≠ 0)
    (hN : 2 ≤ T.N) :
    centeredGramDefect T.maxCurrentVectorState (T.energyPair α β) (T.positionPair γ ε) = 0 ↔
      T.N = 2 ∨ T.N = 3 := by
  rw [centeredGramDefect_affineObservable, mul_eq_zero, or_iff_right (by positivity),
    centeredGramDefect_maxCurrentState_eq_zero_iff T ht hN]

/-- From four sites on, the ratio of every pair is strictly larger than one. -/
lemma one_lt_robertsonSchrodingerRatio_pair (hα : α ≠ 0) (hγ : γ ≠ 0) (ht : T.t ≠ 0)
    (hN : 4 ≤ T.N) :
    1 < robertsonSchrodingerRatio T.maxCurrentVectorState (T.energyPair α β)
      (T.positionPair γ ε) := by
  rw [robertsonSchrodingerRatio_pair hα hγ]
  exact T.one_lt_CNava ht hN

/-- From four sites on, the ratio grows strictly with `N`, even if the two pairs carry different
units. -/
theorem robertsonSchrodingerRatio_pair_lt_pair {T' : TightBindingChain} {α' β' γ' ε' : ℝ}
    (hα : α ≠ 0) (hγ : γ ≠ 0) (hα' : α' ≠ 0) (hγ' : γ' ≠ 0) (ht : T.t ≠ 0) (ht' : T'.t ≠ 0)
    (hN : 4 ≤ T.N) (hNN' : T.N < T'.N) :
    robertsonSchrodingerRatio T.maxCurrentVectorState (T.energyPair α β) (T.positionPair γ ε) <
      robertsonSchrodingerRatio T'.maxCurrentVectorState (T'.energyPair α' β')
        (T'.positionPair γ' ε') := by
  rw [robertsonSchrodingerRatio_pair hα hγ, robertsonSchrodingerRatio_pair hα' hγ']
  exact CNava_lt_CNava ht ht' hN hNN'

/-- From four sites on, the ratio of every pair stays below `√(π² / 3 - 2)`. -/
lemma robertsonSchrodingerRatio_pair_lt (hα : α ≠ 0) (hγ : γ ≠ 0) (ht : T.t ≠ 0)
    (hN : 4 ≤ T.N) :
    robertsonSchrodingerRatio T.maxCurrentVectorState (T.energyPair α β) (T.positionPair γ ε) <
      √(Real.pi ^ 2 / 3 - 2) := by
  rw [robertsonSchrodingerRatio_pair hα hγ]
  exact T.CNava_lt_sqrt_pi_sq_div_three_sub_two ht hN

/-- The excess of every pair over saturation is the dimensional quantum. -/
lemma robertsonSchrodingerRatio_pair_sub_one (hα : α ≠ 0) (hγ : γ ≠ 0) :
    robertsonSchrodingerRatio T.maxCurrentVectorState (T.energyPair α β) (T.positionPair γ ε) -
      1 = T.dimQuantum := by
  rw [robertsonSchrodingerRatio_pair hα hγ, dimQuantum]

/-!

## B. Three pairs on the cube

-/

variable (Tx Ty Tz : TightBindingChain)

/-- Along `x`, the cube sees the ratio of the chain `Tx`. -/
lemma robertsonSchrodingerRatio_alongX
    (a b : Observable (Tx.HilbertSpace →L[ℂ] Tx.HilbertSpace)) :
    robertsonSchrodingerRatio (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongX Ty Tz a)
      (Tx.alongX Ty Tz b) = robertsonSchrodingerRatio Tx.maxCurrentVectorState a b := by
  rw [robertsonSchrodingerRatio_eq, robertsonSchrodingerRatio_eq, variance_alongX,
    variance_alongX, centeredGramDefect_alongX]

/-- Along `y`, the cube sees the ratio of the chain `Ty`. -/
lemma robertsonSchrodingerRatio_alongY
    (a b : Observable (Ty.HilbertSpace →L[ℂ] Ty.HilbertSpace)) :
    robertsonSchrodingerRatio (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongY Ty Tz a)
      (Tx.alongY Ty Tz b) = robertsonSchrodingerRatio Ty.maxCurrentVectorState a b := by
  rw [robertsonSchrodingerRatio_eq, robertsonSchrodingerRatio_eq, variance_alongY,
    variance_alongY, centeredGramDefect_alongY]

/-- Along `z`, the cube sees the ratio of the chain `Tz`. -/
lemma robertsonSchrodingerRatio_alongZ
    (a b : Observable (Tz.HilbertSpace →L[ℂ] Tz.HilbertSpace)) :
    robertsonSchrodingerRatio (Tx.maxCurrentCubeVectorState Ty Tz) (Tx.alongZ Ty Tz a)
      (Tx.alongZ Ty Tz b) = robertsonSchrodingerRatio Tz.maxCurrentVectorState a b := by
  rw [robertsonSchrodingerRatio_eq, robertsonSchrodingerRatio_eq, variance_alongZ,
    variance_alongZ, centeredGramDefect_alongZ]

variable {Tx Ty Tz} {αx βx γx εx αy βy γy εy αz βz γz εz : ℝ}

/-- The pair of the `x` axis of the cube, in its own units, has ratio `C_Nava(Nx)`. -/
lemma robertsonSchrodingerRatio_pairX (hα : αx ≠ 0) (hγ : γx ≠ 0) :
    robertsonSchrodingerRatio (Tx.maxCurrentCubeVectorState Ty Tz)
      (affineObservable αx βx (Tx.alongX Ty Tz Tx.openHamiltonianObservable))
      (affineObservable γx εx (Tx.alongX Ty Tz Tx.positionObservable)) = Tx.CNava := by
  rw [robertsonSchrodingerRatio_affineObservable _ _ _ _ _ hα hγ, robertsonSchrodingerRatio_alongX,
    robertsonSchrodingerRatio_maxCurrentState]

/-- The pair of the `y` axis of the cube, in its own units, has ratio `C_Nava(Ny)`. -/
lemma robertsonSchrodingerRatio_pairY (hα : αy ≠ 0) (hγ : γy ≠ 0) :
    robertsonSchrodingerRatio (Tx.maxCurrentCubeVectorState Ty Tz)
      (affineObservable αy βy (Tx.alongY Ty Tz Ty.openHamiltonianObservable))
      (affineObservable γy εy (Tx.alongY Ty Tz Ty.positionObservable)) = Ty.CNava := by
  rw [robertsonSchrodingerRatio_affineObservable _ _ _ _ _ hα hγ, robertsonSchrodingerRatio_alongY,
    robertsonSchrodingerRatio_maxCurrentState]

/-- The pair of the `z` axis of the cube, in its own units, has ratio `C_Nava(Nz)`. -/
lemma robertsonSchrodingerRatio_pairZ (hα : αz ≠ 0) (hγ : γz ≠ 0) :
    robertsonSchrodingerRatio (Tx.maxCurrentCubeVectorState Ty Tz)
      (affineObservable αz βz (Tx.alongZ Ty Tz Tz.openHamiltonianObservable))
      (affineObservable γz εz (Tx.alongZ Ty Tz Tz.positionObservable)) = Tz.CNava := by
  rw [robertsonSchrodingerRatio_affineObservable _ _ _ _ _ hα hγ, robertsonSchrodingerRatio_alongZ,
    robertsonSchrodingerRatio_maxCurrentState]

/-- **The volumetric quantum of three pairs.** Whatever the units of each axis, the product of
the excesses of the three pairs of the cube is `δ(Nx) δ(Ny) δ(Nz)`. -/
theorem volQuantum_pairs (hαx : αx ≠ 0) (hγx : γx ≠ 0) (hαy : αy ≠ 0) (hγy : γy ≠ 0)
    (hαz : αz ≠ 0) (hγz : γz ≠ 0) :
    (robertsonSchrodingerRatio (Tx.maxCurrentCubeVectorState Ty Tz)
        (affineObservable αx βx (Tx.alongX Ty Tz Tx.openHamiltonianObservable))
        (affineObservable γx εx (Tx.alongX Ty Tz Tx.positionObservable)) - 1) *
      (robertsonSchrodingerRatio (Tx.maxCurrentCubeVectorState Ty Tz)
        (affineObservable αy βy (Tx.alongY Ty Tz Ty.openHamiltonianObservable))
        (affineObservable γy εy (Tx.alongY Ty Tz Ty.positionObservable)) - 1) *
      (robertsonSchrodingerRatio (Tx.maxCurrentCubeVectorState Ty Tz)
        (affineObservable αz βz (Tx.alongZ Ty Tz Tz.openHamiltonianObservable))
        (affineObservable γz εz (Tx.alongZ Ty Tz Tz.positionObservable)) - 1) =
      volQuantum Tx Ty Tz := by
  rw [robertsonSchrodingerRatio_pairX hαx hγx, robertsonSchrodingerRatio_pairY hαy hγy,
    robertsonSchrodingerRatio_pairZ hαz hγz, volQuantum, dimQuantum, dimQuantum, dimQuantum]

end TightBindingChain
end CondensedMatter
