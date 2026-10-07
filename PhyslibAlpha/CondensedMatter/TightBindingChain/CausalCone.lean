/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.LongChainMonotonicity
public import PhyslibAlpha.CondensedMatter.TightBindingChain.SpeedLimit
public import PhyslibAlpha.CondensedMatter.TightBindingChain.UncertaintyCone
public import Physlib.Relativity.Special.ProperTime
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.CausallyFollows
/-!

# The causal cone and the proper time of the energy–position uncertainty

## i. Overview

The Pauli four-vector of the Gram matrix of two fluctuations is a Lorentz vector, the
uncertainty vector. Its Minkowski square is the centered Gram defect, so the
Robertson–Schrödinger relation says exactly that the uncertainty vector causally follows the
origin: it lies in the causal future of `0` in the sense of `Lorentz.Vector.causallyFollows`.

For the energy and position of the open tight binding chain, the bracket component of the
uncertainty vector is half the current `⟨J⟩ = ⟨i [H, X]⟩`, the velocity of the electron. The
speed limit of the chain bounds it by `maxCurrent / 2` in every state. The maximal current state
reaches that bound; its uncertainty vector is lightlike exactly for `N = 2, 3` and timelike from
four sites on.

The proper time of the uncertainty vector, `SpaceTime.properTime 0 v = √⟪v, v⟫ₘ`, is the square
root of the centered Gram defect. Saturation, on the light cone, is proper time zero; the excess
over saturation is the first time. In the maximal current state it is
`|a t cos (π / (N + 1))| √(C_Nava² - 1)`: zero exactly for `N = 2, 3`, positive from four sites
on, strictly increasing with `N` in units of the bracket and below `√(π² / 3 - 3)`. On the cube
each axis has its own positive proper time from `4 × 4 × 4` on.

## ii. Key results

- `uncertaintyVector` : the uncertainty vector of two observables, a Lorentz vector.
- `minkowskiProduct_uncertaintyVector` : its Minkowski square is the centered Gram defect.
- `causallyFollows_uncertaintyVector` : it causally follows the origin.
- `energyPositionVector_inr_one` : for the chain, its bracket component is `⟨J⟩ / 2`.
- `causallyFollows_energyPositionVector_and_abs_le` : in every state it causally follows the
  origin and its bracket component is at most `maxCurrent / 2`.
- `abs_energyPositionVector_maxCurrentState_inr_one` : the maximal current state reaches the
  bound.
- `lightLike_energyPositionVector_maxCurrentState_iff`,
  `timeLike_energyPositionVector_maxCurrentState` : lightlike iff `N = 2, 3`, timelike for
  `N ≥ 4`.
- `properTime_energyPositionVector` : the proper time is `√(centered Gram defect)`.
- `properTime_maxCurrentState_eq_zero_iff`, `properTime_maxCurrentState_pos` : zero iff
  `N = 2, 3`, positive for `N ≥ 4`.
- `properTime_maxCurrentState_div_lt`, `properTime_maxCurrentState_div_lt_sqrt` : in units of
  the bracket it grows strictly with `N`, below `√(π² / 3 - 3)`.
- `properTime_cube_pos` : the three axes of the cube have positive proper time from `4 × 4 × 4`
  on.

## iii. Table of contents

- A. The uncertainty vector
- B. The energy–position vector of the open tight binding chain
- C. The proper time of the uncertainty

## iv. References

* H. P. Robertson, *A general formulation of the uncertainty principle and its classical
  interpretation*, Phys. Rev. 35 (1930) 667.

-/

@[expose] public section

namespace ProbabilisticTheory
namespace UnitalPositiveLinearMap

open scoped ComplexOrder
open Lorentz Vector PauliMatrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (ω : 𝓢[ℂ, A]) (a b : Observable A)

/-!

## A. The uncertainty vector

-/

/-- The uncertainty vector of `a` and `b` in `ω`: the Pauli four-vector of their Gram matrix, as
a Lorentz vector. -/
noncomputable def uncertaintyVector : Lorentz.Vector 3 :=
  pauliCoeff (gramMatrix ω a b)

/-- The Minkowski square of the uncertainty vector is the centered Gram defect. -/
lemma minkowskiProduct_uncertaintyVector :
    ⟪uncertaintyVector ω a b, uncertaintyVector ω a b⟫ₘ = centeredGramDefect ω a b := by
  have hd := det_gramMatrix ω a b
  rw [det_eq_scalarCoeff_sq_sub_pauliRadius_sq, Complex.ofReal_inj] at hd
  rw [← hd, minkowskiProduct_toCoord, pauliRadius, Real.sq_sqrt (by positivity)]
  simp [uncertaintyVector, scalarCoeff, vectorCoeff, sq]

/-- **Robertson–Schrödinger is causality.** The uncertainty vector causally follows the origin. -/
theorem causallyFollows_uncertaintyVector : causallyFollows 0 (uncertaintyVector ω a b) := by
  rw [causallyFollows_zero_iff, minkowskiProduct_uncertaintyVector]
  exact ⟨centeredGramDefect_nonneg ω a b, (pauliRadius_gramMatrix_le ω a b).1⟩

end UnitalPositiveLinearMap
end ProbabilisticTheory

namespace CondensedMatter
namespace TightBindingChain

open scoped ComplexOrder
open ProbabilisticTheory UnitalPositiveLinearMap Lorentz Vector PauliMatrix

variable (T : TightBindingChain)

/-!

## B. The energy–position vector of the open tight binding chain

-/

/-- The uncertainty vector of the energy and the position of the chain in the state `ω`. -/
noncomputable def energyPositionVector (ω : 𝓢[ℂ, T.HilbertSpace →L[ℂ] T.HilbertSpace]) :
    Lorentz.Vector 3 :=
  uncertaintyVector ω T.openHamiltonianObservable T.positionObservable

/-- The bracket component of the energy–position vector is half the current. -/
lemma energyPositionVector_inr_one (ω : 𝓢[ℂ, T.HilbertSpace →L[ℂ] T.HilbertSpace]) :
    T.energyPositionVector ω (Sum.inr 1) = ω⟨T.currentObservable⟩ / 2 := by
  change vectorCoeff _ 1 = _
  rw [(vectorCoeff_gramMatrix _ _ _).2.1, expectation_bracket_openHamiltonian_position]
  ring

/-- **The causal cone of the energy–position uncertainty.** In every state of the chain the
energy–position vector causally follows the origin, and its bracket component, half the velocity
of the electron, is at most `maxCurrent / 2`. -/
theorem causallyFollows_energyPositionVector_and_abs_le (ht : T.t ≠ 0)
    (ω : 𝓢[ℂ, T.HilbertSpace →L[ℂ] T.HilbertSpace]) :
    causallyFollows 0 (T.energyPositionVector ω) ∧
      |T.energyPositionVector ω (Sum.inr 1)| ≤ T.maxCurrent / 2 := by
  refine ⟨causallyFollows_uncertaintyVector _ _ _, ?_⟩
  rw [energyPositionVector_inr_one, abs_div, abs_two]
  linarith [T.abs_expectation_current_le ht ω]

/-- The maximal current state reaches the bound of the bracket component. -/
lemma abs_energyPositionVector_maxCurrentState_inr_one :
    |T.energyPositionVector T.maxCurrentVectorState (Sum.inr 1)| = T.maxCurrent / 2 := by
  rw [energyPositionVector_inr_one, abs_div, abs_two, abs_expectation_current_maxCurrentState]

/-- The energy–position vector of the maximal current state is lightlike exactly for `N = 2` and
`N = 3`. -/
theorem lightLike_energyPositionVector_maxCurrentState_iff (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    causalCharacter (T.energyPositionVector T.maxCurrentVectorState) =
      CausalCharacter.lightLike ↔ T.N = 2 ∨ T.N = 3 := by
  rw [lightLike_iff_norm_sq_zero, energyPositionVector, minkowskiProduct_uncertaintyVector,
    T.centeredGramDefect_maxCurrentState_eq_zero_iff ht hN]

/-- From four sites on, the energy–position vector of the maximal current state is timelike. -/
theorem timeLike_energyPositionVector_maxCurrentState (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    causalCharacter (T.energyPositionVector T.maxCurrentVectorState) =
      CausalCharacter.timeLike := by
  rw [timeLike_iff_norm_sq_pos, energyPositionVector, minkowskiProduct_uncertaintyVector]
  refine (centeredGramDefect_nonneg _ _ _).lt_of_ne fun h => ?_
  rcases (T.centeredGramDefect_maxCurrentState_eq_zero_iff ht (by omega)).mp h.symm with h | h <;>
    omega

/-!

## C. The proper time of the uncertainty

-/

/-- The proper time of the energy–position vector is the square root of the centered Gram
defect. -/
lemma properTime_energyPositionVector (ω : 𝓢[ℂ, T.HilbertSpace →L[ℂ] T.HilbertSpace]) :
    SpaceTime.properTime 0 (T.energyPositionVector ω) =
      √(centeredGramDefect ω T.openHamiltonianObservable T.positionObservable) := by
  rw [SpaceTime.properTime, sub_zero, energyPositionVector, minkowskiProduct_uncertaintyVector]

/-- In the maximal current state the proper time is `|a t cos (π / (N + 1))| √(C_Nava² - 1)`. -/
lemma properTime_maxCurrentState (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    SpaceTime.properTime 0 (T.energyPositionVector T.maxCurrentVectorState) =
      |T.a * T.t * Real.cos (Real.pi / (T.N + 1))| * √(T.CNava ^ 2 - 1) := by
  have hb : |T.a * T.t * Real.cos (Real.pi / (T.N + 1))| ≠ 0 := fun h => by
    have := T.one_le_CNava ht hN
    rw [CNava, h, div_zero] at this
    linarith
  have hv : 0 ≤ variance T.maxCurrentVectorState T.openHamiltonianObservable *
      variance T.maxCurrentVectorState T.positionObservable :=
    mul_nonneg (variance_nonneg _ _) (variance_nonneg _ _)
  rw [properTime_energyPositionVector, centeredGramDefect, normSq_centered_pairing,
    covariance_maxCurrentState, expectation_bracket_maxCurrentState, ← Real.sqrt_sq (abs_nonneg _),
    ← Real.sqrt_mul (sq_nonneg _), CNava, div_pow, Real.sq_sqrt hv, sq_abs]
  congr 1
  rw [mul_sub, mul_one, mul_div_cancel₀ _ (pow_ne_zero 2 (abs_ne_zero.mp hb))]
  ring

/-- **Saturation is time zero.** The proper time of the maximal current state vanishes exactly
for `N = 2` and `N = 3`, where the uncertainty vector lies on the light cone. -/
theorem properTime_maxCurrentState_eq_zero_iff (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    SpaceTime.properTime 0 (T.energyPositionVector T.maxCurrentVectorState) = 0 ↔
      T.N = 2 ∨ T.N = 3 := by
  rw [properTime_energyPositionVector, Real.sqrt_eq_zero (centeredGramDefect_nonneg _ _ _),
    T.centeredGramDefect_maxCurrentState_eq_zero_iff ht hN]

/-- **The excess is the first time.** From four sites on, the proper time of the maximal current
state is positive. -/
theorem properTime_maxCurrentState_pos (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    0 < SpaceTime.properTime 0 (T.energyPositionVector T.maxCurrentVectorState) :=
  SpaceTime.properTime_pos_ofTimeLike _ _ <| by
    rw [sub_zero]
    exact T.timeLike_energyPositionVector_maxCurrentState ht hN

/-- In units of the bracket, the proper time of the maximal current state is
`√(C_Nava² - 1)`. -/
lemma properTime_maxCurrentState_div (ht : T.t ≠ 0) (hN : 2 ≤ T.N) :
    SpaceTime.properTime 0 (T.energyPositionVector T.maxCurrentVectorState) /
        |T.a * T.t * Real.cos (Real.pi / (T.N + 1))| = √(T.CNava ^ 2 - 1) := by
  have hb : |T.a * T.t * Real.cos (Real.pi / (T.N + 1))| ≠ 0 := fun h => by
    have := T.one_le_CNava ht hN
    rw [CNava, h, div_zero] at this
    linarith
  rw [T.properTime_maxCurrentState ht hN, mul_div_cancel_left₀ _ hb]

/-- **The first time grows with the dimension.** From four sites on, the proper time of the
maximal current state, in units of the bracket, strictly increases with the number of sites. -/
theorem properTime_maxCurrentState_div_lt {T T' : TightBindingChain} (ht : T.t ≠ 0)
    (ht' : T'.t ≠ 0) (hN : 4 ≤ T.N) (hNN' : T.N < T'.N) :
    SpaceTime.properTime 0 (T.energyPositionVector T.maxCurrentVectorState) /
        |T.a * T.t * Real.cos (Real.pi / (T.N + 1))| <
      SpaceTime.properTime 0 (T'.energyPositionVector T'.maxCurrentVectorState) /
        |T'.a * T'.t * Real.cos (Real.pi / (T'.N + 1))| := by
  rw [T.properTime_maxCurrentState_div ht (by omega),
    T'.properTime_maxCurrentState_div ht' (by omega)]
  have h1 := T.one_le_CNava ht (by omega)
  have h := CNava_lt_CNava ht ht' hN hNN'
  exact Real.sqrt_lt_sqrt (by nlinarith) (by nlinarith)

/-- From four sites on, the proper time of the maximal current state, in units of the bracket,
stays below `√(π² / 3 - 3)`. -/
theorem properTime_maxCurrentState_div_lt_sqrt (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    SpaceTime.properTime 0 (T.energyPositionVector T.maxCurrentVectorState) /
        |T.a * T.t * Real.cos (Real.pi / (T.N + 1))| < √(Real.pi ^ 2 / 3 - 3) := by
  rw [T.properTime_maxCurrentState_div ht (by omega)]
  have h1 := T.one_le_CNava ht (by omega)
  have h := T.CNava_lt_sqrt_pi_sq_div_three_sub_two ht hN
  have hp : 0 ≤ Real.pi ^ 2 / 3 - 2 := by nlinarith [Real.pi_gt_three]
  have h2 : T.CNava ^ 2 < Real.pi ^ 2 / 3 - 2 := by
    calc T.CNava ^ 2 < √(Real.pi ^ 2 / 3 - 2) ^ 2 := by gcongr
      _ = Real.pi ^ 2 / 3 - 2 := Real.sq_sqrt hp
  exact Real.sqrt_lt_sqrt (by nlinarith) (by linarith)

/-- **The three first times of the cube.** From `4 × 4 × 4` on, the proper time of the
uncertainty vector of each axis of the maximal current state of the cube is positive. -/
theorem properTime_cube_pos (Tx Ty Tz : TightBindingChain) (hx : Tx.t ≠ 0) (hy : Ty.t ≠ 0)
    (hz : Tz.t ≠ 0) (hNx : 4 ≤ Tx.N) (hNy : 4 ≤ Ty.N) (hNz : 4 ≤ Tz.N) :
    0 < SpaceTime.properTime 0 (uncertaintyVector (Tx.maxCurrentCubeVectorState Ty Tz)
        (Tx.alongX Ty Tz Tx.openHamiltonianObservable) (Tx.alongX Ty Tz Tx.positionObservable)) ∧
      0 < SpaceTime.properTime 0 (uncertaintyVector (Tx.maxCurrentCubeVectorState Ty Tz)
        (Tx.alongY Ty Tz Ty.openHamiltonianObservable) (Tx.alongY Ty Tz Ty.positionObservable)) ∧
      0 < SpaceTime.properTime 0 (uncertaintyVector (Tx.maxCurrentCubeVectorState Ty Tz)
        (Tx.alongZ Ty Tz Tz.openHamiltonianObservable)
        (Tx.alongZ Ty Tz Tz.positionObservable)) := by
  obtain ⟨h1, h2, h3⟩ := Tx.nava_robertson_schrodinger_cube Ty Tz hx hy hz hNx hNy hNz
  simp only [SpaceTime.properTime, sub_zero, minkowskiProduct_uncertaintyVector]
  exact ⟨Real.sqrt_pos.mpr h1, Real.sqrt_pos.mpr h2, Real.sqrt_pos.mpr h3⟩

end TightBindingChain
end CondensedMatter
