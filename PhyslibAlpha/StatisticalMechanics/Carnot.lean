/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.StatisticalMechanics.Landauer
/-!

# The second law: Kelvin–Planck and the Carnot bound

## i. Overview

A thermal state cannot be used as a fuel on its own. If a reservoir in its Gibbs state `γ`
evolves by any unitary `U`, its energy can only go up: `⟨H⟩_γ ≤ ⟨H⟩_{U γ U†}`. No cyclic process
extracts work from a single reservoir (Kelvin–Planck).

With two reservoirs, a hot one at `β_h` and a cold one at `β_c`, both starting in their Gibbs
states and evolving by a joint unitary `U`, let `Q_h` be the heat taken from the hot one and
`Q_c` the heat given to the cold one. Then `β_h Q_h ≤ β_c Q_c`, and the work `W = Q_h - Q_c`
obeys the Carnot bound `W ≤ (1 - β_h / β_c) Q_h = (1 - T_c / T_h) Q_h`.

Both follow from the two facts behind Landauer's principle: the entropy of `U (γ_h ⊗ γ_c) U†`
is `S(γ_h) + S(γ_c)`, and `S(σ) ≤ β ⟨H⟩_σ + log Z` with equality at the Gibbs state.

## ii. Key results

- `inner_gibbsState_le_uConj` : Kelvin–Planck, the Gibbs state is passive.
- `carnot_entropy` : `β_h Q_h ≤ β_c Q_c`.
- `carnot` : the Carnot bound `W ≤ (1 - β_h / β_c) Q_h`.
- `carnot_temperature` : the same bound with temperatures, `W ≤ (1 - T_c / T_h) Q_h`.

## iii. Table of contents

- A. Kelvin–Planck
- B. The Carnot bound
- C. The Carnot bound at two temperatures

## iv. References

* W. Pusz, S. L. Woronowicz, *Passive states and KMS states for general quantum systems*,
  Comm. Math. Phys. 58 (1978).
* D. Reeb, M. M. Wolf, *An improved Landauer principle with finite-size corrections*,
  New J. Phys. 16 (2014).
-/

@[expose] public section

noncomputable section

namespace MState

open scoped InnerProductSpace RealInnerProductSpace
open HermitianMat

variable {d dH dC : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
  [Fintype dH] [DecidableEq dH] [Nonempty dH] [Fintype dC] [DecidableEq dC] [Nonempty dC]

/-!

## A. Kelvin–Planck

-/

/-- **Kelvin–Planck.** At positive inverse temperature the Gibbs state is passive: no unitary
lowers its energy, so no work is extracted from a single reservoir. -/
theorem inner_gibbsState_le_uConj {β : ℝ} (hβ : 0 < β) (H : HermitianMat d ℂ) (U : 𝐔[d]) :
    ⟪(gibbsState β H).M, H⟫ ≤ ⟪((gibbsState β H).uConj U).M, H⟫ := by
  have h := Sᵥₙ_le_gibbs ((gibbsState β H).uConj U) β H
  rw [Sᵥₙ_uConj, Sᵥₙ_gibbsState] at h
  nlinarith

/-!

## B. The Carnot bound

-/

/-- The final state of two reservoirs, starting in their Gibbs states, after a joint unitary. -/
def carnotFinal (βh βc : ℝ) (Hh : HermitianMat dH ℂ) (Hc : HermitianMat dC ℂ)
    (U : 𝐔[dH × dC]) : MState (dH × dC) :=
  (gibbsState βh Hh ⊗ᴹ gibbsState βc Hc).uConj U

/-- The heat `Q_h = ⟨H_h⟩_γ - ⟨H_h⟩'` taken from the hot reservoir. -/
def heatHot (βh βc : ℝ) (Hh : HermitianMat dH ℂ) (Hc : HermitianMat dC ℂ)
    (U : 𝐔[dH × dC]) : ℝ :=
  ⟪(gibbsState βh Hh).M, Hh⟫ - ⟪(carnotFinal βh βc Hh Hc U).traceRight.M, Hh⟫

/-- The heat `Q_c = ⟨H_c⟩' - ⟨H_c⟩_γ` given to the cold reservoir. -/
def heatCold (βh βc : ℝ) (Hh : HermitianMat dH ℂ) (Hc : HermitianMat dC ℂ)
    (U : 𝐔[dH × dC]) : ℝ :=
  ⟪(carnotFinal βh βc Hh Hc U).traceLeft.M, Hc⟫ - ⟪(gibbsState βc Hc).M, Hc⟫

/-- The entropy balance of the two reservoirs: `β_h Q_h ≤ β_c Q_c`. -/
theorem carnot_entropy (βh βc : ℝ) (Hh : HermitianMat dH ℂ) (Hc : HermitianMat dC ℂ)
    (U : 𝐔[dH × dC]) :
    βh * heatHot βh βc Hh Hc U ≤ βc * heatCold βh βc Hh Hc U := by
  have hS : Sᵥₙ (carnotFinal βh βc Hh Hc U) =
      Sᵥₙ (gibbsState βh Hh) + Sᵥₙ (gibbsState βc Hc) := by
    rw [carnotFinal, Sᵥₙ_uConj, Sᵥₙ_prod]
  have hsub := Sᵥₙ_subadditivity (carnotFinal βh βc Hh Hc U)
  have hKh := Sᵥₙ_le_gibbs (carnotFinal βh βc Hh Hc U).traceRight βh Hh
  have hKc := Sᵥₙ_le_gibbs (carnotFinal βh βc Hh Hc U).traceLeft βc Hc
  rw [Sᵥₙ_gibbsState, Sᵥₙ_gibbsState] at hS
  rw [heatHot, heatCold]
  nlinarith

/-- **The Carnot bound.** If heat `Q_h ≥ 0` is taken from the hot reservoir, the work
`W = Q_h - Q_c` is at most `(1 - β_h / β_c) Q_h = (1 - T_c / T_h) Q_h`. -/
theorem carnot {βh βc : ℝ} (hβc : 0 < βc) (Hh : HermitianMat dH ℂ) (Hc : HermitianMat dC ℂ)
    (U : 𝐔[dH × dC]) :
    heatHot βh βc Hh Hc U - heatCold βh βc Hh Hc U ≤
      (1 - βh / βc) * heatHot βh βc Hh Hc U := by
  have h := carnot_entropy βh βc Hh Hc U
  have h' : βh / βc * heatHot βh βc Hh Hc U ≤ heatCold βh βc Hh Hc U := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hβc]
    linarith
  linarith

/-!

## C. The Carnot bound at two temperatures

-/

open Constants

/-- **The Carnot bound at two temperatures.** Between reservoirs at temperatures `T_h` and
`T_c`, the work is at most `(1 - T_c / T_h) Q_h`. -/
theorem carnot_temperature (Th Tc : Temperature) (hTh : 0 < Th.val) (hTc : 0 < Tc.val)
    (Hh : HermitianMat dH ℂ) (Hc : HermitianMat dC ℂ) (U : 𝐔[dH × dC]) :
    heatHot Th.β Tc.β Hh Hc U - heatCold Th.β Tc.β Hh Hc U ≤
      (1 - (Tc : ℝ) / Th) * heatHot Th.β Tc.β Hh Hc U := by
  have h := carnot (βh := Th.β) (Tc.beta_pos hTc) Hh Hc U
  have hTh' : (Th : ℝ) ≠ 0 := (show (0 : ℝ) < Th from hTh).ne'
  have hTc' : (Tc : ℝ) ≠ 0 := (show (0 : ℝ) < Tc from hTc).ne'
  have hr : (Th.β : ℝ) / Tc.β = (Tc : ℝ) / Th := by
    rw [Temperature.β_toReal, Temperature.β_toReal]
    field_simp
    exact div_self kB_ne_zero
  rwa [hr] at h

end MState
