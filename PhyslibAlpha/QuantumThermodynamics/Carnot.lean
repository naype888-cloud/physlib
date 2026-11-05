/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.QuantumThermodynamics.Landauer
public import QuantumInfo.Entropy.SSA

/-!
# Kelvin–Planck and the Carnot bound

This file builds on the thermal state and the Gibbs relative-entropy balance of
`PhyslibAlpha.QuantumThermodynamics.ThermalState`.

A thermal state cannot be used as a fuel on its own: if a reservoir in its thermal state
evolves by any unitary `U`, its expected energy can only go up (Kelvin–Planck). With two
reservoirs, hot at `β_h` and cold at `β_c`, both starting in their thermal states and evolving
by a joint unitary, let `Q_h` be the heat taken from the hot one and `Q_c` the heat given to the
cold one. Then `β_h Q_h ≤ β_c Q_c`, and the work `W = Q_h - Q_c` obeys
`W ≤ (1 - β_h / β_c) Q_h`.

## i. Key results

- `MState.exp_val_thermalBetaReal_le_uConj` : Kelvin–Planck, the thermal state is passive.
- `QuantumThermodynamics.carnot_entropy` : `β_h Q_h ≤ β_c Q_c`.
- `QuantumThermodynamics.carnot` : the Carnot bound `W ≤ (1 - β_h / β_c) Q_h`.

## ii. Table of contents

- A. Kelvin–Planck
- B. The Carnot bound

## iii. References

* W. Pusz, S. L. Woronowicz, *Passive states and KMS states for general quantum systems*,
  Comm. Math. Phys. 58 (1978).
* D. Reeb, M. M. Wolf, *An improved Landauer principle with finite-size corrections*,
  New J. Phys. 16 (2014).
-/

@[expose] public section

noncomputable section

open scoped MState

/-!
## A. Kelvin–Planck
-/

namespace MState

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-- The entropy is additive on product states. -/
lemma Sᵥₙ_prod_eq_add {d₁ d₂ : Type*} [Fintype d₁] [DecidableEq d₁] [Nonempty d₁]
    [Fintype d₂] [DecidableEq d₂] [Nonempty d₂] (ρ : MState d₁) (σ : MState d₂) :
    Sᵥₙ (ρ ⊗ᴹ σ) = Sᵥₙ ρ + Sᵥₙ σ := by
  have hI : qMutualInfo (ρ ⊗ᴹ σ) = 0 := by
    have h := qMutualInfo_as_qRelativeEnt (ρ ⊗ᴹ σ)
    simpa using h
  rw [qMutualInfo] at hI
  simpa [add_comm] using (eq_add_of_sub_eq hI).symm

/-- **Kelvin–Planck.** The thermal state is passive: no unitary lowers its expected energy, so
no work is extracted from a single reservoir. -/
lemma exp_val_thermalBetaReal_le_uConj {β : ℝ} (hβ : 0 < β) (H : HermitianMat d ℂ)
    (U : 𝐔[d]) :
    (thermalBetaReal H β).exp_val H ≤ ((thermalBetaReal H β).uConj U).exp_val H := by
  have h := gibbsRelativeEntropyBalanceBetaReal ((thermalBetaReal H β).uConj U) H β
  have hS : Sᵥₙ ((thermalBetaReal H β).uConj U) = Sᵥₙ (thermalBetaReal H β) := by
    simp [Sᵥₙ]
  have hD : 0 ≤ (qRelativeEnt ((thermalBetaReal H β).uConj U) (thermalBetaReal H β)).toReal :=
    ENNReal.toReal_nonneg
  rw [hS] at h
  nlinarith

end MState

/-!
## B. The Carnot bound
-/

namespace QuantumThermodynamics

variable {dH dC : Type*} [Fintype dH] [DecidableEq dH] [Nonempty dH]
  [Fintype dC] [DecidableEq dC] [Nonempty dC]

/-- The state of two reservoirs, starting in their thermal states, after a joint unitary. -/
def carnotFinal (βh βc : ℝ) (Hh : HermitianMat dH ℂ) (Hc : HermitianMat dC ℂ)
    (U : 𝐔[dH × dC]) : MState (dH × dC) :=
  (MState.thermalBetaReal Hh βh ⊗ᴹ MState.thermalBetaReal Hc βc).uConj U

/-- The heat taken from the hot reservoir. -/
def heatHot (βh βc : ℝ) (Hh : HermitianMat dH ℂ) (Hc : HermitianMat dC ℂ)
    (U : 𝐔[dH × dC]) : ℝ :=
  (MState.thermalBetaReal Hh βh).exp_val Hh - (carnotFinal βh βc Hh Hc U).traceRight.exp_val Hh

/-- The heat given to the cold reservoir. -/
def heatCold (βh βc : ℝ) (Hh : HermitianMat dH ℂ) (Hc : HermitianMat dC ℂ)
    (U : 𝐔[dH × dC]) : ℝ :=
  (carnotFinal βh βc Hh Hc U).traceLeft.exp_val Hc - (MState.thermalBetaReal Hc βc).exp_val Hc

/-- The entropy balance of the two reservoirs: `β_h Q_h ≤ β_c Q_c`. -/
lemma carnot_entropy (βh βc : ℝ) (Hh : HermitianMat dH ℂ) (Hc : HermitianMat dC ℂ)
    (U : 𝐔[dH × dC]) :
    βh * heatHot βh βc Hh Hc U ≤ βc * heatCold βh βc Hh Hc U := by
  have hS : Sᵥₙ (carnotFinal βh βc Hh Hc U) =
      Sᵥₙ (MState.thermalBetaReal Hh βh) + Sᵥₙ (MState.thermalBetaReal Hc βc) := by
    have hU : Sᵥₙ (carnotFinal βh βc Hh Hc U) =
        Sᵥₙ (MState.thermalBetaReal Hh βh ⊗ᴹ MState.thermalBetaReal Hc βc) := by
      simp [carnotFinal, Sᵥₙ]
    rw [hU, MState.Sᵥₙ_prod_eq_add]
  have hsub := Sᵥₙ_subadditivity (carnotFinal βh βc Hh Hc U)
  have hh := MState.gibbsRelativeEntropyBalanceBetaReal
    (carnotFinal βh βc Hh Hc U).traceRight Hh βh
  have hc := MState.gibbsRelativeEntropyBalanceBetaReal
    (carnotFinal βh βc Hh Hc U).traceLeft Hc βc
  have hDh : 0 ≤ (qRelativeEnt (carnotFinal βh βc Hh Hc U).traceRight
      (MState.thermalBetaReal Hh βh)).toReal := ENNReal.toReal_nonneg
  have hDc : 0 ≤ (qRelativeEnt (carnotFinal βh βc Hh Hc U).traceLeft
      (MState.thermalBetaReal Hc βc)).toReal := ENNReal.toReal_nonneg
  rw [heatHot, heatCold]
  nlinarith

/-- **The Carnot bound.** The work `W = Q_h - Q_c` is at most `(1 - β_h / β_c) Q_h`. -/
lemma carnot {βh βc : ℝ} (hβc : 0 < βc) (Hh : HermitianMat dH ℂ) (Hc : HermitianMat dC ℂ)
    (U : 𝐔[dH × dC]) :
    heatHot βh βc Hh Hc U - heatCold βh βc Hh Hc U ≤
      (1 - βh / βc) * heatHot βh βc Hh Hc U := by
  have h := carnot_entropy βh βc Hh Hc U
  have h' : βh / βc * heatHot βh βc Hh Hc U ≤ heatCold βh βc Hh Hc U := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hβc]
    linarith
  linarith

end QuantumThermodynamics
