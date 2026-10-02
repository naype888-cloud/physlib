/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import QuantumInfo.Entropy.Relative
public import QuantumInfo.Entropy.SSA
public import Physlib.Thermodynamics.Temperature.Basic
/-!

# Landauer's principle for a finite system and a thermal reservoir

## i. Overview

A reservoir with Hamiltonian `H` at inverse temperature `β` starts in its Gibbs state
`γ = exp (-β H) / Z`. A system in the state `ρ` interacts with it through a unitary `U` on the pair,
which ends in the joint state `ρ' = U (ρ ⊗ γ) U†`. Landauer's
principle says that lowering the entropy of the system costs heat in the reservoir:

`S(ρ) - S(ρ'_S) ≤ β (⟨H⟩_{ρ'_R} - ⟨H⟩_γ)`.

At temperature `T`, with `β = 1 / (k_B T)`, the heat released into the reservoir is at least
`k_B T (S(ρ) - S(ρ'_S))`; erasing one bit, `S(ρ) - S(ρ'_S) = log 2`, costs at least
`k_B T log 2`.

The entropy of `ρ'` is that of `ρ ⊗ γ`, the sum of the two entropies, since unitary
evolution keeps the spectrum. The rest uses two facts: subadditivity of the von Neumann
entropy, and Klein's inequality `0 ≤ ⟪σ, log σ - log γ⟫`, which for the Gibbs state reads
`S(σ) ≤ β ⟨H⟩_σ + log Z`: the Gibbs state maximizes the entropy at fixed mean energy.

## ii. Key results

- `partitionFunction` : the partition function `Z = tr exp (-β H)`, positive.
- `gibbsState` : the Gibbs state `exp (-β H) / Z`.
- `HermitianMat.log_exp` : `log (exp A) = A`.
- `log_gibbsState` : `log γ = -β H - log Z`.
- `Sᵥₙ_gibbsState` : `S(γ) = β ⟨H⟩_γ + log Z`.
- `Sᵥₙ_le_gibbs` : `S(σ) ≤ β ⟨H⟩_σ + log Z` for every state `σ`.
- `Sᵥₙ_prod` : `S(ρ ⊗ σ) = S(ρ) + S(σ)`.
- `Sᵥₙ_uConj` : `S(U ρ U†) = S(ρ)`.
- `landauer` : Landauer's principle for a unitary interaction.
- `landauer_temperature` : the heat is at least `k_B T` times the entropy lost.
- `landauer_bit` : erasing one bit costs at least `k_B T log 2`.

## iii. Table of contents

- A. The Gibbs state
- B. The Gibbs state maximizes the entropy
- C. Entropy of a product and of a unitary evolution
- D. Landauer's principle
- E. Landauer's principle at a temperature

## iv. References

* R. Landauer, *Irreversibility and heat generation in the computing process*,
  IBM J. Res. Dev. 5 (1961).
* D. Reeb, M. M. Wolf, *An improved Landauer principle with finite-size corrections*,
  New J. Phys. 16 (2014).
-/

@[expose] public section

noncomputable section

namespace MState

open scoped InnerProductSpace RealInnerProductSpace
open HermitianMat

variable {d dS dR : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
  [Fintype dS] [DecidableEq dS] [Fintype dR] [DecidableEq dR] [Nonempty dR]

/-!

## A. The Gibbs state

-/

/-- The partition function `Z = tr exp (-β H)` of a Hamiltonian `H` at inverse temperature `β`. -/
def partitionFunction (β : ℝ) (H : HermitianMat d ℂ) : ℝ :=
  ((-β) • H).exp.trace

lemma partitionFunction_pos (β : ℝ) (H : HermitianMat d ℂ) : 0 < partitionFunction β H :=
  trace_pos (exp_pos _)

/-- The Gibbs state `exp (-β H) / Z` of a Hamiltonian `H` at inverse temperature `β`. -/
def gibbsState (β : ℝ) (H : HermitianMat d ℂ) : MState d where
  M := (partitionFunction β H)⁻¹ • ((-β) • H).exp
  nonneg := smul_nonneg (inv_nonneg.2 (partitionFunction_pos β H).le) (exp_nonneg _)
  tr := by
    rw [trace_smul]
    exact inv_mul_cancel₀ (partitionFunction_pos β H).ne'

omit [Nonempty d] in
/-- The logarithm undoes the exponential of a Hermitian matrix. -/
lemma _root_.HermitianMat.log_exp (A : HermitianMat d ℂ) : A.exp.log = A := by
  rw [exp, log, ← HermitianMat.cfc_comp]
  convert HermitianMat.cfc_id (A := A) using 2
  funext x
  simp

lemma log_gibbsState (β : ℝ) (H : HermitianMat d ℂ) :
    (gibbsState β H).M.log = (-Real.log (partitionFunction β H)) • 1 + (-β) • H := by
  rw [gibbsState, log_smul (inv_ne_zero (partitionFunction_pos β H).ne'), Real.log_inv,
    log_exp]

/-- Against any state `σ`, `⟪σ, log γ⟫ = -β ⟨H⟩_σ - log Z`. -/
lemma inner_log_gibbsState (σ : MState d) (β : ℝ) (H : HermitianMat d ℂ) :
    ⟪σ.M, (gibbsState β H).M.log⟫ = -β * ⟪σ.M, H⟫ - Real.log (partitionFunction β H) := by
  rw [log_gibbsState, HermitianMat.inner_add_right, HermitianMat.inner_smul_right,
    HermitianMat.inner_smul_right, inner_one, σ.tr]
  ring

lemma Sᵥₙ_gibbsState (β : ℝ) (H : HermitianMat d ℂ) :
    Sᵥₙ (gibbsState β H) =
      β * ⟪(gibbsState β H).M, H⟫ + Real.log (partitionFunction β H) := by
  rw [Sᵥₙ_eq_neg_trace_log, real_inner_comm, inner_log_gibbsState]
  ring

/-!

## B. The Gibbs state maximizes the entropy

-/

/-- Klein's inequality against the Gibbs state: `S(σ) ≤ β ⟨H⟩_σ + log Z`. -/
theorem Sᵥₙ_le_gibbs (σ : MState d) (β : ℝ) (H : HermitianMat d ℂ) :
    Sᵥₙ σ ≤ β * ⟪σ.M, H⟫ + Real.log (partitionFunction β H) := by
  have hker : (gibbsState β H).M.ker ≤ σ.M.ker := by
    have : NonSingular (gibbsState β H).M :=
      nonSingular_smul (inv_ne_zero (partitionFunction_pos β H).ne').isUnit
    rw [nonSingular_ker_bot]
    exact bot_le
  have hK := inner_log_sub_log_nonneg hker
  rw [inner_sub_right, inner_log_gibbsState] at hK
  rw [Sᵥₙ_eq_neg_trace_log, real_inner_comm]
  linarith

/-!

## C. Entropy of a product and of a unitary evolution

-/

omit [Nonempty dR] in
/-- The entropy of a product state is the sum of the entropies of its factors. -/
theorem Sᵥₙ_prod (ρ : MState dS) (σ : MState dR) : Sᵥₙ (ρ ⊗ᴹ σ) = Sᵥₙ ρ + Sᵥₙ σ := by
  obtain ⟨e, he⟩ := spectrum_prod ρ σ
  simp only [Sᵥₙ, Hₛ, H₁]
  rw [← e.sum_comp, Fintype.sum_prod_type]
  simp only [ProbDistribution.prob, he, Prob.coe_mul, Real.negMulLog_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [σ.spectrum.normalized, ρ.spectrum.normalized, one_mul, one_mul]

omit [Nonempty d] in
/-- A unitary evolution does not change the entropy. -/
@[simp]
theorem Sᵥₙ_uConj (ρ : MState d) (U : 𝐔[d]) : Sᵥₙ (ρ.uConj U) = Sᵥₙ ρ := by
  simp [Sᵥₙ]

/-!

## D. Landauer's principle

-/

/-- Landauer's inequality for any final state `ρ'` with the entropy of `ρ ⊗ γ`. -/
theorem landauer_of_Sᵥₙ_eq (ρ : MState dS) (β : ℝ) (H : HermitianMat dR ℂ)
    (ρ' : MState (dS × dR)) (hS : Sᵥₙ ρ' = Sᵥₙ ρ + Sᵥₙ (gibbsState β H)) :
    Sᵥₙ ρ - Sᵥₙ ρ'.traceRight ≤
      β * (⟪ρ'.traceLeft.M, H⟫ - ⟪(gibbsState β H).M, H⟫) := by
  have hsub := Sᵥₙ_subadditivity ρ'
  have hK := Sᵥₙ_le_gibbs ρ'.traceLeft β H
  rw [Sᵥₙ_gibbsState] at hS
  nlinarith

/-- **Landauer's principle.** The system starts in `ρ`, the reservoir in the Gibbs state `γ` of
`H` at inverse temperature `β`, and the pair evolves by a unitary `U`. Lowering the entropy of the
system costs heat in the reservoir: `S(ρ) - S(ρ'_S) ≤ β (⟨H⟩_{ρ'_R} - ⟨H⟩_γ)`,
with `ρ' = U (ρ ⊗ γ) U†`. -/
theorem landauer (ρ : MState dS) (β : ℝ) (H : HermitianMat dR ℂ) (U : 𝐔[dS × dR]) :
    Sᵥₙ ρ - Sᵥₙ ((ρ ⊗ᴹ gibbsState β H).uConj U).traceRight ≤
      β * (⟪((ρ ⊗ᴹ gibbsState β H).uConj U).traceLeft.M, H⟫ - ⟪(gibbsState β H).M, H⟫) :=
  landauer_of_Sᵥₙ_eq ρ β H _ (by rw [Sᵥₙ_uConj, Sᵥₙ_prod])

/-!

## E. Landauer's principle at a temperature

-/

open Constants

/-- The thermal state of `H` at temperature `T`, the Gibbs state at `β = 1 / (k_B T)`. -/
def thermalState (T : Temperature) (H : HermitianMat dR ℂ) : MState dR :=
  gibbsState T.β H

/-- **Landauer's principle at temperature `T`.** The heat released into the reservoir is at
least `k_B T` times the entropy lost by the system. -/
theorem landauer_temperature (ρ : MState dS) (T : Temperature) (hT : 0 < T.val)
    (H : HermitianMat dR ℂ) (U : 𝐔[dS × dR]) :
    kB * T * (Sᵥₙ ρ - Sᵥₙ ((ρ ⊗ᴹ thermalState T H).uConj U).traceRight) ≤
      ⟪((ρ ⊗ᴹ thermalState T H).uConj U).traceLeft.M, H⟫ - ⟪(thermalState T H).M, H⟫ := by
  have hkT : 0 < kB * (T : ℝ) := mul_pos kB_pos (by exact_mod_cast hT)
  have h := landauer ρ T.β H U
  rw [Temperature.β_toReal] at h
  rw [thermalState]
  calc kB * T * (Sᵥₙ ρ - Sᵥₙ ((ρ ⊗ᴹ gibbsState T.β H).uConj U).traceRight)
      ≤ kB * T * (1 / (kB * T) * (⟪((ρ ⊗ᴹ gibbsState T.β H).uConj U).traceLeft.M, H⟫ -
          ⟪(gibbsState T.β H).M, H⟫)) := mul_le_mul_of_nonneg_left h hkT.le
    _ = _ := by rw [← mul_assoc, mul_one_div_cancel hkT.ne', one_mul]

/-- **Erasing one bit.** If the system loses `log 2` of entropy, the reservoir receives at least
`k_B T log 2` of heat. -/
theorem landauer_bit (ρ : MState dS) (T : Temperature) (hT : 0 < T.val)
    (H : HermitianMat dR ℂ) (U : 𝐔[dS × dR])
    (hbit : Sᵥₙ ρ - Sᵥₙ ((ρ ⊗ᴹ thermalState T H).uConj U).traceRight = Real.log 2) :
    kB * T * Real.log 2 ≤
      ⟪((ρ ⊗ᴹ thermalState T H).uConj U).traceLeft.M, H⟫ - ⟪(thermalState T H).M, H⟫ :=
  hbit ▸ landauer_temperature ρ T hT H U

end MState
