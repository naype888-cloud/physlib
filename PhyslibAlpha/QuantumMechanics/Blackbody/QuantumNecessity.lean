/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Probability.Moments.MGFAnalytic
public import PhyslibAlpha.QuantumMechanics.Blackbody.RayleighJeans
/-!

# Planck's law forces discrete energy levels

## i. Overview

Poincaré's 1912 theorem. Let `𝓒` be a canonical ensemble whose Boltzmann factors are
integrable at every positive temperature. If its mean energy is Planck's `ε / (e^{β ε} - 1)`
at every positive temperature, then its density of states, the image of `𝓒.μ` under the
energy, is a positive multiple of the levels `∑ₙ δ_{n ε}`. No continuous component survives:
the quantum is necessary.

The mean energy is `-∂_β log Z`, so the law makes `Z(β) (1 - e^{-β ε})` constant: the
partition function is that of the levels. Laplace transforms on `β > 0` separate such
weights: after tilting by `e^{-E}` both measures are finite, their complex moment generating
functions agree on the half-plane `Re z < 1` by analytic continuation, and hence so do their
characteristic functions.

## ii. Key results

- `levels` : the density of states `∑ₙ δ_{n ε}` of the quantized oscillator.
- `eq_of_laplace` : the Laplace transform on `β > 0` determines the weight.
- `partition_eq_of_planck` : Planck's mean energy fixes `Z(β)` up to a scalar.
- `planck_forces_levels` : Planck's mean energy forces `μ = c • levels ε`.
- `CanonicalEnsemble.map_energy_eq_levels_of_planck` : the same for a canonical ensemble.

## iii. Table of contents

- A. Tilting
- B. The Laplace transform determines the weight
- C. The levels
- D. Planck's law forces the levels
- E. Canonical ensembles

## iv. References

* H. Poincaré, *Sur la théorie des quanta*, J. Phys. Théor. Appl. 2 (1912) 5–34.

-/

@[expose] public section

namespace BlackBody

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal

variable {μ ν : Measure ℝ} {ε : ℝ}

/-- The weight `μ` has a Laplace transform at every `β > 0`. -/
def HasLaplace (μ : Measure ℝ) : Prop := ∀ β > 0, Integrable (fun E => exp (-β * E)) μ

/-- The levels of spacing `ε`: unit mass at every `n ε`. -/
noncomputable def levels (ε : ℝ) : Measure ℝ :=
  Measure.sum fun n : ℕ => Measure.dirac ((n : ℝ) * ε)

/-!

## A. Tilting

-/

/-- The tilt `e^{-E} μ`, a finite measure when `μ` has a Laplace transform. -/
noncomputable def expTilt (μ : Measure ℝ) : Measure ℝ :=
  μ.withDensity fun E => ((exp (-E)).toNNReal : ℝ≥0∞)

lemma expTilt_smul (t E : ℝ) :
    (exp (-E)).toNNReal • exp (t * E) = exp (-(1 - t) * E) := by
  rw [NNReal.smul_def, coe_toNNReal _ (exp_pos _).le, smul_eq_mul, ← exp_add]
  ring_nf

lemma integrable_expTilt (hμ : HasLaplace μ) {t : ℝ} (ht : t < 1) :
    Integrable (fun E => exp (t * id E)) (expTilt μ) := by
  rw [expTilt, integrable_withDensity_iff_integrable_smul (by fun_prop)]
  simpa only [id, expTilt_smul] using hμ _ (by linarith)

lemma mgf_expTilt (t : ℝ) : mgf id (expTilt μ) t = ∫ E, exp (-(1 - t) * E) ∂μ := by
  rw [mgf, expTilt, integral_withDensity_eq_integral_smul (by fun_prop)]
  simp only [id, expTilt_smul]

lemma isFiniteMeasure_expTilt (hμ : HasLaplace μ) : IsFiniteMeasure (expTilt μ) := by
  have h := (hμ 1 one_pos).hasFiniteIntegral
  simp only [neg_mul, one_mul] at h
  exact isFiniteMeasure_withDensity_ofReal h

lemma withDensity_expTilt (μ : Measure ℝ) :
    (expTilt μ).withDensity (fun E => ((exp E).toNNReal : ℝ≥0∞)) = μ := by
  have h : ((fun E : ℝ => ((exp (-E)).toNNReal : ℝ≥0∞)) * fun E => ((exp E).toNNReal : ℝ≥0∞))
      = 1 := by
    funext E
    simp [← ENNReal.coe_mul, ← toNNReal_mul (exp_pos _).le, ← exp_add]
  rw [expTilt, ← withDensity_mul _ (by fun_prop) (by fun_prop), h, withDensity_one]

/-!

## B. The Laplace transform determines the weight

-/

lemma half_plane_subset (hμ : HasLaplace μ) :
    {z : ℂ | z.re < 1} ⊆ {z | z.re ∈ interior (integrableExpSet id (expTilt μ))} :=
  fun _ hz => interior_maximal (fun _ ht => integrable_expTilt hμ ht) isOpen_Iio hz

lemma tendsto_neg_inv_nat :
    Tendsto (fun n : ℕ => ((-(1 / ((n : ℝ) + 1)) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
  have h : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
  · simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp h
  · simpa using Nat.cast_add_one_ne_zero (R := ℂ) n

/-- Two weights with the same Laplace transform on `β > 0` coincide. -/
theorem eq_of_laplace (hμ : HasLaplace μ) (hν : HasLaplace ν)
    (h : ∀ β > 0, ∫ E, exp (-β * E) ∂μ = ∫ E, exp (-β * E) ∂ν) : μ = ν := by
  have := isFiniteMeasure_expTilt hμ
  have := isFiniteMeasure_expTilt hν
  have hreal (t : ℝ) (ht : t < 1) :
      complexMGF id (expTilt μ) t = complexMGF id (expTilt ν) t := by
    rw [complexMGF_ofReal, complexMGF_ofReal, mgf_expTilt, mgf_expTilt, h _ (by linarith)]
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ),
      complexMGF id (expTilt μ) z = complexMGF id (expTilt ν) z :=
    tendsto_neg_inv_nat.frequently <| Frequently.of_forall fun n => hreal _ <| by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    (analyticOnNhd_complexMGF.mono (half_plane_subset hμ))
    (analyticOnNhd_complexMGF.mono (half_plane_subset hν))
    (convex_halfSpace_re_lt 1).isPreconnected (by simp) hfreq
  have ht : expTilt μ = expTilt ν := Measure.ext_of_charFun <| funext fun t => by
    rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
    exact heq (by simp)
  rw [← withDensity_expTilt μ, ← withDensity_expTilt ν, ht]

/-!

## C. The levels

-/

lemma one_sub_exp_neg_pos {β : ℝ} (hβ : 0 < β) (hε : 0 < ε) : 0 < 1 - exp (-(β * ε)) :=
  sub_pos.mpr (exp_lt_one_iff.mpr (neg_lt_zero.mpr (mul_pos hβ hε)))

lemma lintegral_levels (hε : 0 < ε) {β : ℝ} (hβ : 0 < β) :
    ∫⁻ E, ENNReal.ofReal (exp (-β * E)) ∂levels ε =
      ENNReal.ofReal (1 - exp (-(β * ε)))⁻¹ := by
  have hs := hasSum_exp_neg_levels (mul_pos hβ hε)
  rw [levels, lintegral_sum_measure]
  simp only [lintegral_dirac]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => (exp_pos _).le) hs.summable, hs.tsum_eq]

lemma hasLaplace_levels (hε : 0 < ε) : HasLaplace (levels ε) := fun β hβ =>
  ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => (exp_pos _).le)).mpr
    (by rw [lintegral_levels hε hβ]; exact ENNReal.ofReal_lt_top)⟩

lemma integral_levels (hε : 0 < ε) {β : ℝ} (hβ : 0 < β) :
    ∫ E, exp (-β * E) ∂levels ε = (1 - exp (-(β * ε)))⁻¹ := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => (exp_pos _).le)
    (by fun_prop), lintegral_levels hε hβ,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (one_sub_exp_neg_pos hβ hε).le)]

/-!

## D. Planck's law forces the levels

-/

lemma hasDerivAt_partition (hμ : HasLaplace μ) {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (fun b => ∫ E, exp (-b * E) ∂μ) (-∫ E, E * exp (-β * E) ∂μ) β := by
  have hsub : Set.Iio (0 : ℝ) ⊆ integrableExpSet id μ := fun t (ht : t < 0) => by
    simpa [integrableExpSet] using hμ (-t) (by linarith)
  have hint := interior_maximal hsub isOpen_Iio (neg_lt_zero.mpr hβ)
  simpa [mgf, Function.comp_def] using (hasDerivAt_mgf hint).comp β (hasDerivAt_neg β)

/-- Planck's mean energy makes `Z(β) (1 - e^{-β ε})` constant on `β > 0`. -/
theorem partition_eq_of_planck (hε : 0 < ε) (hμ : HasLaplace μ)
    (hU : ∀ β > 0, (∫ E, E * exp (-β * E) ∂μ) / (∫ E, exp (-β * E) ∂μ)
      = ε / (exp (β * ε) - 1)) :
    ∃ c, ∀ β > 0, ∫ E, exp (-β * E) ∂μ = c * (1 - exp (-(β * ε)))⁻¹ := by
  have hd {β : ℝ} (hβ : 0 < β) : 0 < exp (β * ε) - 1 :=
    sub_pos.mpr (one_lt_exp_iff.mpr (mul_pos hβ hε))
  have hZ {β : ℝ} (hβ : 0 < β) : ∫ E, exp (-β * E) ∂μ ≠ 0 := fun h0 => by
    have := hU β hβ
    rw [h0, div_zero] at this
    exact (div_pos hε (hd hβ)).ne this
  have hf {β : ℝ} (hβ : 0 < β) :
      HasDerivAt (fun b => (∫ E, exp (-b * E) ∂μ) * (1 - exp (-(b * ε)))) 0 β := by
    convert (hasDerivAt_partition hμ hβ).mul
      (((hasDerivAt_id β).mul_const ε).neg.exp.const_sub 1) using 1
    · rfl
    rw [← div_mul_cancel₀ (∫ E, E * exp (-β * E) ∂μ) (hZ hβ), hU β hβ]
    simp only [Pi.neg_apply, id, exp_neg]
    have hx := (hd hβ).ne'
    have hx0 := (exp_pos (β * ε)).ne'
    generalize exp (β * ε) = x at hx hx0 ⊢
    field_simp
    ring
  obtain ⟨c, hc⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi
    (fun b hb => (hf hb).differentiableAt.differentiableWithinAt) (fun b hb => (hf hb).deriv)
  exact ⟨c, fun β hβ => by
    rw [← hc β hβ, mul_inv_cancel_right₀ (one_sub_exp_neg_pos hβ hε).ne']⟩

/-- **Poincaré (1912).** A weight whose Gibbs mean energy is Planck's `ε / (e^{β ε} - 1)` at
every `β > 0` is a positive multiple of the levels `∑ₙ δ_{n ε}`. -/
theorem planck_forces_levels (hε : 0 < ε) (hμ : HasLaplace μ)
    (hU : ∀ β > 0, (∫ E, E * exp (-β * E) ∂μ) / (∫ E, exp (-β * E) ∂μ)
      = ε / (exp (β * ε) - 1)) :
    ∃ c : ℝ≥0, 0 < c ∧ μ = (c : ℝ≥0∞) • levels ε := by
  obtain ⟨c, hc⟩ := partition_eq_of_planck hε hμ hU
  have hq := one_sub_exp_neg_pos one_pos hε
  have hc0 : 0 ≤ c := by
    have hZ1 : 0 ≤ ∫ E, exp (-1 * E) ∂μ := integral_nonneg fun _ => (exp_pos _).le
    rw [hc 1 one_pos] at hZ1
    exact nonneg_of_mul_nonneg_left hZ1 (inv_pos.mpr hq)
  refine ⟨c.toNNReal, ?_, eq_of_laplace hμ
    (fun β hβ => (hasLaplace_levels hε β hβ).smul_measure ENNReal.coe_ne_top) fun β hβ => ?_⟩
  · refine toNNReal_pos.mpr (lt_of_le_of_ne hc0 fun h => ?_)
    have := hU 1 one_pos
    rw [hc 1 one_pos, ← h, zero_mul, div_zero] at this
    exact (div_pos hε (sub_pos.mpr (one_lt_exp_iff.mpr (by simpa using hε)))).ne this
  · rw [integral_smul_measure, integral_levels hε hβ, hc β hβ]
    simp [coe_toNNReal _ hc0]

/-!

## E. Canonical ensembles

-/

open Constants Temperature in
/-- **Poincaré (1912) for canonical ensembles.** If the Boltzmann factors of `𝓒` are
integrable and its mean energy is Planck's `ε / (e^{β ε} - 1)` at every positive temperature,
then its density of states is a positive multiple of the levels `∑ₙ δ_{n ε}`. -/
theorem _root_.CanonicalEnsemble.map_energy_eq_levels_of_planck {ι : Type}
    [MeasurableSpace ι] (𝓒 : CanonicalEnsemble ι) (hε : 0 < ε)
    (hI : ∀ T : Temperature, 0 < (T : ℝ) →
      Integrable (fun i => exp (-T.β * 𝓒.energy i)) 𝓒.μ)
    (hU : ∀ T : Temperature, 0 < (T : ℝ) → 𝓒.meanEnergy T = ε / (exp (T.β * ε) - 1)) :
    ∃ c : ℝ≥0, 0 < c ∧ 𝓒.μ.map 𝓒.energy = (c : ℝ≥0∞) • levels ε := by
  have hm : AEMeasurable 𝓒.energy 𝓒.μ := 𝓒.energy_measurable.aemeasurable
  have hT {β : ℝ} (hβ : 0 < β) : 0 < ((ofβ β.toNNReal : Temperature) : ℝ) := by
    rw [ofβ_toReal, coe_toNNReal _ hβ.le]
    exact one_div_pos.mpr (mul_pos kB_pos hβ)
  have hβ' {β : ℝ} (hβ : 0 < β) : ((ofβ β.toNNReal).β : ℝ) = β := by
    rw [β_ofβ, coe_toNNReal _ hβ.le]
  have hmap {f : ℝ → ℝ} (hf : Continuous f) :
      ∫ E, f E ∂𝓒.μ.map 𝓒.energy = ∫ i, f (𝓒.energy i) ∂𝓒.μ :=
    integral_map hm hf.aestronglyMeasurable
  refine planck_forces_levels hε (fun β hβ => ?_) fun β hβ => ?_
  · have h := hI _ (hT hβ)
    rw [hβ' hβ] at h
    rw [integrable_map_measure (by fun_prop) hm]
    exact h
  · have h := hU _ (hT hβ)
    rw [CanonicalEnsemble.meanEnergy_eq_ratio_of_integrals, hβ' hβ] at h
    rw [hmap (by fun_prop), hmap (by fun_prop)]
    exact h

end BlackBody
