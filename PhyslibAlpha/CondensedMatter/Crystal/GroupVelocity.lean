/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Inversion
public import PhyslibAlpha.CondensedMatter.Crystal.Folner
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!

# The energy–position bracket of a plane wave and the group velocity

In a plane wave on a finite region of a lattice with one site per cell, the expectation of the
bracket of the hopping Hamiltonian and a position is a sum over the bonds inside the region. On
the cubes of `ℤ^d` it tends to `-1/2` times the group velocity of the band.

## i. Overview

Let `ψ(n) = exp (i k n) / √|Λ|` be a plane wave of momentum `k` on a region `Λ`, `H` the hopping
with amplitude `-t` along the bonds and `X` the position along `r`. The bracket
`⁅H, X⁆ = -(i/2) (H X - X H)` has the matrix elements `-(i/2) H_nm (r m - r n)`, so

  `⟨⁅H, X⁆⟩ = -(t / (2 |Λ|)) ∑_{n, m ∈ Λ bonded} r (m - n) sin (k (m - n))`.

The sum counts, for each bond vector `δ`, the sites `n` of `Λ` with `n + δ ∈ Λ`. On the cube
`{0, …, N}^d` their fraction tends to one, by the Følner property of the cubes, so the bracket
tends to `-(t / 2) ∑_δ r δ sin (k δ)`. This is `-1/2` times the derivative along `r` of the band
`ε(k) = -t ∑_δ cos (k δ)`, the group velocity: the spectrum of the hopping fixes the entry `Ω_HX`
that the inversion and time reversal leave, while they force `Σ_HX = 0`.

## ii. Key results

- `expectation_bracket_unitPlaneWave` : the bracket in a plane wave on a finite region.
- `band`, `hasDerivAt_band` : the band and its group velocity along `r`.
- `tendsto_expectation_bracket_box` : on the cubes the bracket tends to `-1/2` times the group
  velocity.

## iii. Table of contents

- A. The bracket in a plane wave
- B. The band and its group velocity
- C. The limit of large cubes

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 8.

-/

@[expose] public section

namespace CondensedMatter.Crystal

open ProbabilisticTheory Filter Topology
open scoped ComplexOrder InnerProductSpace selfAdjoint

attribute [local instance] PeriodicGraph.decidableAdj

variable {G : Type*} [AddCommGroup G] [DecidableEq G]
  (g : PeriodicGraph (Crystal.ofUnitCell G Unit))

/-! ## A. The bracket in a plane wave -/

/-- **The energy–position bracket of a plane wave** on a finite region: a sum over the bonds
inside the region. -/
lemma expectation_bracket_unitPlaneWave {Λ : Finset G} (hne : Λ.Nonempty) (t : ℝ)
    (k r : G →+ ℝ) :
    UnitalPositiveLinearMap.expectation
      (UnitalPositiveLinearMap.ofVec (norm_unitPlaneWave hne k))
      ⁅hoppingObservable (Λ := Λ) g t, positionObservable r⁆ =
      -(t / (2 * Λ.card)) * ∑ n : Λ, ∑ m : Λ,
        if g.toSimpleGraph.Adj ⟨(n : G), ()⟩ ⟨(m : G), ()⟩ then
          r ((m : G) - n) * Real.sin (k ((m : G) - n)) else 0 := by
  rw [← Complex.ofReal_re (UnitalPositiveLinearMap.expectation _ _),
    ← UnitalPositiveLinearMap.apply_observable_eq_expectation, UnitalPositiveLinearMap.ofVec_apply,
    selfAdjoint.coe_bracket]
  change (⟪unitPlaneWave Λ k, ((-(Complex.I / 2)) •
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ) (hoppingMatrix g t) *
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ) (positionMatrix r) -
     Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ) (positionMatrix r) *
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ) (hoppingMatrix g t))) (unitPlaneWave Λ k)⟫_ℂ).re = _
  rw [← map_mul, ← map_mul, ← map_sub, ← map_smul, PiLp.inner_apply, Complex.re_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [RCLike.inner_apply, Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct, Finset.sum_mul,
    Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro m _
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    positionMatrix, hoppingMatrix, unitPlaneWave, planeWave, PiLp.smul_apply, smul_eq_mul]
  have ha : (√(Λ.card : ℝ))⁻¹ * (√(Λ.card : ℝ))⁻¹ = ((Λ.card : ℝ))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have e (x : ℝ) : Complex.exp (x * Complex.I) = Real.cos x + Real.sin x * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  split_ifs with hadj
  · simp only [Complex.real_smul, e, map_mul, map_add, Complex.conj_ofReal, Complex.conj_I,
      map_sub, Real.sin_sub]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.div_ofNat_re, Complex.div_ofNat_im]
    rw [show t / (2 * Λ.card) = t / 2 * ((√(Λ.card : ℝ))⁻¹ * (√(Λ.card : ℝ))⁻¹) by
      rw [ha]; ring]
    ring
  · simp

/-! ## B. The band and its group velocity -/

/-- The bond vectors from a site: the cells of its neighbours. -/
noncomputable def bondVectors : Finset G := (g.neighbors ⟨0, ()⟩).image CellSite.cell

/-- The band of the hopping with amplitude `-t`: `ε(k) = -t ∑_δ cos (k δ)`. -/
noncomputable def band (t : ℝ) (k : G →+ ℝ) : ℝ := -t * ∑ δ ∈ bondVectors g, Real.cos (k δ)

/-- **The group velocity along `r`**: the derivative of the band along `r` is
`t ∑_δ r δ sin (k δ)`. -/
lemma hasDerivAt_band (t : ℝ) (k r : G →+ ℝ) :
    HasDerivAt (fun s : ℝ => band g t (k + s • r))
      (t * ∑ δ ∈ bondVectors g, r δ * Real.sin (k δ)) 0 := by
  have h : HasDerivAt (fun s : ℝ => -t * ∑ δ ∈ bondVectors g, Real.cos (k δ + s * r δ))
      (-t * ∑ δ ∈ bondVectors g, -Real.sin (k δ + 0 * r δ) * (1 * r δ)) 0 :=
    (HasDerivAt.fun_sum fun δ _ =>
      (((hasDerivAt_id' (0 : ℝ)).mul_const (r δ)).const_add (k δ)).cos).const_mul (-t)
  convert h using 1
  · ext s
    simp [band, AddMonoidHom.add_apply, smul_eq_mul]
  · simp only [zero_mul, add_zero, one_mul, neg_mul, Finset.sum_neg_distrib, mul_neg, neg_neg]
    simp_rw [mul_comm (Real.sin _)]

/-! ## C. The limit of large cubes -/

lemma box_succ_nonempty (d N : ℕ) : (box d (N + 1)).Nonempty :=
  ⟨0, Fintype.mem_piFinset.mpr fun _ => by simp⟩

lemma adj_iff_mem_bondVectors (n m : G) :
    g.toSimpleGraph.Adj ⟨n, ()⟩ ⟨m, ()⟩ ↔ m - n ∈ bondVectors g := by
  rw [PeriodicGraph.adj_iff_bonded, PeriodicGraph.Bonded, bondVectors, Finset.mem_image]
  constructor
  · exact fun h => ⟨⟨m - n, ()⟩, (g.mem_neighbors _ _).mpr h, rfl⟩
  · rintro ⟨⟨δ, u⟩, hδ, rfl⟩
    exact (g.mem_neighbors _ _).mp hδ

/-- The sum over the bonds inside a region, by bond vector: each `δ` counts the sites `n` of the
region with `n + δ` in the region. -/
lemma sum_adj_eq_sum_bondVectors (Λ : Finset G) (f : G → ℝ) :
    ∑ n : Λ, ∑ m : Λ, (if g.toSimpleGraph.Adj ⟨(n : G), ()⟩ ⟨(m : G), ()⟩ then
      f ((m : G) - n) else 0) =
      ∑ δ ∈ bondVectors g, f δ * (Λ.filter fun n => n + δ ∈ Λ).card := by
  rw [Finset.sum_coe_sort Λ (fun n => ∑ m : Λ, if g.toSimpleGraph.Adj ⟨n, ()⟩ ⟨(m : G), ()⟩
    then f ((m : G) - n) else 0)]
  calc ∑ n ∈ Λ, ∑ m : Λ, (if g.toSimpleGraph.Adj ⟨n, ()⟩ ⟨(m : G), ()⟩ then f ((m : G) - n)
        else 0)
      = ∑ n ∈ Λ, ∑ δ ∈ bondVectors g, ∑ m ∈ Λ, if m - n = δ then f δ else 0 := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.sum_coe_sort Λ (fun m => if g.toSimpleGraph.Adj ⟨n, ()⟩ ⟨m, ()⟩
          then f (m - n) else 0), Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_ite_eq]
        exact if_congr (adj_iff_mem_bondVectors g n m) rfl rfl
    _ = ∑ δ ∈ bondVectors g, ∑ n ∈ Λ, if n + δ ∈ Λ then f δ else 0 := by
        conv_lhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun n _ => ?_
        simp_rw [sub_eq_iff_eq_add']
        rw [Finset.sum_ite_eq']
    _ = _ := by
        refine Finset.sum_congr rfl fun δ _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **On large cubes the bracketof a plane wave tends to `-1/2` times the group velocity.** -/
lemma tendsto_expectation_bracket_box {d : ℕ} (g : PeriodicGraph (Crystal.ofUnitCell (Fin d → ℤ)
    Unit)) (t : ℝ) (k r : (Fin d → ℤ) →+ ℝ) :
    Tendsto (fun N : ℕ => UnitalPositiveLinearMap.expectation
      (UnitalPositiveLinearMap.ofVec (norm_unitPlaneWave (box_succ_nonempty d N) k))
      ⁅hoppingObservable (Λ := box d (N + 1)) g t, positionObservable r⁆) atTop
      (𝓝 (-(t / 2) * ∑ δ ∈ bondVectors g, r δ * Real.sin (k δ))) := by
  have hratio (δ : Fin d → ℤ) : Tendsto (fun N : ℕ =>
      (((box d (N + 1)).filter fun n => n + δ ∈ box d (N + 1)).card : ℝ) /
        ((N + 1 : ℕ) : ℝ) ^ d) atTop (𝓝 1) := by
    have hfilter (N : ℕ) : (box d (N + 1)).filter (fun n => n + δ ∈ box d (N + 1)) =
        box d (N + 1) ∩ (box d (N + 1)).image (· + -δ) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_image]
      exact and_congr_right fun _ => ⟨fun h => ⟨n + δ, h, by abel⟩,
        fun ⟨b, hb, hbn⟩ => by rw [← hbn]; simpa using hb⟩
    have hsplit (N : ℕ) : (((box d (N + 1)).filter fun n => n + δ ∈ box d (N + 1)).card : ℝ) /
        ((N + 1 : ℕ) : ℝ) ^ d = 1 - ((box d (N + 1) \ (box d (N + 1)).image (· + -δ)).card : ℝ) /
          ((N + 1 : ℕ) : ℝ) ^ d := by
      have h := Finset.card_sdiff_add_card_inter (box d (N + 1)) ((box d (N + 1)).image (· + -δ))
      rw [card_box] at h
      have hpos : ((N + 1 : ℕ) : ℝ) ^ d ≠ 0 := pow_ne_zero _ (by positivity)
      rw [hfilter, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hpos]
      exact_mod_cast (add_comm _ _).trans h
    simp_rw [hsplit]
    have h0 := tendsto_box_sdiff d (-δ)
    have hsq : Tendsto (fun N : ℕ => ((box d (N + 1) \ (box d (N + 1)).image (· + -δ)).card : ℝ) /
        ((N + 1 : ℕ) : ℝ) ^ d) atTop (𝓝 0) :=
      squeeze_zero (fun N => by positivity) (fun N => div_le_div_of_nonneg_right
        (le_add_of_nonneg_left (Nat.cast_nonneg _)) (by positivity)) h0
    simpa using hsq.const_sub 1
  have heq (N : ℕ) : UnitalPositiveLinearMap.expectation
      (UnitalPositiveLinearMap.ofVec (norm_unitPlaneWave (box_succ_nonempty d N) k))
      ⁅hoppingObservable (Λ := box d (N + 1)) g t, positionObservable r⁆ =
      -(t / 2) * ∑ δ ∈ bondVectors g, r δ * Real.sin (k δ) *
        ((((box d (N + 1)).filter fun n => n + δ ∈ box d (N + 1)).card : ℝ) /
          ((N + 1 : ℕ) : ℝ) ^ d) := by
    have hs := sum_adj_eq_sum_bondVectors g (box d (N + 1)) (fun δ => r δ * Real.sin (k δ))
    simp only at hs
    rw [expectation_bracket_unitPlaneWave g (box_succ_nonempty d N), hs, card_box, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun δ _ => ?_
    push_cast
    ring
  simp_rw [heq]
  refine Tendsto.const_mul _ ?_
  rw [show ∑ δ ∈ bondVectors g, r δ * Real.sin (k δ) =
    ∑ δ ∈ bondVectors g, r δ * Real.sin (k δ) * 1 by simp]
  exact tendsto_finsetSum _ fun δ _ => (hratio δ).const_mul _


end CondensedMatter.Crystal
