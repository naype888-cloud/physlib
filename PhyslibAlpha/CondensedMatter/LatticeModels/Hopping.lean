/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import PhyslibAlpha.CondensedMatter.LatticeModels.Variational
/-!

# The hopping Hamiltonian of a graph

## i. Overview

On the Hilbert space `ℂ^ι` of the sites of a finite graph `G`, the kinetic operator of a hop `t`
is `t` times the Laplacian of `G`. Its quadratic form is `t / 2` times the sum over the edges of
the squared differences of the amplitudes, so it is never negative. A local potential `V` adds `Σ
V ‖ψ‖²`, and the ground energy is at least the minimum of `V`.

## ii. Key results

- `lapOp`, `edgeForm` : the Laplacian as an operator and the sum over the edges.
- `inner_lap` : `⟪ψ, L ψ⟫ = ½ Σᵢ Σⱼ [i ~ j] ‖ψᵢ - ψⱼ‖²`.
- `hamiltonian` : the Hamiltonian `t L + V` of a hop and a local potential.
- `rayleigh_hamiltonian` : its Rayleigh quotient is the edge form plus the potential form.
- `groundEnergy_ge_potential` : the ground energy is at least the minimum of `V`.

## iii. Table of contents

- A. The Laplacian and the sum over the edges
- B. The Hamiltonian and its ground energy

## iv. References

-/

@[expose] public section

namespace CondensedMatter
namespace LatticeModels
open scoped InnerProductSpace
open Finset Matrix

/-!

## A. The Laplacian and the sum over the edges

-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]

/-- The Laplacian of the graph as an operator of `ℂ^ι`: the kinetic operator of unit hop. -/
noncomputable def lapOp : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanLin (G.lapMatrix ℂ)

/-- The sum over the edges of the squared differences, `½ Σᵢ Σⱼ [i ~ j] ‖ψᵢ - ψⱼ‖²`. -/
noncomputable def edgeForm (ψ : EuclideanSpace ℂ ι) : ℝ :=
  1 / 2 * ∑ i, ∑ j, if G.Adj i j then ‖ψ.ofLp i - ψ.ofLp j‖ ^ 2 else 0

omit [DecidableEq ι] in
/-- The sum over the edges of the squared differences is never negative. -/
lemma edgeForm_nonneg (ψ : EuclideanSpace ℂ ι) : 0 ≤ edgeForm G ψ := by
  unfold edgeForm
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
  split_ifs <;> positivity

/-- The quadratic form of the Laplacian is the sum over the edges. -/
lemma inner_lap (ψ : EuclideanSpace ℂ ι) : ⟪ψ, lapOp G ψ⟫_ℂ = (edgeForm G ψ : ℂ) := by
  have hN : ∀ i, ∑ u ∈ G.neighborFinset i, (ψ.ofLp i - ψ.ofLp u) =
      ∑ j, if G.Adj i j then ψ.ofLp i - ψ.ofLp j else 0 := fun i => by
    rw [← Finset.sum_filter, SimpleGraph.neighborFinset_eq_filter]
  have h1 : ⟪ψ, lapOp G ψ⟫_ℂ = ∑ i, ∑ j, if G.Adj i j then
      (ψ.ofLp i - ψ.ofLp j) * (starRingEnd ℂ) (ψ.ofLp i) else 0 := by
    have hL : ∀ i, (lapOp G ψ).ofLp i = (G.lapMatrix ℂ *ᵥ ψ.ofLp) i := fun i => rfl
    simp only [PiLp.inner_apply, RCLike.inner_apply, hL, SimpleGraph.lapMatrix_mulVec_apply', hN]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> simp
  have h2 : ∑ i, ∑ j, (if G.Adj i j then (ψ.ofLp i - ψ.ofLp j) * (starRingEnd ℂ) (ψ.ofLp i)
      else 0) = ∑ i, ∑ j, (if G.Adj i j then
        (ψ.ofLp j - ψ.ofLp i) * (starRingEnd ℂ) (ψ.ofLp j) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [G.adj_comm i j]
  have h3 : ∑ i, ∑ j, (if G.Adj i j then (ψ.ofLp i - ψ.ofLp j) * (starRingEnd ℂ) (ψ.ofLp i)
      else 0) = (1 / 2 : ℂ) * ∑ i, ∑ j, (if G.Adj i j then
        ((‖ψ.ofLp i - ψ.ofLp j‖ ^ 2 : ℝ) : ℂ) else 0) := by
    set S := ∑ i, ∑ j, (if G.Adj i j then (ψ.ofLp i - ψ.ofLp j) * (starRingEnd ℂ) (ψ.ofLp i)
      else 0)
    have hS : S + S = ∑ i, ∑ j, (if G.Adj i j then
        ((‖ψ.ofLp i - ψ.ofLp j‖ ^ 2 : ℝ) : ℂ) else 0) := by
      conv_lhs => arg 2; rw [h2]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · have := Complex.mul_conj (ψ.ofLp i - ψ.ofLp j)
        rw [Complex.normSq_eq_norm_sq] at this
        rw [← this]
        simp only [map_sub]
        ring
      · simp
    rw [← hS]; ring
  rw [h1, h3, edgeForm]
  push_cast
  simp only [apply_ite Complex.ofReal, Complex.ofReal_zero, Complex.ofReal_pow]

/-!

## B. The Hamiltonian and its ground energy

-/

/-- The Hamiltonian of a hop `t` and a local potential `V` on the graph `G`. -/
noncomputable def hamiltonian (t : ℝ) (V : ι → ℝ) : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  (t : ℂ) • lapOp G + Matrix.toEuclideanLin (Matrix.diagonal fun i => (V i : ℂ))

/-- The quadratic form of a diagonal potential is `Σ V ‖ψ‖²`. -/
lemma inner_potential (V : ι → ℝ) (ψ : EuclideanSpace ℂ ι) :
    ⟪ψ, Matrix.toEuclideanLin (Matrix.diagonal fun i => (V i : ℂ)) ψ⟫_ℂ =
      ((∑ i, V i * ‖ψ.ofLp i‖ ^ 2 : ℝ) : ℂ) := by
  have hL : ∀ i, (Matrix.toEuclideanLin (Matrix.diagonal fun i => (V i : ℂ)) ψ).ofLp i =
      (V i : ℂ) * ψ.ofLp i := fun i => by
    show ((Matrix.diagonal fun i => (V i : ℂ)) *ᵥ ψ.ofLp) i = _
    simp [Matrix.mulVec_diagonal]
  simp only [PiLp.inner_apply, RCLike.inner_apply, hL]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have := Complex.mul_conj (ψ.ofLp i)
  rw [Complex.normSq_eq_norm_sq] at this
  push_cast at this
  linear_combination (V i : ℂ) * this

/-- The Rayleigh quotient of the Hamiltonian is the edge form plus the potential form. -/
lemma rayleigh_hamiltonian (t : ℝ) (V : ι → ℝ) (ψ : EuclideanSpace ℂ ι) :
    rayleigh (hamiltonian G t V) ψ = t * edgeForm G ψ + ∑ i, V i * ‖ψ.ofLp i‖ ^ 2 := by
  unfold rayleigh hamiltonian
  rw [LinearMap.add_apply, inner_add_right, LinearMap.smul_apply, inner_smul_right, inner_lap,
    inner_potential]
  simp [← Complex.ofReal_mul]

/-- The ground energy is at least the minimum of the potential, for a non-negative hop. -/
lemma groundEnergy_ge_potential {t : ℝ} (ht : 0 ≤ t) {V : ι → ℝ} {m : ℝ} (hm : ∀ i, m ≤ V i)
    (W : Submodule ℂ (EuclideanSpace ℂ ι)) (hne : Nonempty (UnitIn W)) :
    m ≤ groundEnergy (hamiltonian G t V) W := by
  refine le_groundEnergy _ W hne fun ψ _ hψ => ?_
  rw [rayleigh_hamiltonian]
  have h1 : 0 ≤ t * edgeForm G ψ := mul_nonneg ht (edgeForm_nonneg G ψ)
  have h2 : ∑ i, ‖ψ.ofLp i‖ ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_sq_eq] at *
    simp [hψ]
  have h3 : m = ∑ i, m * ‖ψ.ofLp i‖ ^ 2 := by rw [← Finset.mul_sum, h2, mul_one]
  have h4 : ∑ i, m * ‖ψ.ofLp i‖ ^ 2 ≤ ∑ i, V i * ‖ψ.ofLp i‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hm i) (sq_nonneg _)
  linarith

end LatticeModels
end CondensedMatter
