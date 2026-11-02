/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import PhyslibAlpha.CondensedMatter.LatticeModels.Hopping
/-!

# The speed limit of a hopping graph

## i. Overview

On the sites of a finite graph `G` with a real position `x` and a hop `t`, the velocity is `v = i
[t A, X]`, where `A` is the adjacency operator and `X` the multiplication by `x`: it acts as `(v
ψ)(p) = i t Σ_{q ~ p} (x q - x p) ψ(q)`. If every edge moves the position by at most `Δ` and every
site has at most `D` neighbours, then `‖v ψ‖ ≤ t Δ D ‖ψ‖` (Schur's test).

## ii. Key results

- `velocityMatrix`, `velocityOp` : the matrix and the operator of the velocity.
- `velocityMatrix_eq` : the matrix of the velocity is `i t (A X - X A)`.
- `velocity_bound` : `‖v ψ‖ ≤ t Δ D ‖ψ‖`.

## iii. Table of contents

- A. The velocity operator
- B. The bound

## iv. References

-/

@[expose] public section

namespace CondensedMatter
namespace LatticeModels
open scoped InnerProductSpace
open Finset Matrix

/-!

## A. The velocity operator

-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (G : SimpleGraph ι) [DecidableRel G.Adj]

/-- The matrix of the velocity `i t [A, X]`. -/
noncomputable def velocityMatrix (t : ℝ) (x : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.of fun p q => if G.Adj p q then Complex.I * (t : ℂ) * ((x q : ℂ) - (x p : ℂ)) else 0

/-- The velocity operator `i t [A, X]`. -/
noncomputable def velocityOp (t : ℝ) (x : ι → ℝ) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι :=
  Matrix.toEuclideanLin (velocityMatrix G t x)

/-- The velocity is `i t` times the commutator of the adjacency with the position. -/
lemma velocityMatrix_eq (t : ℝ) (x : ι → ℝ) :
    velocityMatrix G t x =
      Complex.I • (t : ℂ) • (G.adjMatrix ℂ * Matrix.diagonal (fun i => (x i : ℂ)) -
        Matrix.diagonal (fun i => (x i : ℂ)) * G.adjMatrix ℂ) := by
  ext p q
  simp only [velocityMatrix, Matrix.of_apply, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul, SimpleGraph.adjMatrix_apply, smul_eq_mul]
  split_ifs <;> ring

/-!

## B. The bound

-/

omit [DecidableEq ι] in
/-- Summing a function of the neighbours over all sites weighs each site by its degree. -/
lemma sum_neighbors_swap (f : ι → ℝ) :
    ∑ p, ∑ q ∈ G.neighborFinset p, f q = ∑ q, (G.degree q : ℝ) * f q := by
  have h : ∀ p, ∑ q ∈ G.neighborFinset p, f q = ∑ q, if G.Adj p q then f q else 0 := fun p => by
    rw [← Finset.sum_filter, SimpleGraph.neighborFinset_eq_filter]
  simp_rw [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  have : ∀ p, (if G.Adj p q then f q else 0) = if G.Adj q p then f q else 0 := fun p => by
    simp only [G.adj_comm p q]
  simp_rw [this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  rw [← SimpleGraph.neighborFinset_eq_filter, SimpleGraph.card_neighborFinset_eq_degree]

/-- The speed bound. -/
lemma velocity_bound (t Δ : ℝ) {x : ι → ℝ} (ht : 0 ≤ t) (hΔ : 0 ≤ Δ) {D : ℕ}
    (hx : ∀ p q, G.Adj p q → |x q - x p| ≤ Δ) (hD : ∀ p, G.degree p ≤ D)
    (ψ : EuclideanSpace ℂ ι) : ‖velocityOp G t x ψ‖ ≤ t * Δ * D * ‖ψ‖ := by
  have hent : ∀ p, ((velocityOp G t x) ψ).ofLp p =
      ∑ q ∈ G.neighborFinset p, Complex.I * (t : ℂ) * ((x q : ℂ) - (x p : ℂ)) * ψ.ofLp q := by
    intro p
    show ((velocityMatrix G t x) *ᵥ ψ.ofLp) p = _
    simp only [velocityMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
    exact Finset.sum_congr rfl fun q _ => by split_ifs <;> simp
  have hp : ∀ p, ‖((velocityOp G t x) ψ).ofLp p‖ ^ 2 ≤
      (t * Δ) ^ 2 * D * ∑ q ∈ G.neighborFinset p, ‖ψ.ofLp q‖ ^ 2 := by
    intro p
    rw [hent p]
    have h1 : ‖∑ q ∈ G.neighborFinset p, Complex.I * (t : ℂ) * ((x q : ℂ) - (x p : ℂ)) *
        ψ.ofLp q‖ ≤ ∑ q ∈ G.neighborFinset p, t * Δ * ‖ψ.ofLp q‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq => ?_)
      have hadj : G.Adj p q := by simpa using hq
      have : ‖Complex.I * (t : ℂ) * ((x q : ℂ) - (x p : ℂ)) * ψ.ofLp q‖ =
          t * |x q - x p| * ‖ψ.ofLp q‖ := by
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, ← Complex.ofReal_sub,
          Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ht, one_mul]
      rw [this]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hx p q hadj) ht) (norm_nonneg _)
    have h2 : (∑ q ∈ G.neighborFinset p, t * Δ * ‖ψ.ofLp q‖) ^ 2 ≤
        (G.neighborFinset p).card * ∑ q ∈ G.neighborFinset p, (t * Δ * ‖ψ.ofLp q‖) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hc : ((G.neighborFinset p).card : ℝ) ≤ D := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]; exact_mod_cast hD p
    calc ‖∑ q ∈ G.neighborFinset p, Complex.I * (t : ℂ) * ((x q : ℂ) - (x p : ℂ)) *
          ψ.ofLp q‖ ^ 2
        ≤ (∑ q ∈ G.neighborFinset p, t * Δ * ‖ψ.ofLp q‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ ≤ (t * Δ) ^ 2 * D * ∑ q ∈ G.neighborFinset p, ‖ψ.ofLp q‖ ^ 2 := by
          have : ∑ q ∈ G.neighborFinset p, (t * Δ * ‖ψ.ofLp q‖) ^ 2 =
              (t * Δ) ^ 2 * ∑ q ∈ G.neighborFinset p, ‖ψ.ofLp q‖ ^ 2 := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
          rw [this]
          have h0 : 0 ≤ (t * Δ) ^ 2 * ∑ q ∈ G.neighborFinset p, ‖ψ.ofLp q‖ ^ 2 :=
            mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          nlinarith [mul_le_mul_of_nonneg_right hc h0]
  have hsum : ‖velocityOp G t x ψ‖ ^ 2 ≤ (t * Δ * D) ^ 2 * ‖ψ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    calc ∑ p, ‖((velocityOp G t x) ψ).ofLp p‖ ^ 2
        ≤ ∑ p, (t * Δ) ^ 2 * D * ∑ q ∈ G.neighborFinset p, ‖ψ.ofLp q‖ ^ 2 :=
          Finset.sum_le_sum fun p _ => hp p
      _ = (t * Δ) ^ 2 * D * ∑ q, (G.degree q : ℝ) * ‖ψ.ofLp q‖ ^ 2 := by
          rw [← Finset.mul_sum, sum_neighbors_swap G (fun q => ‖ψ.ofLp q‖ ^ 2)]
      _ ≤ (t * Δ) ^ 2 * D * ∑ q, (D : ℝ) * ‖ψ.ofLp q‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => ?_)
            (by positivity)
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hD q) (sq_nonneg _)
      _ = (t * Δ * D) ^ 2 * ∑ q, ‖ψ.ofLp q‖ ^ 2 := by
          rw [← Finset.mul_sum]; ring
  have hr : 0 ≤ t * Δ * D * ‖ψ‖ := by positivity
  exact abs_le_of_sq_le_sq' (by nlinarith [hsum]) hr |>.2

end LatticeModels
end CondensedMatter
