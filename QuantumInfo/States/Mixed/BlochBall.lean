/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import QuantumInfo.States.Mixed.MState
public import QuantumInfo.States.Pure.Qubit

/-!
# The Bloch ball

## i. Overview

The identity and the three Pauli gates `X`, `Y`, `Z` form a basis of the self-adjoint two by
two complex matrices: every such `A` is `(tr A + ⟪X, A⟫ X + ⟪Y, A⟫ Y + ⟪Z, A⟫ Z) / 2`.
For a state `ρ` of a qubit the trace is one, so `ρ = (1 + w_x X + w_y Y + w_z Z) / 2` where
`w = (⟨X⟩, ⟨Y⟩, ⟨Z⟩)` is the Bloch vector, the triple of expectation values of the Pauli
gates. The determinant of `ρ` is `(1 - |w|²) / 4`, and `ρ` is positive semidefinite exactly
when `|w| ≤ 1`. So the Bloch vector is a bijection from the states of a qubit onto the closed
unit ball of three-dimensional Euclidean space.

## ii. Key results

- `Qubit.pauliBasis` : the identity and the Pauli gates as a basis of the self-adjoint matrices.
- `Qubit.eq_pauli_decomposition` : the decomposition of a self-adjoint matrix in that basis.
- `MState.M_eq_blochMat` : a state is one half of the identity plus a real combination of
  the Pauli gates, with the Bloch vector as coefficients.
- `MState.blochVector_mem_closedBall` : the Bloch vector lies in the closed unit ball.
- `MState.blochEquiv` : the Bloch vector is a bijection onto the closed unit ball.

## iii. Table of contents

- A. The Pauli gates as self-adjoint matrices
- B. The Pauli basis
- C. The Bloch vector
- D. The Bloch ball

## iv. References

* M. A. Nielsen and I. L. Chuang, *Quantum Computation and Quantum Information*,
  Cambridge University Press (2010), §2.4.1 and Exercise 2.72.

-/

@[expose] public section

open Matrix
open scoped ComplexOrder InnerProductSpace

noncomputable section

namespace Qubit

/-!

## A. The Pauli gates as self-adjoint matrices

-/

/-- The Pauli gates `X`, `Y`, `Z` as self-adjoint matrices. -/
def pauli (j : Fin 3) : HermitianMat Qubit ℂ :=
  ⟨![X.val, Y.val, Z.val] j, by
    fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;> simp [X, Y, Z]⟩

lemma pauli_mat (j : Fin 3) : (pauli j).mat = ![X.val, Y.val, Z.val] j := rfl

lemma pauli_zero_mat : (pauli 0).mat = !![0, 1; 1, 0] := rfl

lemma pauli_one_mat : (pauli 1).mat = !![0, -Complex.I; Complex.I, 0] := rfl

lemma pauli_two_mat : (pauli 2).mat = !![1, 0; 0, -1] := rfl

/-- `⟪σⱼ, A⟫ = Re tr(σⱼ A)` in terms of the entries of `A`. -/
lemma inner_pauli (A : HermitianMat Qubit ℂ) :
    ⟪pauli 0, A⟫_ℝ = (A.mat 1 0).re + (A.mat 0 1).re ∧
    ⟪pauli 1, A⟫_ℝ = (A.mat 1 0).im - (A.mat 0 1).im ∧
    ⟪pauli 2, A⟫_ℝ = (A.mat 0 0).re - (A.mat 1 1).re := by
  simp only [HermitianMat.inner_eq_re_trace, pauli_zero_mat, pauli_one_mat, pauli_two_mat,
    trace_fin_two, mul_apply, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_⟩ <;> simp [-HermitianMat.mat_apply] <;> ring

/-!

## B. The Pauli basis

-/

/-- The identity followed by the three Pauli gates. -/
def pauliFamily : Fin 4 → HermitianMat Qubit ℂ :=
  ![1, pauli 0, pauli 1, pauli 2]

/-- **Pauli decomposition.** A self-adjoint matrix is
`(tr A + ⟪X, A⟫ X + ⟪Y, A⟫ Y + ⟪Z, A⟫ Z) / 2`. -/
lemma eq_pauli_decomposition (A : HermitianMat Qubit ℂ) :
    A = (2⁻¹ : ℝ) • (A.trace • 1 + ∑ j, ⟪pauli j, A⟫_ℝ • pauli j) := by
  obtain ⟨h0, h1, h2⟩ := inner_pauli A
  have hA := A.H
  have h00 := congrFun₂ hA 0 0
  have h11 := congrFun₂ hA 1 1
  have h01 := congrFun₂ hA 0 1
  simp only [conjTranspose_apply, Complex.star_def, Complex.ext_iff, Complex.conj_re,
    Complex.conj_im] at h00 h11 h01
  ext a b
  rw [Fin.sum_univ_three, h0, h1, h2, HermitianMat.trace_eq_re_trace, trace_fin_two]
  fin_cases a <;> fin_cases b <;>
    simp [-HermitianMat.mat_apply, HermitianMat.mat_smul, HermitianMat.mat_add,
      HermitianMat.mat_one, Complex.ext_iff, pauli_zero_mat, pauli_one_mat,
      pauli_two_mat] <;> constructor <;> linarith

lemma linearIndependent_pauliFamily : LinearIndependent ℝ pauliFamily := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have e : ∀ a b : Qubit, (∑ i, g i • pauliFamily i).mat a b = 0 := by
    simp [-HermitianMat.mat_apply, hg]
  have e00 := e 0 0
  have e11 := e 1 1
  have e01 := e 0 1
  simp [-HermitianMat.mat_apply, Fin.sum_univ_four, pauliFamily, HermitianMat.mat_smul,
    HermitianMat.mat_add, HermitianMat.mat_one, pauli_zero_mat, pauli_one_mat, pauli_two_mat,
    Complex.ext_iff] at e00 e11 e01
  intro i
  fin_cases i <;> simp <;> linarith [e00, e11, e01.1, e01.2]

lemma span_pauliFamily : ⊤ ≤ Submodule.span ℝ (Set.range pauliFamily) := by
  intro A _
  rw [eq_pauli_decomposition A]
  refine Submodule.smul_mem _ _ (Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun j _ => ?_))
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨j.succ, ?_⟩)
    fin_cases j <;> rfl

/-- The identity and the three Pauli gates form a basis of the self-adjoint two by two complex
matrices. -/
def pauliBasis : Module.Basis (Fin 4) ℝ (HermitianMat Qubit ℂ) :=
  .mk linearIndependent_pauliFamily span_pauliFamily

@[simp]
lemma pauliBasis_apply (i : Fin 4) : pauliBasis i = pauliFamily i := by
  simp [pauliBasis]

end Qubit

namespace MState

open Qubit

/-!

## C. The Bloch vector

-/

/-- The Bloch vector of a state of a qubit: the expectation values of the Pauli gates. -/
def blochVector (ρ : MState Qubit) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 fun j => ρ.exp_val (pauli j)

@[simp]
lemma blochVector_apply (ρ : MState Qubit) (j : Fin 3) :
    ρ.blochVector j = ρ.exp_val (pauli j) := rfl

/-- The self-adjoint matrix `(1 + w_x X + w_y Y + w_z Z) / 2` with Bloch vector `w`. -/
def blochMat (w : EuclideanSpace ℝ (Fin 3)) : HermitianMat Qubit ℂ :=
  (2⁻¹ : ℝ) • (1 + ∑ j, w j • pauli j)

lemma blochMat_mat (w : EuclideanSpace ℝ (Fin 3)) : (blochMat w).mat =
    !![(1 + (w 2 : ℂ)) / 2, (w 0 - Complex.I * w 1) / 2;
      (w 0 + Complex.I * w 1) / 2, (1 - (w 2 : ℂ)) / 2] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [-HermitianMat.mat_apply, blochMat, Fin.sum_univ_three, HermitianMat.mat_smul,
      HermitianMat.mat_add, HermitianMat.mat_one, pauli_zero_mat, pauli_one_mat,
      pauli_two_mat] <;> ring

/-- **Decomposition of a qubit state.** `ρ = (1 + ⟨X⟩ X + ⟨Y⟩ Y + ⟨Z⟩ Z) / 2`. -/
lemma M_eq_blochMat (ρ : MState Qubit) : ρ.M = blochMat ρ.blochVector := by
  conv_lhs => rw [eq_pauli_decomposition ρ.M, ρ.tr]
  simp [blochMat, exp_val, HermitianMat.inner_comm]

lemma trace_blochMat (w : EuclideanSpace ℝ (Fin 3)) : (blochMat w).trace = 1 := by
  rw [HermitianMat.trace_eq_re_trace, blochMat_mat, trace_fin_two]
  simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
    RCLike.re_to_complex, Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.ofReal_re,
    Complex.sub_re]
  ring

/-!

## D. The Bloch ball

-/

/-- With `|w| ≤ 1`, the quadratic form `x* (1 + w · σ) x` is nonnegative, by Cauchy–Schwarz:
the vector `(2 Re(a* b), 2 Im(a* b), |a|² − |b|²)` has length `|a|² + |b|²`. -/
lemma bloch_quadratic_nonneg {w₀ w₁ w₂ : ℝ} (hw : w₀ ^ 2 + w₁ ^ 2 + w₂ ^ 2 ≤ 1)
    (a₁ a₂ b₁ b₂ : ℝ) :
    0 ≤ a₁ ^ 2 + a₂ ^ 2 + b₁ ^ 2 + b₂ ^ 2 + (w₀ * (2 * (a₁ * b₁ + a₂ * b₂)) +
      w₁ * (2 * (a₁ * b₂ - a₂ * b₁)) + w₂ * (a₁ ^ 2 + a₂ ^ 2 - (b₁ ^ 2 + b₂ ^ 2))) := by
  set s := a₁ ^ 2 + a₂ ^ 2 + b₁ ^ 2 + b₂ ^ 2
  set p := 2 * (a₁ * b₁ + a₂ * b₂)
  set q := 2 * (a₁ * b₂ - a₂ * b₁)
  set d := a₁ ^ 2 + a₂ ^ 2 - (b₁ ^ 2 + b₂ ^ 2)
  have hv : p ^ 2 + q ^ 2 + d ^ 2 = s ^ 2 := by simp only [s, p, q, d]; ring
  have hs : 0 ≤ s := by positivity
  have hcs : (w₀ * p + w₁ * q + w₂ * d) ^ 2 ≤ s ^ 2 := by
    nlinarith [sq_nonneg (w₀ * q - w₁ * p), sq_nonneg (w₀ * d - w₂ * p),
      sq_nonneg (w₁ * d - w₂ * q), sq_nonneg p, sq_nonneg q, sq_nonneg d]
  nlinarith [neg_abs_le (w₀ * p + w₁ * q + w₂ * d), abs_le_of_sq_le_sq' hcs hs]

lemma norm_sq_eq (w : EuclideanSpace ℝ (Fin 3)) : ‖w‖ ^ 2 = w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]

/-- `blochMat w` is positive semidefinite exactly when `|w| ≤ 1`. -/
lemma zero_le_blochMat_iff (w : EuclideanSpace ℝ (Fin 3)) : 0 ≤ blochMat w ↔ ‖w‖ ≤ 1 := by
  rw [HermitianMat.zero_le_iff, ← sq_le_one_iff₀ (norm_nonneg w), norm_sq_eq]
  constructor
  · intro h
    have hd := h.det_nonneg
    rw [blochMat_mat, det_fin_two_of, Complex.nonneg_iff] at hd
    simp at hd
    nlinarith [hd.1]
  · intro hw
    refine PosSemidef.of_dotProduct_mulVec_nonneg (blochMat w).H fun x => ?_
    rw [Complex.nonneg_iff, blochMat_mat]
    simp [ dotProduct, mulVec, Fin.sum_univ_two]
    constructor
    · nlinarith [bloch_quadratic_nonneg hw (x 0).re (x 0).im (x 1).re (x 1).im]
    · ring

/-- The Bloch vector of a state lies in the closed unit ball. -/
lemma blochVector_mem_closedBall (ρ : MState Qubit) :
    ρ.blochVector ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [mem_closedBall_zero_iff, ← zero_le_blochMat_iff, ← M_eq_blochMat]
  exact ρ.nonneg

/-- The state with Bloch vector `w`, for `|w| ≤ 1`. -/
def ofBlochVector (w : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) : MState Qubit where
  M := blochMat w
  nonneg := (zero_le_blochMat_iff w).2 (mem_closedBall_zero_iff.1 w.2)
  tr := trace_blochMat w

lemma blochVector_blochMat (w : EuclideanSpace ℝ (Fin 3)) (j : Fin 3) :
    ⟪blochMat w, pauli j⟫_ℝ = w j := by
  rw [HermitianMat.inner_comm]
  obtain ⟨h0, h1, h2⟩ := inner_pauli (blochMat w)
  fin_cases j
  · rw [Fin.zero_eta, h0, blochMat_mat]
    simp
  · rw [Fin.mk_one, h1, blochMat_mat]
    simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
      Complex.div_ofNat_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      mul_zero, Complex.I_im, Complex.ofReal_re, one_mul, zero_add, Complex.sub_im, zero_sub]
    ring
  · rw [show (⟨2, by omega⟩ : Fin 3) = 2 from rfl, h2, blochMat_mat]
    simp only [Fin.isValue, of_apply, cons_val', cons_val_zero, cons_val_fin_one,
      Complex.div_ofNat_re, Complex.add_re, Complex.one_re, Complex.ofReal_re, cons_val_one,
      Complex.sub_re]
    ring

/-- **The Bloch ball.** The Bloch vector is a bijection from the states of a qubit onto the
closed unit ball of three-dimensional Euclidean space. -/
def blochEquiv : MState Qubit ≃ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 where
  toFun ρ := ⟨ρ.blochVector, ρ.blochVector_mem_closedBall⟩
  invFun := ofBlochVector
  left_inv ρ := by
    ext1
    simp only [ofBlochVector]
    exact (M_eq_blochMat ρ).symm
  right_inv w := by
    ext j
    simp [ofBlochVector, exp_val, blochVector_blochMat]

end MState
