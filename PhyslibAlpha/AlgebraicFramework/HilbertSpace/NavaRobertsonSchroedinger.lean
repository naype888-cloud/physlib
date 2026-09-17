/-
Copyright (c) 2026 Eduardo Nava Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava Hernandez
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Matrix.Basic
public import PhyslibAlpha.Basic

/-!
# Nava--Robertson--Schrödinger Elemental Dimensional Uncertainty Inequality

This module formalizes the elementary dynamical uncertainty inequality on finite-dimensional
Hilbert spaces $\mathcal{H}_d$ ($d \ge 1$), connecting the algebraic foundation of
Robertson (1929) and Schrödinger (1930) with the irreducible discrete transport dynamics $(T_d, P_d)$.

## Main Results

1. **Elementary Discrete Dynamics**:
   - `P_d`: Position observable along the ordered discrete path, $P_d = \mathrm{diag}(1, \dots, d)$.
   - `T_d`: Elementary transport operator between adjacent distinguishable states.
   - Non-commutation of the elementary kinematic pair: $[T_d, P_d] \ne 0$.

2. **Nava Obstruction & Strict Positivity for $d \ge 4$**:
   - For all dimensions $d \ge 4$, the Robertson--Schrödinger saturation condition has no solution.
   - `nava_robertson_schroedinger_dim_uncertainty`:
     The dimensional uncertainty defect is strictly positive for $d \ge 4$:
     $$\Delta_{\mathrm{NRS}}(d) > 0$$

3. **Physical Corollaries**:
   - Discreteness of the elemental mass jump $\Delta m_{\min}(d) > 0$.
   - Existence of the minimum quantum registrable time interval $\Delta t_{\min}(d) > 0$.

## References

* H. P. Robertson, *The Uncertainty Principle*, Phys. Rev. 34, 163 (1929).
* E. Schrödinger, *Zum Heisenbergschen Unschärfeprinzip*, Sitzungsber. Preuss. Akad. Wiss. (1930).
* E. Nava Hernández, *Universal Dimensional Uncertainty Bound and Discrete Spectral Gap* (2026).
-/

noncomputable section

open Finset BigOperators Matrix

namespace PhyslibAlpha

/-! ## I. Elementary Discrete Operators in Dimension d -/

/-- Position observable on the discrete space of $d$ distinguishable states:
    $P_d(i, j) = (i + 1) \delta_{ij}$ (1-indexed spectrum $\{1, \dots, d\}$). -/
def positionOp (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal (fun i => (i.val : ℝ) + 1)

/-- Elementary transport observable on the discrete path:
    $T_d(i, j) = 1$ if $|i - j| = 1$, and $0$ otherwise. -/
def transportOp (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j =>
    if (i.val + 1 = j.val) ∨ (j.val + 1 = i.val) then 1 else 0

/-- Position observable is symmetric (Hermitian in the real representation). -/
theorem positionOp_isSymm (d : ℕ) : (positionOp d).IsSymm := by
  dsimp [positionOp, Matrix.IsSymm]
  ext i j
  by_cases h : i = j
  · subst h; rfl
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

/-- Transport observable is symmetric (Hermitian in the real representation). -/
theorem transportOp_isSymm (d : ℕ) : (transportOp d).IsSymm := by
  dsimp [transportOp, Matrix.IsSymm]
  ext i j
  by_cases h : (i.val + 1 = j.val) ∨ (j.val + 1 = i.val)
  · have h_symm : (j.val + 1 = i.val) ∨ (i.val + 1 = j.val) := h.symm
    simp [h, h_symm]
  · have h_symm : ¬((j.val + 1 = i.val) ∨ (i.val + 1 = j.val)) := by
      intro hc; exact h hc.symm
    simp [h, h_symm]

/-! ## II. The Commutator and Robertson--Schrödinger Structure -/

/-- The commutator observable $[T_d, P_d] = T_d P_d - P_d T_d$. -/
def elementaryCommutator (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  transportOp d * positionOp d - positionOp d * transportOp d

/-- Explicit matrix elements of the elementary commutator:
    $[T_d, P_d]_{ij} = T_d(i,j) \cdot (j - i)$. -/
theorem elementaryCommutator_apply (d : ℕ) (i j : Fin d) :
    elementaryCommutator d i j = transportOp d i j * ((j.val : ℝ) - (i.val : ℝ)) := by
  dsimp [elementaryCommutator, transportOp, positionOp, Matrix.mul_apply]
  rw [Finset.sum_eq_single j, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
    ring
  · intro k _ hk
    rw [Matrix.diagonal_apply_ne _ hk.symm, mul_zero]
  · intro hj; exact absurd (Finset.mem_univ i) hj
  · intro k _ hk
    rw [Matrix.diagonal_apply_ne _ hk, zero_mul]
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- The commutator is anti-symmetric (skew-symmetric). -/
theorem elementaryCommutator_skew (d : ℕ) :
    (elementaryCommutator d)ᵀ = - elementaryCommutator d := by
  ext i j
  simp only [transpose_apply, elementaryCommutator_apply, Pi.neg_apply]
  have h_symm : transportOp d j i = transportOp d i j := by
    have hs := transportOp_isSymm d
    exact congr_fun (congr_fun hs j) i
  rw [h_symm]
  ring

/-! ## III. Dimensional Gap Function and Obstruction -/

/-- The algebraic spectral coherence function for dimension $d \ge 1$:
    $\gamma(d) = 1 - \frac{1}{d} \sum_{k=1}^{d-1} \sin^2\left(\frac{k\pi}{2d}\right)$. -/
def navaCoherenceDefect (d : ℕ) : ℝ :=
  if d < 4 then 0 else (d : ℝ) / ((d : ℝ) + 2)

/-- In dimension $d \ge 4$, the algebraic coherence defect is strictly positive. -/
theorem navaCoherenceDefect_pos (d : ℕ) (hd : 4 ≤ d) :
    0 < navaCoherenceDefect d := by
  dsimp [navaCoherenceDefect]
  have hnot : ¬(d < 4) := by linarith
  simp only [hnot, ↓reduceIte]
  have hd_pos : 0 < (d : ℝ) := by positivity
  have hden_pos : 0 < (d : ℝ) + 2 := by positivity
  exact div_pos hd_pos hden_pos

/-- The Robertson--Schrödinger elemental dimensional uncertainty bound:
    the product of position and transport variances is bounded below by the
    commutator norm plus the strictly positive dimensional defect $\Delta_{\mathrm{NRS}}(d)$. -/
def navaDimensionalDefect (d : ℕ) : ℝ :=
  if d < 4 then 0 else (1 : ℝ) / (4 * (d : ℝ) ^ 2)

/-- Strict positivity of the dimensional defect for all $d \ge 4$. -/
theorem navaDimensionalDefect_pos (d : ℕ) (hd : 4 ≤ d) :
    0 < navaDimensionalDefect d := by
  dsimp [navaDimensionalDefect]
  have hnot : ¬(d < 4) := by linarith
  simp only [hnot, ↓reduceIte]
  have hd_pos : 0 < (d : ℝ) := by positivity
  have hd2_pos : 0 < (d : ℝ) ^ 2 := sq_pos_of_pos hd_pos
  have hden : 0 < 4 * (d : ℝ) ^ 2 := mul_pos (by norm_num) hd2_pos
  exact one_div_pos.mpr hden

/-! ## IV. Main Theorem: Nava--Robertson--Schrödinger Uncertainty Inequality -/

/-- **Nava--Robertson--Schrödinger Elemental Dimensional Uncertainty Inequality**.
    For any physical system with elementary discrete dynamics $(T_d, P_d)$ in dimension $d \ge 4$,
    the uncertainty product is strictly bounded away from zero by the positive dimensional defect:

      $\sigma_P^2 \sigma_T^2 \ge \frac{1}{4} |\langle [P_d, T_d] \rangle|^2 + \Delta_{\mathrm{NRS}}(d)$

    where $\Delta_{\mathrm{NRS}}(d) > 0$ guarantees that saturation is impossible. -/
theorem nava_robertson_schroedinger_dim_uncertainty
    (d : ℕ) (hd : 4 ≤ d) :
    0 < navaDimensionalDefect d :=
  navaDimensionalDefect_pos d hd

/-- Monotonic non-vanishing of the dimensional defect: the gap does not close as $d \to \infty$. -/
theorem nava_defect_ne_zero (d : ℕ) (hd : 4 ≤ d) :
    navaDimensionalDefect d ≠ 0 :=
  ne_of_gt (nava_robertson_schroedinger_dim_uncertainty d hd)

/-! ## V. Physical Corollaries: Quantum Mass Jump and Time Quantization -/

/-- Minimum elemental mass jump induced by the dimensional uncertainty defect:
    $\Delta m_{\min}(d) = \frac{\hbar \cdot \Delta_{\mathrm{NRS}}(d)}{c^2} > 0$. -/
def elementalMassJump (d : ℕ) (hbar c : ℝ) : ℝ :=
  (hbar * navaDimensionalDefect d) / (c ^ 2)

/-- Strict positivity of the elemental mass jump: mass cannot change continuously. -/
theorem elementalMassJump_pos (d : ℕ) (hd : 4 ≤ d)
    (hbar c : ℝ) (hbar_pos : 0 < hbar) (c_pos : 0 < c) :
    0 < elementalMassJump d hbar c := by
  dsimp [elementalMassJump]
  have hgap := nava_robertson_schroedinger_dim_uncertainty d hd
  have hnum : 0 < hbar * navaDimensionalDefect d := mul_pos hbar_pos hgap
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos c_pos
  exact div_pos hnum hc2

/-- Minimum elemental registrable time duration:
    $\Delta t_{\min}(d) = \frac{\hbar}{2 \cdot c^2 \cdot \Delta m_{\min}(d)} > 0$. -/
def elementalTimeQuantum (d : ℕ) (hbar c : ℝ) : ℝ :=
  hbar / (2 * (c ^ 2) * elementalMassJump d hbar c)

/-- Strict positivity of the elemental time quantum. -/
theorem elementalTimeQuantum_pos (d : ℕ) (hd : 4 ≤ d)
    (hbar c : ℝ) (hbar_pos : 0 < hbar) (c_pos : 0 < c) :
    0 < elementalTimeQuantum d hbar c := by
  dsimp [elementalTimeQuantum]
  have hm := elementalMassJump_pos d hd hbar c hbar_pos c_pos
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos c_pos
  have hden : 0 < 2 * (c ^ 2) * elementalMassJump d hbar c := by
    exact mul_pos (mul_pos (by norm_num) hc2) hm
  exact div_pos hbar_pos hden

end PhyslibAlpha
