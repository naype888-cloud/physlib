/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.NavaCoherencePositivity

/-!

# The Robertson–Schrödinger inequality for the path observables

Let `T = transportObservable d` and `P = positionObservable d` on `ℂ^d`, and let `ψ` be the
extremal vector `extremalState d`. The Robertson–Schrödinger inequality
`cov(T, P) ^ 2 + ⟨[T, P]⟩ ^ 2 ≤ Var T * Var P` holds in every state. In the vector state of `ψ`
its gap is exactly `(C_Nava d ^ 2 - 1) / (d - 1) ^ 2`, by `nava_robertson_defect`. Combined with the
values of `C_Nava d ^ 2`, this shows that in this state the inequality

* is an equality if and only if `d = 2` or `d = 3`,
* is strict for every `d ≥ 4`.

All three statements are about this single vector state; nothing is asserted about other states.

## Main results

- `robertson_schrodinger_gap_extremal` : the gap is `(C_Nava d ^ 2 - 1) / (d - 1) ^ 2`.
- `robertson_schrodinger_eq_iff_extremal` : equality holds exactly for `d = 2` and `d = 3`.
- `robertson_schrodinger_lt_extremal` : the inequality is strict for `d ≥ 4`.

-/

@[expose] public section

open scoped ComplexOrder InnerProductSpace
open ContinuousLinearMap UnitalPositiveLinearMap
open scoped selfAdjoint

namespace PathObservables

/-- The vector state of the extremal vector `extremalState d`, for `2 ≤ d`. -/
noncomputable def extremalVectorState {d : ℕ} (hd : 2 ≤ d) :
    𝓢[EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)] :=
  UnitalPositiveLinearMap.ofVec (norm_extremalState d (by omega))

/-- In the extremal vector state, the gap in the Robertson–Schrödinger inequality for the path
observables is `(C_Nava d ^ 2 - 1) / (d - 1) ^ 2`. -/
lemma robertson_schrodinger_gap_extremal {d : ℕ} (hd : 2 ≤ d) :
    variance (extremalVectorState hd) (transportObservable d) *
        variance (extremalVectorState hd) (positionObservable d) -
      (covariance (extremalVectorState hd) (transportObservable d) (positionObservable d) ^ 2 +
        (extremalVectorState hd)⟨⁅transportObservable d, positionObservable d⁆⟩ ^ 2) =
      (CNavaSq d - 1) / ((d : ℝ) - 1) ^ 2 := by
  have h : centeredGramDefect (extremalVectorState hd) (transportObservable d)
      (positionObservable d) = (CNavaSq d - 1) / ((d : ℝ) - 1) ^ 2 := nava_robertson_defect hd
  unfold centeredGramDefect at h
  rw [normSq_centered_pairing] at h
  exact h

/-- In the extremal vector state, the Robertson–Schrödinger inequality for the path observables
is an equality if and only if `d = 2` or `d = 3`. -/
lemma robertson_schrodinger_eq_iff_extremal {d : ℕ} (hd : 2 ≤ d) :
    covariance (extremalVectorState hd) (transportObservable d) (positionObservable d) ^ 2 +
        (extremalVectorState hd)⟨⁅transportObservable d, positionObservable d⁆⟩ ^ 2 =
      variance (extremalVectorState hd) (transportObservable d) *
        variance (extremalVectorState hd) (positionObservable d) ↔ d = 2 ∨ d = 3 := by
  have hd1 : ((d : ℝ) - 1) ^ 2 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    positivity
  have hgap := robertson_schrodinger_gap_extremal hd
  constructor
  · intro h
    have h0 : (CNavaSq d - 1) / ((d : ℝ) - 1) ^ 2 = 0 := by rw [← hgap]; linarith
    have hC : CNavaSq d = 1 := by
      rcases div_eq_zero_iff.mp h0 with h1 | h1
      · linarith
      · exact absurd h1 hd1
    by_contra hne
    exact (one_lt_CNavaSq (by omega : 4 ≤ d)).ne' hC
  · rintro (rfl | rfl)
    · have h : (CNavaSq 2 - 1) / (((2 : ℕ) : ℝ) - 1) ^ 2 = 0 := by rw [CNavaSq_two]; simp
      linarith
    · have h : (CNavaSq 3 - 1) / (((3 : ℕ) : ℝ) - 1) ^ 2 = 0 := by rw [CNavaSq_three]; simp
      linarith

/-- In the extremal vector state, the Robertson–Schrödinger inequality for the path observables
is strict for every `d ≥ 4`. -/
lemma robertson_schrodinger_lt_extremal {d : ℕ} (hd : 4 ≤ d) :
    let ω := extremalVectorState (by omega : 2 ≤ d)
    covariance ω (transportObservable d) (positionObservable d) ^ 2 +
        ω⟨⁅transportObservable d, positionObservable d⁆⟩ ^ 2 <
      variance ω (transportObservable d) * variance ω (positionObservable d) := by
  intro ω
  refine lt_of_le_of_ne (robertson_schrodinger ω _ _) fun h => ?_
  have := (robertson_schrodinger_eq_iff_extremal (by omega : 2 ≤ d)).mp h
  omega

end PathObservables
