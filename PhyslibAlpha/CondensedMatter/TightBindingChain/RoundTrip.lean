/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.CausalCone
/-!

# The round trip of the uncertainty

## i. Overview

Reversing the direction of an observable, `b ↦ -b`, reflects the uncertainty vector: the
covariance and the bracket change sign, the variances do not. The centered Gram defect, and with
it the proper time, is the same both ways: going and coming back cost the same.

The way there and the way back together have no net covariance and no net bracket. Yet, by the
reverse triangle inequality of causal vectors, their sum carries at least twice the proper time
of one way: the round trip pays twice, and returning to the start does not undo it.

For the energy and position of the open tight binding chain in the maximal current state, with
the position reflected, the round trip has positive proper time from four sites on.

## ii. Key results

- `centeredGramDefect_neg_right` : the defect does not depend on the direction.
- `properTime_uncertaintyVector_neg_right` : nor does the proper time.
- `uncertaintyVector_add_neg_right_inr_one` : the way there and back has no net bracket.
- `two_mul_properTime_le_round_trip` : the round trip carries at least twice the proper time.
- `round_trip_maxCurrentState_pos` : for the chain, from four sites on, it is positive.

## iii. Table of contents

- A. Reversing the direction
- B. The round trip
- C. The open tight binding chain

## iv. References

* P. Langevin, *L'évolution de l'espace et du temps*, Scientia 10 (1911) 31.

-/

@[expose] public section

namespace ProbabilisticTheory
namespace UnitalPositiveLinearMap

open scoped ComplexOrder selfAdjoint

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (ω : 𝓢[ℂ, A]) (a b : Observable A)

/-!

## A. Reversing the direction

-/

/-- Reversing an observable reverses its fluctuation. -/
lemma centered_neg : centered ω (-b) = -centered ω b := by
  simp only [centered, LinearMap.centered, map_neg, neg_smul, sub_neg_eq_add, neg_sub]
  abel

/-- Reversing an observable keeps its variance. -/
lemma variance_neg : variance ω (-b) = variance ω b := by
  rw [variance_eq_re_apply_centered_mul_self, variance_eq_re_apply_centered_mul_self, centered_neg,
    NegMemClass.coe_neg, neg_mul_neg]

/-- Reversing an observable reverses the pairing of the fluctuations. -/
lemma apply_centered_mul_centered_neg :
    ω ((centered ω a : A) * centered ω (-b)) = -ω ((centered ω a : A) * centered ω b) := by
  rw [centered_neg, NegMemClass.coe_neg, mul_neg, map_neg]

/-- **The defect does not depend on the direction.** -/
lemma centeredGramDefect_neg_right :
    centeredGramDefect ω a (-b) = centeredGramDefect ω a b := by
  rw [centeredGramDefect, centeredGramDefect, variance_neg, apply_centered_mul_centered_neg,
    Complex.normSq_neg]

/-- **Going and coming back cost the same proper time.** -/
theorem properTime_uncertaintyVector_neg_right :
    SpaceTime.properTime 0 (uncertaintyVector ω a (-b)) =
      SpaceTime.properTime 0 (uncertaintyVector ω a b) := by
  simp only [SpaceTime.properTime, sub_zero, minkowskiProduct_uncertaintyVector,
    centeredGramDefect_neg_right]

/-!

## B. The round trip

-/

/-- The way there and the way back together have no net bracket. -/
lemma uncertaintyVector_add_neg_right_inr_one :
    (uncertaintyVector ω a b + uncertaintyVector ω a (-b)) (Sum.inr 1) = 0 := by
  have h1 := (vectorCoeff_gramMatrix ω a b).2.1
  have h2 := (vectorCoeff_gramMatrix ω a (-b)).2.1
  have hb : ω⟨⁅a, -b⁆⟩ = -ω⟨⁅a, b⁆⟩ := by
    rw [← map_neg]
    congr 1
    apply Subtype.ext
    rw [selfAdjoint.coe_bracket, NegMemClass.coe_neg, NegMemClass.coe_neg, selfAdjoint.coe_bracket,
      ← smul_neg]
    congr 1
    noncomm_ring
  change PauliMatrix.vectorCoeff _ 1 + PauliMatrix.vectorCoeff _ 1 = 0
  rw [h1, h2, hb]
  ring

/-- **The round trip pays twice.** The way there and the way back together carry at least twice
the proper time of one way. -/
theorem two_mul_properTime_le_round_trip :
    2 * SpaceTime.properTime 0 (uncertaintyVector ω a b) ≤
      SpaceTime.properTime 0 (uncertaintyVector ω a b + uncertaintyVector ω a (-b)) := by
  have h := Lorentz.Vector.sqrt_add_sqrt_le_sqrt_add_of_causallyFollows
    (causallyFollows_uncertaintyVector ω a b) (causallyFollows_uncertaintyVector ω a (-b))
  have hn := properTime_uncertaintyVector_neg_right ω a b
  simp only [SpaceTime.properTime, sub_zero] at h hn ⊢
  rw [two_mul]
  nth_rewrite 2 [← hn]
  exact h

end UnitalPositiveLinearMap
end ProbabilisticTheory

namespace CondensedMatter
namespace TightBindingChain

open ProbabilisticTheory UnitalPositiveLinearMap

variable (T : TightBindingChain)

/-!

## C. The open tight binding chain

-/

/-- **The round trip of the chain.** From four sites on, in the maximal current state, the way
there and back along the reflected position carries positive proper time. -/
theorem round_trip_maxCurrentState_pos (ht : T.t ≠ 0) (hN : 4 ≤ T.N) :
    0 < SpaceTime.properTime 0
      (uncertaintyVector T.maxCurrentVectorState T.openHamiltonianObservable
          T.positionObservable +
        uncertaintyVector T.maxCurrentVectorState T.openHamiltonianObservable
          (-T.positionObservable)) := by
  have h := two_mul_properTime_le_round_trip T.maxCurrentVectorState
    T.openHamiltonianObservable T.positionObservable
  have hp := T.properTime_maxCurrentState_pos ht hN
  rw [energyPositionVector] at hp
  linarith

end TightBindingChain
end CondensedMatter
