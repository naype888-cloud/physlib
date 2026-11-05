/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.Cube.Basic
public import PhyslibAlpha.ProbabilisticTheory.CStarAlgebra.StateOrderUncertainty

/-!

# Robertson's relation on the cube for `AlgState`

## i. Overview

`robertson_det_cube` is stated for the states `𝓢[ℂ, A]` of the algebra of operators of the cube.
The translation invariant states of a crystal are `AlgState`s. On the cube, the algebra of
operators is a C⋆-algebra with its star order, so an `AlgState` is a state `𝓢[ℂ, A]`
(`AlgState.toState`) with the same covariance matrix and the same brackets, and the relation holds
for it with the matrices of `AlgState`.

## ii. Key results

- `axisBracket_toState` : the bracket of the pair of an axis in the state of an `AlgState`.
- `robertson_det_cube_algState` : Robertson's relation for the six observables of the cube in
  every `AlgState`.

## iii. Table of contents

- A. Robertson's relation for `AlgState`

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open scoped ComplexOrder selfAdjoint
open ProbabilisticTheory

variable (Tx Ty Tz : TightBindingChain)

/-!

## A. Robertson's relation for `AlgState`

-/

/-- The bracket of the pair of an axis is the expectation of the bracket in the `AlgState`. -/
lemma axisBracket_toState (ω : AlgState (Tx.CubeOperators Ty Tz)) (k : Fin 3) :
    Tx.axisBracket Ty Tz ω.toState k =
      ω.bracket (Tx.cubePairs Ty Tz (0, k)) (Tx.cubePairs Ty Tz (1, k)) := by
  rw [← AlgState.ofState_toState ω]
  exact (UnitalPositiveLinearMap.bracket_ofState _ _ _).symm

/-- **Robertson's relation on the cube for an `AlgState`.** The volume `det Σ` of the dispersion
of the six observables is at least the product of the squared brackets of the three axes. -/
lemma robertson_det_cube_algState (ω : AlgState (Tx.CubeOperators Ty Tz)) :
    (ω.bracket (Tx.cubePairs Ty Tz (0, 0)) (Tx.cubePairs Ty Tz (1, 0)) *
      ω.bracket (Tx.cubePairs Ty Tz (0, 1)) (Tx.cubePairs Ty Tz (1, 1)) *
      ω.bracket (Tx.cubePairs Ty Tz (0, 2)) (Tx.cubePairs Ty Tz (1, 2))) ^ 2 ≤
      (ω.covarianceMatrix (Tx.cubePairs Ty Tz)).det := by
  have h := Tx.robertson_det_cube Ty Tz ω.toState
  rw [axisBracket_toState, axisBracket_toState, axisBracket_toState] at h
  rwa [← UnitalPositiveLinearMap.covarianceMatrix_ofState, AlgState.ofState_toState] at h

end TightBindingChain
end CondensedMatter
