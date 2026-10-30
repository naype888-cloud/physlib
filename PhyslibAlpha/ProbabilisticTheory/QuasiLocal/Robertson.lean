/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.ProbabilisticTheory.QuasiLocal.Limit
public import PhyslibAlpha.ProbabilisticTheory.StarAlgebra.StateUncertainty

/-!

# Robertson's relation in the limit of a net of local states

## i. Overview

Let `ω Λ` be a state of the algebra of each finite region `Λ`, and let `ω∞` be the limit state of
the quasi-local algebra along a fine ultrafilter (`QuasiLocal.limitState`). Robertson's relation
holds for `ω∞` because it holds for every state (`AlgState.robertson_det`). Moreover the matrices
`Σ` and `Ω` of local observables in the limit state are the limits of the local ones, so the
relation is not lost in the passage to the infinite system: it is the limit of the relations of
the finite regions.

## ii. Key results

- `QuasiLocal.limitState_robertson_det` : `|det Ω| ≤ det Σ` in the limit state.
- `QuasiLocal.tendsto_covariance_local` : the covariance of two local observables in `ω Λ`
  tends to their covariance in the limit state.
- `QuasiLocal.tendsto_bracket_local` : the same for the expectation of the bracket.

## iii. Table of contents

- A. Robertson in the limit state
- B. Covariance and bracket are continuous along the net

## iv. References

-/

@[expose] public section

namespace ProbabilisticTheory

open Filter Topology

namespace QuasiLocal

variable {S : Type*} [DecidableEq S] {N : AlgebraNet S}

/-! ## A. Robertson in the limit state -/

variable (ω : ∀ Λ : Finset S, AlgState (N.A Λ)) {𝒰 : Ultrafilter (Finset S)}
  (hb : N.IsLocallyBounded) (h𝒰 : (𝒰 : Filter (Finset S)) ≤ atTop)

/-- **Robertson's relation in the limit state**, for any finite family of observables of the
quasi-local algebra. -/
lemma limitState_robertson_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → selfAdjoint N.Quasilocal) :
    |((limitState ω hb h𝒰).bracketMatrix a).det| ≤ ((limitState ω hb h𝒰).covarianceMatrix a).det :=
  (limitState ω hb h𝒰).robertson_det a

/-! ## B. Covariance and bracket are continuous along the net -/

/-- A self-adjoint local observable, included in a larger region. -/
def inclSA {X Λ : Finset S} (h : X ≤ Λ) (a : selfAdjoint (N.A X)) : selfAdjoint (N.A Λ) :=
  ⟨N.incl h a, selfAdjoint.mem_iff.mpr (by rw [← map_star, selfAdjoint.mem_iff.mp a.2])⟩

/-- A self-adjoint local observable, as an observable of the quasi-local algebra. -/
noncomputable def ofSA (X : Finset S) (a : selfAdjoint (N.A X)) : selfAdjoint N.Quasilocal :=
  ⟨N.of X a, selfAdjoint.mem_iff.mpr (by rw [← map_star, selfAdjoint.mem_iff.mp a.2])⟩

/-- The covariance of two local observables in the local state of `Λ`, zero if `Λ` does not
contain the region. -/
noncomputable def localCov (X : Finset S) (a b : selfAdjoint (N.A X)) (Λ : Finset S) : ℝ :=
  if h : X ≤ Λ then (ω Λ).covariance (inclSA h a) (inclSA h b) else 0

/-- The expectation of the bracket of two local observables in the local state of `Λ`. -/
noncomputable def localBracket (X : Finset S) (a b : selfAdjoint (N.A X)) (Λ : Finset S) : ℝ :=
  if h : X ≤ Λ then (ω Λ).bracket (inclSA h a) (inclSA h b) else 0

/-- **The covariance of local observables in the limit state is the limit of the local
covariances.** -/
lemma tendsto_covariance_local (X : Finset S) (a b : selfAdjoint (N.A X)) :
    Tendsto (localCov ω X a b) 𝒰
      (𝓝 ((limitState ω hb h𝒰).covariance (ofSA X a) (ofSA X b))) := by
  have hab := limitState_of ω hb h𝒰 X ((a : N.A X) * b)
  have ha := limitState_of ω hb h𝒰 X (a : N.A X)
  have hb' := limitState_of ω hb h𝒰 X (b : N.A X)
  have h := (Complex.continuous_re.tendsto _).comp (hab.sub (ha.mul hb'))
  rw [AlgState.covariance, AlgState.apply_fluctuation_mul]
  change Tendsto _ _ (𝓝 ((limitState ω hb h𝒰 ((N.of X a) * (N.of X b)) -
    limitState ω hb h𝒰 (N.of X a) * limitState ω hb h𝒰 (N.of X b)).re))
  rw [← map_mul]
  refine h.congr' ?_
  filter_upwards [h𝒰 (eventually_ge_atTop X)] with Λ hΛ
  simp only [Function.comp_apply, localCov, hΛ, dite_true, AlgState.covariance,
    AlgState.apply_fluctuation_mul, localSeq_eq ω X _ hΛ, inclSA, map_mul]

/-- **The expectation of the bracket of local observables in the limit state is the limit of the
local ones.** -/
lemma tendsto_bracket_local (X : Finset S) (a b : selfAdjoint (N.A X)) :
    Tendsto (localBracket ω X a b) 𝒰
      (𝓝 ((limitState ω hb h𝒰).bracket (ofSA X a) (ofSA X b))) := by
  have h := (Complex.continuous_re.tendsto _).comp
    (limitState_of ω hb h𝒰 X ((-(Complex.I / 2)) • ((a : N.A X) * b - b * a)))
  rw [AlgState.bracket, selfAdjoint.coe_bracket]
  change Tendsto _ _ (𝓝 ((limitState ω hb h𝒰 ((-(Complex.I / 2)) •
    ((N.of X a) * (N.of X b) - (N.of X b) * (N.of X a)))).re))
  rw [← map_mul, ← map_mul, ← map_sub, ← map_smul]
  refine h.congr' ?_
  filter_upwards [h𝒰 (eventually_ge_atTop X)] with Λ hΛ
  simp only [Function.comp_apply, localBracket, hΛ, dite_true, AlgState.bracket,
    selfAdjoint.coe_bracket, localSeq_eq ω X _ hΛ, inclSA, map_sub, map_mul, map_smul]

end QuasiLocal

end ProbabilisticTheory
