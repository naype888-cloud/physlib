/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.StatisticalMechanics.Carnot
/-!

# The end of the count: the Gibbs state

## i. Overview

A finite system has at most `log d` of entropy to count. The Gibbs state `γ = exp (-β H) / Z`
holds the most entropy that its mean energy allows: every state with the same mean energy has
at most as much. It is also passive: no unitary evolution lowers its mean energy, so no work can
be extracted from it (Kelvin–Planck). Once a system has reached it, there is nothing left to
count and nothing left to extract.

## ii. Key results

- `Sᵥₙ_le_Sᵥₙ_gibbsState` : at equal mean energy, the Gibbs state has the most entropy.
- `Sᵥₙ_gibbsState_le_log` : its entropy is at most `log d`.
- `gibbsState_end_of_count` : the Gibbs state maximizes the entropy at its mean energy, holds at
  most `log d`, and is passive.

## iii. Table of contents

- A. The most entropy at fixed energy
- B. The end of the count

## iv. References

* J. W. Gibbs, *Elementary principles in statistical mechanics*, Scribner (1902).
* J. von Neumann, *Mathematische Grundlagen der Quantenmechanik*, Springer (1932).

-/

@[expose] public section

namespace MState

open scoped InnerProductSpace RealInnerProductSpace
open HermitianMat

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-!

## A. The most entropy at fixed energy

-/

/-- At equal mean energy, the Gibbs state has the most entropy. -/
lemma Sᵥₙ_le_Sᵥₙ_gibbsState (β : ℝ) (H : HermitianMat d ℂ) (σ : MState d)
    (hσ : ⟪σ.M, H⟫ = ⟪(gibbsState β H).M, H⟫) : Sᵥₙ σ ≤ Sᵥₙ (gibbsState β H) := by
  rw [Sᵥₙ_gibbsState, ← hσ]
  exact Sᵥₙ_le_gibbs σ β H

/-- The entropy of the Gibbs state is at most `log d`. -/
lemma Sᵥₙ_gibbsState_le_log (β : ℝ) (H : HermitianMat d ℂ) :
    Sᵥₙ (gibbsState β H) ≤ Real.log (Fintype.card d) := by
  simpa using Sᵥₙ_le_log_d (gibbsState β H)

/-!

## B. The end of the count

-/

/-- **The end of the count.** The Gibbs state at positive inverse temperature holds the most
entropy its mean energy allows, at most `log d`, and is passive: no unitary evolution lowers its
mean energy. -/
theorem gibbsState_end_of_count {β : ℝ} (hβ : 0 < β) (H : HermitianMat d ℂ) :
    (∀ σ : MState d, ⟪σ.M, H⟫ = ⟪(gibbsState β H).M, H⟫ →
        Sᵥₙ σ ≤ Sᵥₙ (gibbsState β H)) ∧
      Sᵥₙ (gibbsState β H) ≤ Real.log (Fintype.card d) ∧
      ∀ U : 𝐔[d], ⟪(gibbsState β H).M, H⟫ ≤ ⟪((gibbsState β H).uConj U).M, H⟫ :=
  ⟨Sᵥₙ_le_Sᵥₙ_gibbsState β H, Sᵥₙ_gibbsState_le_log β H, inner_gibbsState_le_uConj hβ H⟩

end MState
