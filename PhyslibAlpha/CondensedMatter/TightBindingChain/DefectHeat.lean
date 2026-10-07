/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.CutBonds
public import PhyslibAlpha.CondensedMatter.TightBindingChain.VolumetricQuantum
public import PhyslibAlpha.StatisticalMechanics.Landauer
public import QuantumInfo.States.Entanglement
/-!

# The heat of the quantum defect

## i. Overview

Each quantum of the open tight binding chain carries the dimensional quantum `δ = C_Nava - 1`, so
`k` quanta carry the defect `Ω = k δ`. It vanishes for `N = 2, 3`, below the rupture, and is
positive from four sites on.

Place `k` quanta on the `M` long bonds across a cut: there are `W = M^k` configurations, and their
entropy is `S = log W = k log M`, a count of bonds across the cut. From four sites on it is
proportional to the defect, `S = (log M / δ) Ω`.

Landauer's principle prices that entropy. Erasing the configuration, by driving the uniform
mixture of all `W` configurations to a pure state with a unitary interaction with a reservoir at
temperature `T`, releases into the reservoir a heat of at least `k_B T S`. From four sites on
this is `k_B T (log M / δ) Ω`: the heat is proportional to the defect.

## ii. Key results

- `quantumDefect` : the defect `k δ` of `k` quanta.
- `quantumDefect_eq_zero_of_N`, `quantumDefect_pos` : zero for `N = 2, 3`, positive from four
  sites on.
- `CutConfig`, `cutEntropy` : the configurations of `k` quanta across a cut and their entropy.
- `cutEntropy_eq_mul_quantumDefect` : `S = (log M / δ) Ω` from four sites on.
- `landauer_cutEntropy` : erasing the configurations releases a heat of at least `k_B T S`.
- `landauer_quantumDefect` : from four sites on, at least `k_B T (log M / δ) Ω`.

## iii. Table of contents

- A. The quantum defect
- B. The entropy of the quanta across a cut
- C. The heat of the defect

## iv. References

* L. Boltzmann, *Über die Beziehung zwischen dem zweiten Hauptsatze der mechanischen
  Wärmetheorie und der Wahrscheinlichkeitsrechnung*, Wien. Ber. 76 (1877) 373.
* R. Landauer, *Irreversibility and heat generation in the computing process*,
  IBM J. Res. Dev. 5 (1961).

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain

open Constants MState
open scoped InnerProductSpace RealInnerProductSpace

variable (T : TightBindingChain)

/-!

## A. The quantum defect

-/

/-- The defect `k δ` of `k` quanta of the chain. -/
noncomputable def quantumDefect (k : ℕ) : ℝ := k * T.dimQuantum

/-- Below the rupture, `N = 2, 3`, the quanta carry no defect. -/
lemma quantumDefect_eq_zero_of_N (ht : T.t ≠ 0) (hN : T.N = 2 ∨ T.N = 3) (k : ℕ) :
    T.quantumDefect k = 0 := by
  rw [quantumDefect, (T.dimQuantum_eq_zero_iff ht (by omega)).mpr hN, mul_zero]

/-- From four sites on, `k ≥ 1` quanta carry a positive defect. -/
lemma quantumDefect_pos (ht : T.t ≠ 0) (hN : 4 ≤ T.N) {k : ℕ} (hk : 1 ≤ k) :
    0 < T.quantumDefect k :=
  mul_pos (by exact_mod_cast hk) (T.dimQuantum_pos ht hN)

/-!

## B. The entropy of the quanta across a cut

-/

/-- The configurations of `k` quanta on the long bonds across the cut after site `c`. -/
abbrev CutConfig (c k : ℕ) : Type := Fin k → T.cutBonds c

/-- The entropy `k log M` of `k` quanta on the `M` long bonds across a cut. -/
noncomputable def cutEntropy (c k : ℕ) : ℝ := k * Real.log (T.cutBonds c).card

/-- The entropy counts the configurations: `S = log W` with `W = M^k`. -/
lemma cutEntropy_eq_log_card (c k : ℕ) :
    T.cutEntropy c k = Real.log (Fintype.card (T.CutConfig c k)) := by
  rw [cutEntropy, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow,
    Real.log_pow]

/-- **The entropy is proportional to the defect.** From four sites on,
`S = (log M / δ) Ω`. -/
theorem cutEntropy_eq_mul_quantumDefect (ht : T.t ≠ 0) (hN : 4 ≤ T.N) (c k : ℕ) :
    T.cutEntropy c k = Real.log (T.cutBonds c).card / T.dimQuantum * T.quantumDefect k := by
  rw [cutEntropy, quantumDefect]
  field_simp [(T.dimQuantum_pos ht hN).ne']

/-!

## C. The heat of the defect

-/

variable {dR : Type*} [Fintype dR] [DecidableEq dR] [Nonempty dR]

/-- **Landauer's principle for the quanta across a cut.** A unitary interaction with a reservoir
at temperature `θ` that drives the uniform mixture of the `M^k` configurations to a pure state
releases into the reservoir a heat of at least `k_B θ S`. -/
theorem landauer_cutEntropy {c k : ℕ} [Nonempty (T.CutConfig c k)] (θ : Temperature)
    (hθ : 0 < θ.val) (H : HermitianMat dR ℂ) (U : 𝐔[T.CutConfig c k × dR])
    (hpure : Sᵥₙ ((uniform ⊗ᴹ thermalState θ H).uConj U).traceRight = 0) :
    kB * θ * T.cutEntropy c k ≤
      ⟪((uniform ⊗ᴹ thermalState θ H).uConj U).traceLeft.M, H⟫ -
        ⟪(thermalState θ H).M, H⟫ := by
  have hS : Sᵥₙ (uniform : MState (T.CutConfig c k)) = T.cutEntropy c k := by
    rw [uniform, Sᵥₙ_ofClassical, Hₛ_uniform, Finset.card_univ, cutEntropy_eq_log_card]
  have h := landauer_temperature (uniform : MState (T.CutConfig c k)) θ hθ H U
  rwa [hpure, sub_zero, hS] at h

/-- **The heat of the defect.** From four sites on, erasing the quanta across a cut releases a
heat of at least `k_B θ (log M / δ) Ω`: proportional to the defect. -/
theorem landauer_quantumDefect (ht : T.t ≠ 0) (hN : 4 ≤ T.N) {c k : ℕ}
    [Nonempty (T.CutConfig c k)] (θ : Temperature) (hθ : 0 < θ.val) (H : HermitianMat dR ℂ)
    (U : 𝐔[T.CutConfig c k × dR])
    (hpure : Sᵥₙ ((uniform ⊗ᴹ thermalState θ H).uConj U).traceRight = 0) :
    kB * θ * (Real.log (T.cutBonds c).card / T.dimQuantum * T.quantumDefect k) ≤
      ⟪((uniform ⊗ᴹ thermalState θ H).uConj U).traceLeft.M, H⟫ -
        ⟪(thermalState θ H).M, H⟫ := by
  rw [← T.cutEntropy_eq_mul_quantumDefect ht hN]
  exact T.landauer_cutEntropy θ hθ H U hpure

end TightBindingChain
end CondensedMatter
