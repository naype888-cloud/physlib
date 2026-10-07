/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Data.Nat.Choose.Bounds
public import Physlib.Cosmology.FLRW.DeSitterHorizon
public import PhyslibAlpha.CondensedMatter.TightBindingChain.CutBonds
/-!

# The cosmological constant from a count of states

## i. Overview

`DeSitterHorizon` reads the cosmological constant `Λ = 3 π / (ℓ² S)` backwards from the entropy
`S` of the horizon. Here `S` is counted first, with no `Λ` in the input, and `Λ` comes out.

Cut the open tight binding chain after the site `c`. The bonds of range at least two across the
cut, on which the open Hamiltonian vanishes, number `M = (c + 1)(N - 1 - c) - 1`
(`card_cutBonds`). Placing `k` quanta, each on one of these `M` bonds, gives `W = Mᵏ`
configurations and the entropy `S = log W = k log M`. The constant `3 π / (ℓ² log W)` solves
both Friedmann equations with no matter, and its horizon has entropy exactly `log W`. It is
positive for every count, decreases strictly as the count grows and tends to `0`, a limit that
no finite count attains. If the quanta sit on distinct bonds, `S = log (M choose k) ≤ M log 2`,
and the count bounds the constant from below: `3 π / (ℓ² M log 2) ≤ Λ`.

## ii. Key results

- `cutEntropy` : the entropy `k log M` of `k` quanta on the bonds across the cut.
- `countCosmologicalConstant` : the constant `3 π / (ℓ² log W)` fixed by the count.
- `countCosmologicalConstant_eq` : `Λ = 3 π / (ℓ² k log ((c + 1)(N - 1 - c) - 1))`.
- `deSitterEntropy_countCosmologicalConstant` : its horizon has entropy `log W`.
- `countCosmologicalConstant_firstOrderFriedmann`,
  `countCosmologicalConstant_secondOrderFriedmann` : both Friedmann equations hold.
- `countCosmologicalConstant_strictAnti`, `countCosmologicalConstant_pos`,
  `tendsto_countCosmologicalConstant` : more quanta, a smaller positive `Λ`, tending to `0`.
- `le_simpleCountCosmologicalConstant` : on distinct bonds, `3 π / (ℓ² M log 2) ≤ Λ`.

## iii. Table of contents

- A. The entropy of the cut
- B. The constant counted
- C. Distinct bonds: the bound

## iv. References

* G. W. Gibbons and S. W. Hawking, *Cosmological event horizons, thermodynamics, and particle
  creation*, Phys. Rev. D 15 (1977) 2738.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain

open Real Time Topology Cosmology.FLRW.FriedmannEquation

variable (T : TightBindingChain)

/-!

## A. The entropy of the cut

-/

/-- The entropy `log W = k log M` of `k` quanta, each on one of the `M` bonds of range at least
two across the cut after the site `c`. -/
noncomputable def cutEntropy (c k : ℕ) : ℝ := k * Real.log (T.cutBonds c).card

lemma cutEntropy_eq {c : ℕ} (hc : c + 1 < T.N) (k : ℕ) :
    T.cutEntropy c k = k * Real.log (((c + 1) * (T.N - 1 - c) - 1 : ℕ) : ℝ) := by
  rw [cutEntropy, T.card_cutBonds hc]

/-- A cut with two sites on each side has at least three bonds across it. -/
lemma three_le_card_cutBonds {c : ℕ} (hc : 1 ≤ c) (hcN : c + 3 ≤ T.N) :
    3 ≤ (T.cutBonds c).card := by
  rw [T.card_cutBonds (by omega)]
  have : 2 * 2 ≤ (c + 1) * (T.N - 1 - c) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- The entropy of `k ≥ 1` quanta on a cut with at least two bonds is positive. -/
lemma cutEntropy_pos {c k : ℕ} (hk : 1 ≤ k) (hM : 2 ≤ (T.cutBonds c).card) :
    0 < T.cutEntropy c k :=
  mul_pos (by exact_mod_cast hk) (Real.log_pos (by exact_mod_cast hM))

/-!

## B. The constant counted

-/

/-- The cosmological constant fixed by the count `W = Mᵏ`: `3 π / (ℓ² log W)`. -/
noncomputable def countCosmologicalConstant (c k : ℕ) (ℓ : ℝ) : ℝ :=
  entropyCosmologicalConstant (T.cutEntropy c k) ℓ

/-- **The constant counted**: `Λ = 3 π / (ℓ² k log ((c + 1)(N - 1 - c) - 1))`. -/
theorem countCosmologicalConstant_eq {c : ℕ} (hc : c + 1 < T.N) (k : ℕ) (ℓ : ℝ) :
    T.countCosmologicalConstant c k ℓ =
      3 * π / (ℓ ^ 2 * (k * Real.log (((c + 1) * (T.N - 1 - c) - 1 : ℕ) : ℝ))) := by
  rw [countCosmologicalConstant, entropyCosmologicalConstant, T.cutEntropy_eq hc]

/-- The horizon of the counted constant has entropy exactly `log W`. -/
theorem deSitterEntropy_countCosmologicalConstant {c k : ℕ} {ℓ : ℝ} (hk : 1 ≤ k)
    (hM : 2 ≤ (T.cutBonds c).card) (hℓ : ℓ ≠ 0) :
    deSitterEntropy (T.countCosmologicalConstant c k ℓ) ℓ = T.cutEntropy c k :=
  deSitterEntropy_entropyCosmologicalConstant (T.cutEntropy_pos hk hM) hℓ

/-- The counted constant gives a de Sitter solution of the first Friedmann equation. -/
theorem countCosmologicalConstant_firstOrderFriedmann {c k : ℕ} {a₀ σ ℓ G c' : ℝ}
    (hk : 1 ≤ k) (hM : 2 ≤ (T.cutBonds c).card) (hℓ : ℓ ≠ 0) (ha₀ : a₀ ≠ 0)
    (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    FirstOrderFriedmann (deSitterScaleFactor a₀ σ (T.countCosmologicalConstant c k ℓ) c')
      (fun _ => 0) 0 (T.countCosmologicalConstant c k ℓ) G c' t :=
  entropyCosmologicalConstant_firstOrderFriedmann (T.cutEntropy_pos hk hM) hℓ ha₀ hσ t

/-- The counted constant gives a de Sitter solution of the second Friedmann equation. -/
theorem countCosmologicalConstant_secondOrderFriedmann {c k : ℕ} {a₀ σ ℓ G c' : ℝ}
    (hk : 1 ≤ k) (hM : 2 ≤ (T.cutBonds c).card) (hℓ : ℓ ≠ 0) (ha₀ : a₀ ≠ 0)
    (hσ : σ = 1 ∨ σ = -1) (t : Time) :
    SecondOrderFriedmann (deSitterScaleFactor a₀ σ (T.countCosmologicalConstant c k ℓ) c')
      (fun _ => 0) (fun _ => 0) (T.countCosmologicalConstant c k ℓ) G c' t :=
  entropyCosmologicalConstant_secondOrderFriedmann (T.cutEntropy_pos hk hM) hℓ ha₀ hσ t

/-- The counted constant is positive: a finite count never gives `Λ = 0`. -/
theorem countCosmologicalConstant_pos {c k : ℕ} {ℓ : ℝ} (hk : 1 ≤ k)
    (hM : 2 ≤ (T.cutBonds c).card) (hℓ : ℓ ≠ 0) : 0 < T.countCosmologicalConstant c k ℓ :=
  entropyCosmologicalConstant_pos (T.cutEntropy_pos hk hM) hℓ

/-- More quanta on the cut, a strictly smaller constant. -/
theorem countCosmologicalConstant_strictAnti {c k₁ k₂ : ℕ} {ℓ : ℝ} (hk : 1 ≤ k₁) (h : k₁ < k₂)
    (hM : 2 ≤ (T.cutBonds c).card) (hℓ : ℓ ≠ 0) :
    T.countCosmologicalConstant c k₂ ℓ < T.countCosmologicalConstant c k₁ ℓ := by
  refine entropyCosmologicalConstant_strictAntiOn hℓ (T.cutEntropy_pos hk hM)
    (T.cutEntropy_pos (hk.trans h.le) hM) ?_
  exact mul_lt_mul_of_pos_right (by exact_mod_cast h) (Real.log_pos (by exact_mod_cast hM))

/-- **`Λ → 0` as the count grows**, a limit that no finite count attains. -/
theorem tendsto_countCosmologicalConstant (c : ℕ) (ℓ : ℝ) :
    Filter.Tendsto (fun k : ℕ => T.countCosmologicalConstant c k ℓ) Filter.atTop (𝓝 0) := by
  have h : (fun k : ℕ => T.countCosmologicalConstant c k ℓ) =
      fun k : ℕ => 3 * π / (ℓ ^ 2 * Real.log (T.cutBonds c).card) * (k : ℝ)⁻¹ := by
    funext k
    rw [countCosmologicalConstant, entropyCosmologicalConstant, cutEntropy]
    ring
  rw [h]
  have := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
    (3 * π / (ℓ ^ 2 * Real.log (T.cutBonds c).card))
  rwa [mul_zero] at this

/-!

## C. Distinct bonds: the bound

-/

/-- The entropy `log (M choose k)` of `k` quanta on distinct bonds across the cut. -/
noncomputable def simpleCutEntropy (c k : ℕ) : ℝ := Real.log ((T.cutBonds c).card.choose k)

lemma simpleCutEntropy_pos {c k : ℕ} (hk : 1 ≤ k) (hkM : k < (T.cutBonds c).card) :
    0 < T.simpleCutEntropy c k := by
  have h : k + 1 ≤ (T.cutBonds c).card.choose k := by
    rw [← Nat.choose_succ_self_right]
    exact Nat.choose_le_choose k hkM
  exact Real.log_pos (by exact_mod_cast (show 1 < (T.cutBonds c).card.choose k by omega))

/-- On distinct bonds the entropy is at most `M log 2`. -/
lemma simpleCutEntropy_le {c k : ℕ} (hkM : k ≤ (T.cutBonds c).card) :
    T.simpleCutEntropy c k ≤ (T.cutBonds c).card * Real.log 2 := by
  rw [simpleCutEntropy, ← Real.log_pow]
  refine Real.log_le_log (by exact_mod_cast Nat.choose_pos hkM) ?_
  exact_mod_cast Nat.choose_le_two_pow _ _

/-- The cosmological constant fixed by `k` quanta on distinct bonds across the cut. -/
noncomputable def simpleCountCosmologicalConstant (c k : ℕ) (ℓ : ℝ) : ℝ :=
  entropyCosmologicalConstant (T.simpleCutEntropy c k) ℓ

/-- **The count bounds the constant from below**: `3 π / (ℓ² M log 2) ≤ Λ`. -/
theorem le_simpleCountCosmologicalConstant {c k : ℕ} {ℓ : ℝ} (hk : 1 ≤ k)
    (hkM : k < (T.cutBonds c).card) (hℓ : ℓ ≠ 0) :
    3 * π / (ℓ ^ 2 * ((T.cutBonds c).card * Real.log 2)) ≤
      T.simpleCountCosmologicalConstant c k ℓ := by
  have hS := T.simpleCutEntropy_pos hk hkM
  have hmax := T.simpleCutEntropy_le hkM.le
  rw [simpleCountCosmologicalConstant, entropyCosmologicalConstant]
  have hℓ2 : 0 < ℓ ^ 2 := by positivity
  gcongr

end TightBindingChain
end CondensedMatter
