/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.DefectHeat
/-!

# The entropy of the paths at the speed limit

## i. Overview

On the cube a path at the speed limit takes one step per unit of time, each along one axis,
always forward: in `k = a + b + c` steps it reaches the edge of the light cone, the octahedron
`|Δx| + |Δy| + |Δz| = k`, with `a`, `b`, `c` steps along `x`, `y`, `z`. Such a path is the
choice of which `a` of the `k` steps go along `x` and which `b` of the remaining go along `y`:
there are `C(k, a) C(k - a, b)` of them, the multinomial coefficient.

Along one axis there is exactly one such path, and its path entropy is zero. As soon as two axes
move there are at least two, and the path entropy is positive, even at the speed limit. By
Landauer's principle, erasing the record of which path was taken releases into a reservoir a
heat of at least `k_B T` times that entropy.

## ii. Key results

- `LightPath` : the paths at the speed limit with `a`, `b`, `c` steps along the three axes.
- `card_lightPath` : there are `C(a + b + c, a) C(b + c, b)` of them.
- `card_lightPath_axis` : along one axis there is exactly one.
- `one_lt_card_lightPath` : as soon as two axes move there are at least two.
- `pathEntropy_pos` : the path entropy is then positive.
- `landauer_pathEntropy` : erasing which path was taken costs at least `k_B T` times it.

## iii. Table of contents

- A. The paths at the speed limit
- B. The path entropy and its heat

## iv. References

* L. Szilard, *Über die Entropieverminderung in einem thermodynamischen System bei Eingriffen
  intelligenter Wesen*, Z. Phys. 53 (1929) 840.
* R. Landauer, *Irreversibility and heat generation in the computing process*,
  IBM J. Res. Dev. 5 (1961).

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain

open Constants MState
open scoped InnerProductSpace RealInnerProductSpace

/-!

## A. The paths at the speed limit

-/

/-- The paths at the speed limit on the cube with `a`, `b`, `c` steps along `x`, `y`, `z`: the
set of steps along `x`, and, among the remaining ones, the set of steps along `y`. -/
abbrev LightPath (a b c : ℕ) : Type :=
  (X : Finset.powersetCard a (Finset.univ : Finset (Fin (a + b + c)))) ×
    Finset.powersetCard b (X.1ᶜ)

/-- **The multinomial count.** There are `C(a + b + c, a) C(b + c, b)` paths at the speed
limit. -/
lemma card_lightPath (a b c : ℕ) :
    Fintype.card (LightPath a b c) = (a + b + c).choose a * (b + c).choose b := by
  rw [Fintype.card_sigma]
  have h (X : Finset.powersetCard a (Finset.univ : Finset (Fin (a + b + c)))) :
      Fintype.card (Finset.powersetCard b (X.1ᶜ)) = (b + c).choose b := by
    rw [Fintype.card_coe, Finset.card_powersetCard, Finset.card_compl, Fintype.card_fin,
      (Finset.mem_powersetCard.mp X.2).2]
    congr 1
    omega
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_coe, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- Along one axis there is exactly one path at the speed limit. -/
lemma card_lightPath_axis (a : ℕ) : Fintype.card (LightPath a 0 0) = 1 := by
  rw [card_lightPath]
  simp

private lemma two_le_choose {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) : 2 ≤ n.choose k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.choose_succ_succ']
  have := Nat.choose_pos (show j ≤ m by omega)
  have := Nat.choose_pos (show j + 1 ≤ m by omega)
  omega

/-- **As soon as two axes move, there are at least two paths at the speed limit.** -/
lemma one_lt_card_lightPath {a b c : ℕ} (h : (1 ≤ a ∧ 1 ≤ b + c) ∨ (1 ≤ b ∧ 1 ≤ c)) :
    1 < Fintype.card (LightPath a b c) := by
  rw [card_lightPath]
  have h1 := Nat.choose_pos (show a ≤ a + b + c by omega)
  have h2 := Nat.choose_pos (show b ≤ b + c by omega)
  rcases h with ⟨ha, hbc⟩ | ⟨hb, hc⟩
  · have := two_le_choose (n := a + b + c) ha (by omega)
    nlinarith
  · have := two_le_choose (n := b + c) hb (by omega)
    nlinarith

/-!

## B. The path entropy and its heat

-/

/-- The path entropy: the logarithm of the number of paths at the speed limit. -/
noncomputable def pathEntropy (a b c : ℕ) : ℝ := Real.log (Fintype.card (LightPath a b c))

/-- Along one axis the path entropy is zero. -/
lemma pathEntropy_axis (a : ℕ) : pathEntropy a 0 0 = 0 := by
  rw [pathEntropy, card_lightPath_axis, Nat.cast_one, Real.log_one]

/-- **Even at the speed limit, the path entropy is positive as soon as two axes move.** -/
theorem pathEntropy_pos {a b c : ℕ} (h : (1 ≤ a ∧ 1 ≤ b + c) ∨ (1 ≤ b ∧ 1 ≤ c)) :
    0 < pathEntropy a b c :=
  Real.log_pos (by exact_mod_cast one_lt_card_lightPath h)

variable {dR : Type*} [Fintype dR] [DecidableEq dR] [Nonempty dR]

/-- **The heat of the path.** A unitary interaction with a reservoir at temperature `θ` that
erases the record of which path was taken, from the uniform mixture of all paths at the speed
limit to a pure state, releases into the reservoir a heat of at least `k_B θ` times the path
entropy. -/
theorem landauer_pathEntropy {a b c : ℕ} [Nonempty (LightPath a b c)] (θ : Temperature)
    (hθ : 0 < θ.val) (H : HermitianMat dR ℂ) (U : 𝐔[LightPath a b c × dR])
    (hpure : Sᵥₙ ((uniform ⊗ᴹ thermalState θ H).uConj U).traceRight = 0) :
    kB * θ * pathEntropy a b c ≤
      ⟪((uniform ⊗ᴹ thermalState θ H).uConj U).traceLeft.M, H⟫ -
        ⟪(thermalState θ H).M, H⟫ := by
  have hS : Sᵥₙ (uniform : MState (LightPath a b c)) = pathEntropy a b c := by
    rw [uniform, Sᵥₙ_ofClassical, Hₛ_uniform, Finset.card_univ, pathEntropy]
  have h := landauer_temperature (uniform : MState (LightPath a b c)) θ hθ H U
  rwa [hpure, sub_zero, hS] at h

end TightBindingChain
end CondensedMatter
