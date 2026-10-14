/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.MaxCurrentState.FluctuationAngle
/-!

# A positive lower bound for the fluctuation angle

## i. Overview

The fluctuation angle `θ = arccos (1 / C)` of the maximal current state depends only on the
number of sites `N`, not on the spacing `a` nor on the hopping `t`. From four sites on it opens
and grows strictly with `N`. Hence the four site value bounds every chain from below: whatever
its size and its scale, no chain with at least four sites gets below `θ(4) > 0`.

In particular the saturated value `θ = 0`, which a constant commutator `[X, P] = iħ` allows, is
not the limit of any family of chains with at least four sites: growing the chain moves the
angle away from `0`, never towards it.

## ii. Key results

- `fluctuationAngle_eq_fluctuationAngle` : the angle depends only on the number of sites.
- `exists_le_fluctuationAngle` : a positive lower bound for the angle of every chain with
  `N ≥ 4`.
- `not_tendsto_fluctuationAngle_zero` : no family of chains with `N ≥ 4` has angle tending to
  `0`.

## iii. Table of contents

- A. The angle depends only on `N`
- B. The lower bound

## iv. References

* W. Heisenberg, *Über den anschaulichen Inhalt der quantentheoretischen Kinematik und
  Mechanik*, Z. Phys. 43 (1927) 172.
* H. P. Robertson, *A general formulation of the uncertainty principle and its classical
  interpretation*, Phys. Rev. 35 (1930) 667.
* F. Mercati and M. Sergola, *Pauli–Jordan function and scalar field quantization in
  κ-Minkowski noncommutative spacetime*, Phys. Rev. D 98 (2018) 045017.
* E. J. Thompson, *On the Limits of a Space-Time Description and the Physical Meaning of Phase
  Space in a Nonlocal Continuum*, arXiv:2606.27387.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open Filter Topology

/-!

## A. The angle depends only on `N`

-/

/-- Two chains with the same number of sites have the same fluctuation angle, whatever `a` and
`t`. -/
lemma fluctuationAngle_eq_fluctuationAngle {T T' : TightBindingChain} (ht : T.t ≠ 0)
    (ht' : T'.t ≠ 0) (hN : 2 ≤ T.N) (hNN' : T.N = T'.N) :
    T.fluctuationAngle = T'.fluctuationAngle := by
  have hN' : 2 ≤ T'.N := hNN' ▸ hN
  have hC : T.uncertaintyRatio = T'.uncertaintyRatio := by
    refine (pow_left_inj₀ (zero_le_one.trans (T.one_le_uncertaintyRatio ht hN))
      (zero_le_one.trans (T'.one_le_uncertaintyRatio ht' hN')) two_ne_zero).mp ?_
    rw [T.uncertaintyRatio_sq_eq_uncertaintyRatioSqForm ht hN,
      T'.uncertaintyRatio_sq_eq_uncertaintyRatioSqForm ht' hN', hNN']
  rw [T.fluctuationAngle_eq ht hN, T'.fluctuationAngle_eq ht' hN', hC]

/-!

## B. The lower bound

-/

/-- **A positive lower bound for the fluctuation angle.** The fluctuation angle of every chain
with at least four sites, of any size and any scale, is at least the four site value
`θ(4) > 0`. -/
lemma exists_le_fluctuationAngle :
    ∃ θ₀ > 0, ∀ T : TightBindingChain, T.t ≠ 0 → 4 ≤ T.N → θ₀ ≤ T.fluctuationAngle := by
  let T₄ : TightBindingChain := { N := 4, a := 1, a_pos := one_pos, E0 := 0, t := 1 }
  have ht₄ : T₄.t ≠ 0 := one_ne_zero
  have hN₄ : T₄.N = 4 := rfl
  refine ⟨T₄.fluctuationAngle, T₄.fluctuationAngle_pos ht₄ hN₄.ge, fun T ht hN => ?_⟩
  rcases hN.eq_or_lt with h | h
  · exact (fluctuationAngle_eq_fluctuationAngle ht₄ ht (by omega) (hN₄.trans h)).le
  · exact (fluctuationAngle_lt_fluctuationAngle ht₄ ht hN₄.ge (hN₄ ▸ h)).le

/-- **The saturated angle is not a limit of chains.** Along any nontrivial filter, no family of
chains with at least four sites has fluctuation angle tending to `0`. -/
lemma not_tendsto_fluctuationAngle_zero {ι : Type*} {l : Filter ι} [l.NeBot]
    (T : ι → TightBindingChain) (ht : ∀ i, (T i).t ≠ 0) (hN : ∀ i, 4 ≤ (T i).N) :
    ¬ Tendsto (fun i => (T i).fluctuationAngle) l (𝓝 0) := fun h => by
  obtain ⟨θ₀, hθ₀, hbound⟩ := exists_le_fluctuationAngle
  obtain ⟨i, hi⟩ := (h.eventually (gt_mem_nhds hθ₀)).exists
  exact (hbound (T i) (ht i) (hN i)).not_gt hi

end TightBindingChain
end CondensedMatter
