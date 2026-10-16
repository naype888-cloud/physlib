/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.PointGroup.Sublattices

/-!

# The point groups of the diamond and honeycomb crystals

The point group of the diamond crystal has order forty-eight, and the point group of the
honeycomb crystal has order twelve.

## i. Overview

Both crystals have two sites `A` and `B` per cell, and every bond joins an `A` site to a `B` site.
The differences of the bonds at an `A` site are the twelve neighbours of the face-centred cubic
lattice for diamond, and the six neighbours of the triangular lattice for the honeycomb. By
`PeriodicGraph.pointGroupMulEquivOfLift` the point groups are those of these lattices, once two
finite checks are done. Only translations fix every cell direction. Every point operation of the
lattice lifts, either with the identity on the labels or with the exchange of `A` and `B`. For
diamond, the operations of the first kind form the tetrahedral group `-43m`, and those of the
second kind are its products with the inversion through the centre of a bond, which exchanges the
two sublattices. For the honeycomb the inversion through the centre of a bond and the reflections
in the bonds also exchange the two sublattices.

## ii. Key results

- `triangular_card_pointGroup` : the point group of the triangular lattice has order `12`.
- `diamondPointGroupMulEquiv` : the point group of diamond is that of the face-centred cubic
  lattice.
- `diamond_card_pointGroup` : order `48`.
- `honeycombPointGroupMulEquiv` : the point group of the honeycomb is that of the triangular
  lattice.
- `honeycomb_card_pointGroup` : order `12`.

## iii. Table of contents

- A. The triangular lattice
- B. Diamond
- C. Honeycomb

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapters 4 and 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

open PeriodicGraph

/-! ## A. The triangular lattice -/

/-- **The point group of the triangular lattice has order `12`.** -/
lemma triangular_card_pointGroup : Nat.card triangularGraph.pointGroup = 12 := by
  refine (card_pointGroup (N := bondNeighbors triangularBonds) ?_
    (bonded_ofBonds_unit triangularBonds)).trans ?_
  · intro j
    fin_cases j <;> decide
  · rw [Nat.card_congr (admissibleEquiv _), Nat.card_eq_fintype_card]
    decide +kernel

/-! ## B. Diamond -/

lemma diamond_bondDifferences : bondDifferences diamondBonds = bondNeighbors fccBonds := by
  decide +kernel

/-- Only translations of diamond fix every cell direction. -/
lemma diamond_mem_translations (s : CellSymmetry (Fin 3 → ℤ) DiamondLabel)
    (hs : s ∈ diamondGraph.symmetries) (hL : s.linear = AddEquiv.refl _) :
    s ∈ CellSymmetry.translations (Fin 3 → ℤ) DiamondLabel :=
  mem_translations_of_linear_eq .A (fun i => by cases i <;> decide) (by decide +kernel) s hs hL

/-- Every point operation of the face-centred cubic lattice lifts to a symmetry of diamond. -/
lemma diamond_lift : Function.Surjective (linearToLattice diamond_bondDifferences) :=
  lift_of_admissible diamond_bondDifferences (fun j => by fin_cases j <;> decide)
    (fun | .A => {0} | .B => {0, ![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![-1, 0, 0],
      ![0, -1, 0], ![0, 0, -1]}) (by decide +kernel)

/-- **The point group of diamond is the point group of the face-centred cubic lattice.** -/
noncomputable def diamondPointGroupMulEquiv : diamondGraph.pointGroup ≃* fccGraph.pointGroup :=
  pointGroupMulEquivOfLift diamond_bondDifferences diamond_mem_translations diamond_lift

/-- **The point group of diamond has order `48`.** -/
lemma diamond_card_pointGroup : Nat.card diamondGraph.pointGroup = 48 :=
  (Nat.card_congr diamondPointGroupMulEquiv.toEquiv).trans fcc_card_pointGroup

/-! ## C. Honeycomb -/

lemma honeycomb_bondDifferences :
    bondDifferences honeycombBonds = bondNeighbors triangularBonds := by
  decide +kernel

/-- **The point group of the honeycomb is the point group of the triangular lattice.** -/
noncomputable def honeycombPointGroupMulEquiv :
    honeycombGraph.pointGroup ≃* triangularGraph.pointGroup :=
  pointGroupMulEquivOfLift honeycomb_bondDifferences
    (mem_translations_of_linear_eq .A (fun i => by cases i <;> decide) (by decide +kernel))
    (lift_of_admissible honeycomb_bondDifferences (fun j => by fin_cases j <;> decide)
      (fun | .A => {0} | .B => {0, ![1, 0], ![0, 1], ![-1, 0], ![0, -1]}) (by decide +kernel))

/-- **The point group of the honeycomb has order `12`.** -/
lemma honeycomb_card_pointGroup : Nat.card honeycombGraph.pointGroup = 12 :=
  (Nat.card_congr honeycombPointGroupMulEquiv.toEquiv).trans triangular_card_pointGroup

end CondensedMatter.Crystal
