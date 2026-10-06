/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.OpenBoundary
/-!

# The long bonds across a cut of the open tight binding chain

## i. Overview

Cut the open chain between the sites `c` and `c + 1`. A bond `(m, n)` crosses the cut when
`m ≤ c < n`. The open Hamiltonian hops only between neighbours, so of the `(c + 1)(N - 1 - c)`
bonds across the cut exactly one, `(c, c + 1)`, carries a hopping. The other
`(c + 1)(N - 1 - c) - 1` have range at least two; the open Hamiltonian has no matrix element
on any of them.

## ii. Key results

- `cutBonds` : the bonds of range at least two across the cut after the site `c`.
- `inner_openHamiltonian_of_mem_cutBonds` : the open Hamiltonian vanishes on them.
- `card_cutBonds` : there are `(c + 1)(N - 1 - c) - 1` of them.

## iii. Table of contents

- A. The bonds across a cut
- B. Their number

## iv. References

* https://www.damtp.cam.ac.uk/user/tong/aqm/aqmtwo.pdf. [ref: tong_statistical_physics]

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain

open InnerProductSpace

variable (T : TightBindingChain)

/-!

## A. The bonds across a cut

-/

/-- The bonds `(m, n)` of range at least two across the cut after the site `c`:
  `m ≤ c < n` and `m + 2 ≤ n`. -/
def cutBonds (c : ℕ) : Finset (Fin T.N × Fin T.N) :=
  Finset.univ.filter fun p => (p.1 : ℕ) ≤ c ∧ c < p.2 ∧ (p.1 : ℕ) + 2 ≤ p.2

lemma mem_cutBonds {c : ℕ} {p : Fin T.N × Fin T.N} :
    p ∈ T.cutBonds c ↔ (p.1 : ℕ) ≤ c ∧ c < p.2 ∧ (p.1 : ℕ) + 2 ≤ p.2 := by
  simp [cutBonds]

/-- The open Hamiltonian has no matrix element on a bond across the cut of range at least
  two. -/
lemma inner_openHamiltonian_of_mem_cutBonds {c : ℕ} {p : Fin T.N × Fin T.N}
    (hp : p ∈ T.cutBonds c) : ⟪|p.1⟩, T.openHamiltonian |p.2⟩⟫_ℂ = 0 := by
  rw [mem_cutBonds] at hp
  have h1 : p.1 ≠ p.2 := fun h => by rw [h] at hp; omega
  have h2 : ¬((p.1 : ℕ) + 1 = p.2 ∨ (p.2 : ℕ) + 1 = p.1) := by omega
  rw [inner_openHamiltonian]
  simp [h1, h2]

/-!

## B. Their number

-/

/-- The sites at or before `c` number `c + 1`. -/
lemma card_sites_le (c : ℕ) (hc : c < T.N) :
    (Finset.univ.filter fun m : Fin T.N => (m : ℕ) ≤ c).card = c + 1 := by
  simp_rw [← Nat.lt_succ_iff]
  rw [Fin.card_filter_val_lt]
  omega

/-- The sites after `c` number `N - 1 - c`. -/
lemma card_sites_gt (c : ℕ) :
    (Finset.univ.filter fun n : Fin T.N => c < (n : ℕ)).card = T.N - 1 - c := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun n : Fin T.N => (n : ℕ) < c + 1)
  simp only [not_lt, Nat.succ_le_iff, Finset.card_univ, Fintype.card_fin] at h
  rw [Fin.card_filter_val_lt] at h
  omega

/-- **The number of long bonds across the cut** after the site `c`, for `c + 1 < N`:
  `(c + 1)(N - 1 - c) - 1`. -/
lemma card_cutBonds {c : ℕ} (hc : c + 1 < T.N) :
    (T.cutBonds c).card = (c + 1) * (T.N - 1 - c) - 1 := by
  set L := Finset.univ.filter fun m : Fin T.N => (m : ℕ) ≤ c
  set R := Finset.univ.filter fun n : Fin T.N => c < (n : ℕ)
  have hp : ((⟨c, by omega⟩ : Fin T.N), (⟨c + 1, hc⟩ : Fin T.N)) ∈ L ×ˢ R := by
    simp [L, R]
  have h : T.cutBonds c = (L ×ˢ R).erase (⟨c, by omega⟩, ⟨c + 1, hc⟩) := by
    ext ⟨m, n⟩
    simp only [mem_cutBonds, Finset.mem_erase, Finset.mem_product, L, R, Finset.mem_filter,
      Finset.mem_univ, true_and, ne_eq, Prod.mk.injEq, Fin.ext_iff]
    omega
  rw [h, Finset.card_erase_of_mem hp, Finset.card_product, T.card_sites_le c (by omega),
    T.card_sites_gt]

end TightBindingChain
end CondensedMatter
