/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.TightBindingChain.OpenBoundary
/-!

# The light cone of the open tight binding chain

## i. Overview

The open chain hops only between neighbouring sites. Counting time in applications of the
Hamiltonian, after `k` of them an amplitude has moved at most `k` sites: `⟨m| H^k |n⟩ = 0`
whenever `|m - n| > k`. This is the light cone of the chain, one site per step.

The front is reached on time: the site `k` steps ahead receives exactly `(-t)^k` after `k`
steps, and nothing before. An event at one site is registered at another exactly from the step
equal to their distance on: never before.

Two packets emitted from the same site `m ≥ 1` steps apart are nested: at any time the later one
stays strictly inside the cone of the earlier one and never reaches its front.

## ii. Key results

- `siteDist` : the distance `|m - n|` between two sites.
- `inner_pow_openHamiltonian_eq_zero` : the light cone, `⟨m| H^k |n⟩ = 0` for `|m - n| > k`.
- `inner_pow_openHamiltonian_front` : the front, `⟨n + k| H^k |n⟩ = (-t)^k`.
- `event_window` : for `t ≠ 0`, the site `r` ahead sees nothing for `k < r` and a nonzero
  amplitude at `k = r`.
- `inner_pow_openHamiltonian_front_eq_zero` : a packet emitted `m ≥ 1` steps later has no
  amplitude on the front of the earlier one.

## iii. Table of contents

- A. The light cone
- B. The front and the window of an event
- C. Nested packets

## iv. References

* E. H. Lieb, D. W. Robinson, *The finite group velocity of quantum spin systems*,
  Communications in Mathematical Physics 28 (1972) 251.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain
open InnerProductSpace

variable (T : TightBindingChain)

/-!

## A. The light cone

-/

/-- The distance `|m - n|` between two sites of the chain. -/
def siteDist {N : ℕ} (m n : Fin N) : ℕ := ((m : ℕ) - n) + ((n : ℕ) - m)

/-- **The light cone of the chain.** After `k` steps nothing connects sites more than `k`
apart. -/
theorem inner_pow_openHamiltonian_eq_zero (k : ℕ) :
    ∀ m n : Fin T.N, k < siteDist m n → ⟪|m⟩, (T.openHamiltonian ^ k) |n⟩⟫_ℂ = 0 := by
  induction k with
  | zero =>
    intro m n h
    have hmn : m ≠ n := by rintro rfl; simp [siteDist] at h
    simp [hmn]
  | succ k ih =>
    intro m n h
    rw [pow_succ, Module.End.mul_apply, ← localizedState.sum_repr' (T.openHamiltonian |n⟩),
      map_sum, inner_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, inner_smul_right, inner_openHamiltonian]
    by_cases hj : k < siteDist m j
    · rw [ih m j hj, mul_zero]
    · have hjn : ¬ (j = n ∨ (j : ℕ) + 1 = n ∨ (n : ℕ) + 1 = j) := by
        unfold siteDist at h hj
        rintro (rfl | h' | h') <;> omega
      rw [not_or, not_or] at hjn
      simp [hjn.1, hjn.2.1, hjn.2.2]

/-!

## B. The front and the window of an event

-/

/-- **The front is reached on time.** The site `k` steps ahead receives `(-t)^k` after `k`
steps. -/
theorem inner_pow_openHamiltonian_front (k : ℕ) :
    ∀ m n : Fin T.N, (m : ℕ) = n + k →
      ⟪|m⟩, (T.openHamiltonian ^ k) |n⟩⟫_ℂ = (-(T.t : ℂ)) ^ k := by
  induction k with
  | zero =>
    intro m n h
    have : m = n := Fin.ext (by omega)
    subst this
    simp
  | succ k ih =>
    intro m n h
    let j : Fin T.N := ⟨n + 1, by omega⟩
    rw [pow_succ, Module.End.mul_apply, ← localizedState.sum_repr' (T.openHamiltonian |n⟩),
      map_sum, inner_sum, Finset.sum_eq_single j]
    · rw [map_smul, inner_smul_right, inner_openHamiltonian, ih m j (by simp [j]; omega),
        pow_succ]
      have hjn : j ≠ n := fun h' => by simp [j, Fin.ext_iff] at h'
      simp [hjn, j, mul_comm]
    · intro i _ hi
      rw [map_smul, inner_smul_right, inner_openHamiltonian]
      by_cases hk : k < siteDist m i
      · rw [T.inner_pow_openHamiltonian_eq_zero k m i hk, mul_zero]
      · have hne : ¬ (i = n ∨ (i : ℕ) + 1 = n ∨ (n : ℕ) + 1 = i) := by
          unfold siteDist at hk
          rintro (rfl | h' | h')
          · omega
          · omega
          · exact hi (Fin.ext (by simp [j]; omega))
        rw [not_or, not_or] at hne
        simp [hne.1, hne.2.1, hne.2.2]
    · simp

/-- **The window of an event.** For `t ≠ 0`, the site `r` steps ahead of `n` receives nothing
during the first `r` steps and a nonzero amplitude at step `r`: the event is registered there
exactly from step `r` on, never before. -/
theorem event_window (ht : T.t ≠ 0) (m n : Fin T.N) {r : ℕ} (hr : (m : ℕ) = n + r) :
    (∀ k < r, ⟪|m⟩, (T.openHamiltonian ^ k) |n⟩⟫_ℂ = 0) ∧
      ⟪|m⟩, (T.openHamiltonian ^ r) |n⟩⟫_ℂ ≠ 0 := by
  refine ⟨fun k hk => T.inner_pow_openHamiltonian_eq_zero k m n ?_, ?_⟩
  · unfold siteDist
    omega
  · rw [T.inner_pow_openHamiltonian_front r m n hr]
    exact pow_ne_zero _ (neg_ne_zero.mpr (by exact_mod_cast ht))

/-!

## C. Nested packets

-/

/-- **Nested packets.** On the front of a packet emitted from `n`, the sites `k` steps away, a
packet emitted from `n` at least one step later has no amplitude. -/
theorem inner_pow_openHamiltonian_front_eq_zero {k l : ℕ} (hl : l < k) (m n : Fin T.N)
    (hmn : siteDist m n = k) : ⟪|m⟩, (T.openHamiltonian ^ l) |n⟩⟫_ℂ = 0 :=
  T.inner_pow_openHamiltonian_eq_zero l m n (hmn ▸ hl)

end TightBindingChain
end CondensedMatter
