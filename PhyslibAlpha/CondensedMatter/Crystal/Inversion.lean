/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.CondensedMatter.Crystal.Symmetry
public import PhyslibAlpha.ProbabilisticTheory.HilbertSpace.State.Antiunitary
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!

# Inversion and time reversal on a Bravais lattice

Every lattice with one site per cell is symmetric under the inversion `n ↦ -n`. Combined with
time reversal, it makes the energy and position fluctuations of a plane wave uncorrelated.

## i. Overview

In a periodic graph with one site per cell, the sites `n` and `m` are bonded exactly when `0`
and `m - n` are. Translating by `-n - m` and swapping the two sites shows that `-n` and `-m` are
bonded as well. So the inversion `n ↦ -n` is a symmetry of every periodic graph of a Bravais
lattice: these lattices are centrosymmetric.

Take a finite region `Λ` of the lattice with `-Λ = Λ`, a real hopping amplitude `t` along the
bonds, and the position `r` along a direction, an additive map `G → ℝ`. The map
`(f ψ)(n) = conj ψ(-n)` combines the inversion with time reversal. It is an antiunitary
involution. The hopping is real and invariant under the inversion, so `f H f = H`, while
`f X f = -X` because `r (-n) = -r n`. By `covariance_ofVec_eq_zero_of_antiunitary`, in every
state fixed by `f` the energy and the position along every direction are uncorrelated. Every
plane wave `n ↦ exp (i k n)` is fixed by `f`, since both operations reverse the momentum.

## ii. Key results

- `PeriodicGraph.inversion_mem_symmetries` : the inversion is a symmetry of every periodic graph
  with one site per cell.
- `inversionReversal` : the inversion combined with time reversal, `f`.
- `inversionReversal_hopping`, `inversionReversal_position` : `f H f = H` and `f X f = -X`.
- `covariance_hopping_position_eq_zero` : in a state fixed by `f`, the energy and position
  fluctuations are uncorrelated.
- `inversionReversal_planeWave` : every plane wave is fixed by `f`.
- `covariance_hopping_position_unitPlaneWave` : so in every plane wave the energy and the
  position along every direction are uncorrelated.

## iii. Table of contents

- A. The inversion of a Bravais lattice
- B. Hopping on a symmetric region
- C. Uncorrelated fluctuations

## iv. References

* N. Ashcroft & N. D. Mermin, Solid State Physics, Chapter 7.

-/

@[expose] public section

namespace CondensedMatter.Crystal

open ProbabilisticTheory
open scoped ComplexOrder InnerProductSpace selfAdjoint

variable {G : Type*} [AddCommGroup G]

/-! ## A. The inversion of a Bravais lattice -/

namespace PeriodicGraph

/-- In a lattice with one site per cell, the bond to `-d` exists exactly when the bond to `d`
does. -/
lemma bonded_neg (g : PeriodicGraph (Crystal.ofUnitCell G Unit)) (d : G) :
    g.Bonded () () (-d) ↔ g.Bonded () () d := by
  have h := g.adj_vadd (-d) ⟨0, ()⟩ ⟨d, ()⟩
  change g.toSimpleGraph.Adj ⟨-d + 0, ()⟩ ⟨-d + d, ()⟩ ↔ _ at h
  rw [add_zero, neg_add_cancel] at h
  rw [Bonded, Bonded, g.toSimpleGraph.adj_comm, h]

/-- In a lattice with one site per cell, `-n` and `-m` are bonded exactly when `n` and `m`
are. -/
lemma adj_neg (g : PeriodicGraph (Crystal.ofUnitCell G Unit)) (n m : G) :
    g.toSimpleGraph.Adj ⟨-n, ()⟩ ⟨-m, ()⟩ ↔ g.toSimpleGraph.Adj ⟨n, ()⟩ ⟨m, ()⟩ := by
  rw [adj_iff_bonded, adj_iff_bonded, show -m - -n = -(m - n) by abel, bonded_neg]

/-- The inversion `n ↦ -n` of a lattice with one site per cell. -/
def inversion : CellSymmetry G Unit := ⟨AddEquiv.neg G, Equiv.refl Unit, fun _ => 0⟩

/-- **Every lattice with one site per cell is centrosymmetric**: the inversion preserves the
bonds of every periodic graph. -/
lemma inversion_mem_symmetries (g : PeriodicGraph (Crystal.ofUnitCell G Unit)) :
    inversion ∈ g.symmetries := by
  rw [mem_symmetries_iff]
  intro i j d
  change _ ↔ g.toSimpleGraph.Adj ⟨0, ()⟩ ⟨-d + 0 - 0, ()⟩
  rw [add_zero, sub_zero, ← neg_zero, adj_neg]
  rfl

end PeriodicGraph

/-! ## B. Hopping on a symmetric region -/

attribute [local instance] PeriodicGraph.decidableAdj

variable [DecidableEq G] (g : PeriodicGraph (Crystal.ofUnitCell G Unit)) {Λ : Finset G}
  (hΛ : ∀ n ∈ Λ, -n ∈ Λ)

/-- The inversion of a region with `-Λ = Λ`. -/
def regionNeg (n : Λ) : Λ := ⟨-n, hΛ n n.2⟩

omit [DecidableEq G] in
lemma regionNeg_regionNeg (n : Λ) : regionNeg hΛ (regionNeg hΛ n) = n :=
  Subtype.ext (neg_neg (n : G))

/-- The hopping matrix of the graph on the region, with amplitude `-t` along every bond. -/
def hoppingMatrix (t : ℝ) : Matrix Λ Λ ℂ :=
  fun n m => if g.toSimpleGraph.Adj ⟨(n : G), ()⟩ ⟨(m : G), ()⟩ then -(t : ℂ) else 0

/-- The position along a direction `r` on the region, a diagonal matrix. -/
def positionMatrix (r : G →+ ℝ) : Matrix Λ Λ ℂ := Matrix.diagonal fun n => (r n : ℂ)

/-- The hopping Hamiltonian as an observable. -/
noncomputable def hoppingObservable (t : ℝ) : Observable (EuclideanSpace ℂ Λ →L[ℂ]
    EuclideanSpace ℂ Λ) :=
  ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ) (hoppingMatrix g t), selfAdjoint.mem_iff.mpr <|
    (show IsSelfAdjoint (hoppingMatrix g t) by
      ext n m
      simp only [Matrix.star_apply, hoppingMatrix, g.toSimpleGraph.adj_comm]
      split_ifs <;> simp).map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ))⟩

/-- The position along `r` as an observable. -/
noncomputable def positionObservable (r : G →+ ℝ) : Observable (EuclideanSpace ℂ Λ →L[ℂ]
    EuclideanSpace ℂ Λ) :=
  ⟨Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ) (positionMatrix r), selfAdjoint.mem_iff.mpr <|
    (show IsSelfAdjoint (positionMatrix (Λ := Λ) r) by
      ext n m
      simp only [Matrix.star_apply, positionMatrix, Matrix.diagonal_apply]
      split_ifs with h h' h' <;> simp_all).map (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ))⟩

/-- Inversion combined with time reversal: `(f ψ)(n) = conj ψ(-n)`. -/
noncomputable def inversionReversalₗ : EuclideanSpace ℂ Λ →ₗ⋆[ℂ] EuclideanSpace ℂ Λ where
  toFun ψ := WithLp.toLp 2 fun n => (starRingEnd ℂ) (ψ (regionNeg hΛ n))
  map_add' ψ φ := by ext n; simp
  map_smul' c ψ := by ext n; simp

omit [DecidableEq G] in
lemma inversionReversalₗ_apply (ψ : EuclideanSpace ℂ Λ) (n : Λ) :
    inversionReversalₗ hΛ ψ n = (starRingEnd ℂ) (ψ (regionNeg hΛ n)) := rfl

omit [DecidableEq G] in
lemma inner_inversionReversalₗ (ψ φ : EuclideanSpace ℂ Λ) :
    ⟪inversionReversalₗ hΛ ψ, inversionReversalₗ hΛ φ⟫_ℂ = (starRingEnd ℂ) ⟪ψ, φ⟫_ℂ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, inversionReversalₗ_apply, map_sum, map_mul,
    Complex.conj_conj]
  exact Equiv.sum_comp (Function.Involutive.toPerm _ (regionNeg_regionNeg hΛ))
    (fun n => (starRingEnd ℂ) (φ n) * ψ n)

/-- Inversion combined with time reversal, an antiunitary involution. -/
noncomputable def inversionReversal : EuclideanSpace ℂ Λ →L⋆[ℂ] EuclideanSpace ℂ Λ :=
  antiunitaryOfInner (inversionReversalₗ hΛ) (inner_inversionReversalₗ hΛ)

omit [DecidableEq G] in
lemma inversionReversal_apply (ψ : EuclideanSpace ℂ Λ) (n : Λ) :
    inversionReversal hΛ ψ n = (starRingEnd ℂ) (ψ (regionNeg hΛ n)) := rfl

omit [DecidableEq G] in
lemma inversionReversal_inversionReversal (ψ : EuclideanSpace ℂ Λ) :
    inversionReversal hΛ (inversionReversal hΛ ψ) = ψ := by
  ext n
  rw [inversionReversal_apply, inversionReversal_apply, Complex.conj_conj, regionNeg_regionNeg]

/-- A matrix with `conj M (-n) (-m) = s M n m` is carried to `s M` by `f`. -/
lemma inversionReversal_matrix (M : Matrix Λ Λ ℂ) (s : ℂ)
    (hM : ∀ n m, (starRingEnd ℂ) (M (regionNeg hΛ n) (regionNeg hΛ m)) = s * M n m)
    (ψ : EuclideanSpace ℂ Λ) :
    inversionReversal hΛ (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ) M (inversionReversal hΛ ψ)) =
      s • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Λ) M ψ := by
  ext n
  rw [inversionReversal_apply, PiLp.smul_apply]
  change (starRingEnd ℂ) (Matrix.mulVec M _ _) = s • Matrix.mulVec M _ _
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, smul_eq_mul, Finset.mul_sum]
  rw [← Equiv.sum_comp (Function.Involutive.toPerm _ (regionNeg_regionNeg hΛ))]
  refine Finset.sum_congr rfl fun m _ => ?_
  change (starRingEnd ℂ) (M _ (regionNeg hΛ m)) *
    (starRingEnd ℂ) ((starRingEnd ℂ) (ψ (regionNeg hΛ (regionNeg hΛ m)))) = _
  rw [hM, Complex.conj_conj, regionNeg_regionNeg, mul_assoc]
  rfl

/-- `f H f = H`: the hopping is real and invariant under the inversion. -/
lemma inversionReversal_hopping (t : ℝ) (ψ : EuclideanSpace ℂ Λ) :
    inversionReversal hΛ ((hoppingObservable (Λ := Λ) g t : EuclideanSpace ℂ Λ →L[ℂ] _)
      (inversionReversal hΛ ψ)) =
      (hoppingObservable (Λ := Λ) g t : EuclideanSpace ℂ Λ →L[ℂ] _) ψ := by
  have h := inversionReversal_matrix hΛ (hoppingMatrix g t) 1 (fun n m => by
    simp only [hoppingMatrix, regionNeg, PeriodicGraph.adj_neg, one_mul]
    split_ifs <;> simp) ψ
  rwa [one_smul] at h

/-- `f X f = -X`: the position along `r` is reversed by the inversion. -/
lemma inversionReversal_position (r : G →+ ℝ) (ψ : EuclideanSpace ℂ Λ) :
    inversionReversal hΛ ((positionObservable (Λ := Λ) r : EuclideanSpace ℂ Λ →L[ℂ] _)
      (inversionReversal hΛ ψ)) =
      (0 : ℂ) • ψ - (positionObservable (Λ := Λ) r : EuclideanSpace ℂ Λ →L[ℂ] _) ψ := by
  rw [zero_smul, zero_sub, ← neg_one_smul ℂ]
  refine inversionReversal_matrix hΛ (positionMatrix r) (-1) (fun n m => ?_) ψ
  simp only [positionMatrix, Matrix.diagonal_apply, regionNeg, Subtype.mk.injEq, neg_inj,
    ← Subtype.ext_iff]
  split_ifs <;> simp

/-! ## C. Uncorrelated fluctuations -/

/-- **In a state fixed by the inversion combined with time reversal, the energy and the
position along every direction are uncorrelated.** -/
lemma covariance_hopping_position_eq_zero (t : ℝ) (r : G →+ ℝ) {ψ : EuclideanSpace ℂ Λ}
    (h : ‖ψ‖ = 1) (hψ : inversionReversal hΛ ψ = ψ) :
    UnitalPositiveLinearMap.covariance (UnitalPositiveLinearMap.ofVec h)
      (hoppingObservable g t) (positionObservable r) = 0 :=
  UnitalPositiveLinearMap.covariance_ofVec_eq_zero_of_antiunitary (f := inversionReversal hΛ)
    (inversionReversal_inversionReversal hΛ) (inner_inversionReversalₗ hΛ) h hψ
    (inversionReversal_hopping g hΛ t) 0 (inversionReversal_position hΛ r)

/-- A plane wave of momentum `k`, an additive map `G → ℝ`, on the region. -/
noncomputable def planeWave (Λ : Finset G) (k : G →+ ℝ) : EuclideanSpace ℂ Λ :=
  WithLp.toLp 2 fun n => Complex.exp (k n * Complex.I)

omit [DecidableEq G] in
/-- **Every plane wave is fixed by the inversion combined with time reversal.** -/
lemma inversionReversal_planeWave (k : G →+ ℝ) :
    inversionReversal hΛ (planeWave Λ k) = planeWave Λ k := by
  ext n
  rw [inversionReversal_apply]
  change (starRingEnd ℂ) (Complex.exp (k (-n) * Complex.I)) = Complex.exp (k n * Complex.I)
  rw [← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf

omit [DecidableEq G] in
lemma norm_planeWave (Λ : Finset G) (k : G →+ ℝ) : ‖planeWave Λ k‖ = √(Λ.card : ℝ) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [planeWave, Complex.norm_exp_ofReal_mul_I]

/-- The plane wave of momentum `k`, normalized on a nonempty region. -/
noncomputable def unitPlaneWave (Λ : Finset G) (k : G →+ ℝ) : EuclideanSpace ℂ Λ :=
  ((√(Λ.card : ℝ))⁻¹ : ℝ) • planeWave Λ k

omit [DecidableEq G] in
lemma norm_unitPlaneWave (hne : Λ.Nonempty) (k : G →+ ℝ) : ‖unitPlaneWave Λ k‖ = 1 := by
  rw [unitPlaneWave, norm_smul, norm_planeWave, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hne.card_pos))

include hΛ in
/-- **In every plane wave on a symmetric region of a lattice with one site per cell, the energy
and the position along every direction are uncorrelated.** -/
lemma covariance_hopping_position_unitPlaneWave (hne : Λ.Nonempty) (t : ℝ) (k r : G →+ ℝ) :
    UnitalPositiveLinearMap.covariance
      (UnitalPositiveLinearMap.ofVec (norm_unitPlaneWave hne k))
      (hoppingObservable g t) (positionObservable r) = 0 := by
  refine covariance_hopping_position_eq_zero g hΛ t r _ ?_
  rw [unitPlaneWave, ← Complex.coe_smul, (inversionReversal hΛ).map_smulₛₗ, Complex.conj_ofReal,
    inversionReversal_planeWave]

end CondensedMatter.Crystal
