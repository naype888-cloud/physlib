/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod
public import PhyslibAlpha.CondensedMatter.LatticeModels.Region
/-!

# The graph of the cube and its middle block

## i. Overview

The cube of `n` cells on a side is the box product of three paths. The `8` cells in the middle of an
even cube form a block that has `24` edges leaving it, and none of its cells touches the border, so
its wall potential vanishes: the block bounds the ground energy of a Coulomb centre in the middle of
the cube by `3 t - 2 k / (√3 a)`.

## ii. Key results

- `outEdges_boxProd` : the edges that leave a product of two sets in a box product of graphs.
- `outEdges_middleBlock` : the middle block of the cube has `24` edges leaving it.
- `degree_cube_interior` : a cell of the cube that does not touch the border has `6` neighbours.
- `groundEnergy_le_middleBlock_cube` : `groundEnergy ≤ 3 t - 2 k / (√3 a)` for a cube of at least
  four cells on a side.

## iii. Table of contents

- A. Edges that leave a product
- B. The cube and its middle block
- C. The Coulomb centre in the middle of the cube

## iv. References

-/

@[expose] public section

namespace CondensedMatter
namespace LatticeModels
open SimpleGraph Finset

/-!

## A. Edges that leave a product

-/

/-- The two cells `a` and `a + 1` of a path of `n` cells. -/
def cellPair (n a : ℕ) : Finset (Fin n) := univ.filter fun i => a ≤ i.val ∧ i.val ≤ a + 1

/-- Membership in the pair of cells. -/
lemma mem_cellPair {n a : ℕ} {i : Fin n} : i ∈ cellPair n a ↔ a ≤ i.val ∧ i.val ≤ a + 1 := by
  simp [cellPair]

lemma card_cellPair {n a : ℕ} (h : a + 1 < n) : (cellPair n a).card = 2 := by
  have : cellPair n a = {⟨a, by omega⟩, ⟨a + 1, h⟩} := by
    ext i; simp only [mem_cellPair, mem_insert, mem_singleton, Fin.ext_iff]; omega
  rw [this]
  exact Finset.card_pair (by simp [Fin.ext_iff])

lemma outEdges_cellPair {n a : ℕ} (h0 : 1 ≤ a) (h : a + 2 < n) :
    outEdges (pathGraph n) (cellPair n a) = 2 := by
  have : (univ.filter fun e : Fin n × Fin n => e.1 ∈ cellPair n a ∧ e.2 ∉ cellPair n a ∧
      (pathGraph n).Adj e.1 e.2) = {(⟨a, by omega⟩, ⟨a - 1, by omega⟩),
        (⟨a + 1, by omega⟩, ⟨a + 2, h⟩)} := by
    ext ⟨i, j⟩
    simp only [mem_filter, mem_univ, true_and, mem_cellPair, pathGraph_adj, mem_insert,
      mem_singleton, Prod.mk.injEq, Fin.ext_iff]
    omega
  unfold outEdges
  rw [this]
  exact Finset.card_pair (by simp [Prod.ext_iff, Fin.ext_iff])

lemma sum_diag_eq_card {γ : Type*} [Fintype γ] [DecidableEq γ] (D : Finset γ) :
    ∑ x, ∑ y, (if x ∈ D ∧ x = y then 1 else 0 : ℕ) = D.card := by
  have : ∀ x, ∑ y, (if x ∈ D ∧ x = y then 1 else 0 : ℕ) = if x ∈ D then 1 else 0 := fun x => by
    by_cases hx : x ∈ D <;> simp [hx]
  simp_rw [this]
  simp

section Box
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  (G : SimpleGraph α) (H : SimpleGraph β) [DecidableRel G.Adj] [DecidableRel H.Adj]
  [DecidableRel (G □ H).Adj]

lemma outEdges_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (K : SimpleGraph ι)
    [DecidableRel K.Adj] (B : Finset ι) :
    outEdges K B = ∑ i, ∑ j, if i ∈ B ∧ j ∉ B ∧ K.Adj i j then 1 else 0 := by
  unfold outEdges
  rw [Finset.card_filter, Fintype.sum_prod_type]

omit [DecidableEq α] [DecidableEq β] in
lemma sum_sum_mul_sum_sum (t1 : α → α → ℕ) (t2 : β → β → ℕ) :
    ∑ a, ∑ c, ∑ a', ∑ c', t1 a a' * t2 c c' = (∑ a, ∑ a', t1 a a') * ∑ c, ∑ c', t2 c c' := by
  have h : ∀ a, ∑ c, ∑ a', ∑ c', t1 a a' * t2 c c' = ∑ a', ∑ c, ∑ c', t1 a a' * t2 c c' :=
    fun a => Finset.sum_comm
  simp_rw [h, ← Finset.mul_sum, ← Finset.sum_mul]


/-- The edges that leave a product of two sets in a box product of graphs. -/
lemma outEdges_boxProd (A : Finset α) (C : Finset β) :
    outEdges (G □ H) (A ×ˢ C) = outEdges G A * C.card + A.card * outEdges H C := by
  have pt : ∀ a c a' c', (if (a, c) ∈ A ×ˢ C ∧ (a', c') ∉ A ×ˢ C ∧ (G □ H).Adj (a, c) (a', c')
      then 1 else 0 : ℕ) =
      (if a ∈ A ∧ a' ∉ A ∧ G.Adj a a' then 1 else 0) * (if c ∈ C ∧ c = c' then 1 else 0) +
        (if a ∈ A ∧ a = a' then 1 else 0) * (if c ∈ C ∧ c' ∉ C ∧ H.Adj c c' then 1 else 0) := by
    intro a c a' c'
    simp only [mem_product, SimpleGraph.boxProd_adj]
    by_cases h1 : a ∈ A <;> by_cases h2 : a' ∈ A <;> by_cases h3 : c ∈ C <;>
      by_cases h4 : c' ∈ C <;> by_cases h5 : G.Adj a a' <;> by_cases h6 : H.Adj c c' <;>
      by_cases h7 : a = a' <;> by_cases h8 : c = c' <;> simp_all [G.ne_of_adj, H.ne_of_adj]
  rw [outEdges_eq_sum]
  simp only [Fintype.sum_prod_type]
  simp_rw [pt]
  simp only [Finset.sum_add_distrib]
  rw [sum_sum_mul_sum_sum, sum_sum_mul_sum_sum, sum_diag_eq_card C, sum_diag_eq_card A,
    ← outEdges_eq_sum G A, ← outEdges_eq_sum H C]

end Box

/-!

## B. The cube and its middle block

-/

/-- The adjacency of a box product is decidable. -/
instance instDecidableRelBoxProd {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β)
    [DecidableEq α] [DecidableEq β] [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj :=
  fun _ _ => decidable_of_iff _ SimpleGraph.boxProd_adj.symm

/-- The graph of the cube: three paths of `n` sites. -/
def cubeGraph (n : ℕ) : SimpleGraph (Fin n × Fin n × Fin n) :=
  pathGraph n □ (pathGraph n □ pathGraph n)

instance (n : ℕ) : DecidableRel (cubeGraph n).Adj := instDecidableRelBoxProd _ _

/-- The middleBlock of the eight cells around the middle of the cube. -/
def middleBlock (n a : ℕ) : Finset (Fin n × Fin n × Fin n) :=
  cellPair n a ×ˢ (cellPair n a ×ˢ cellPair n a)

lemma card_middleBlock {n a : ℕ} (h : a + 1 < n) : (middleBlock n a).card = 8 := by
  simp [middleBlock, Finset.card_product, card_cellPair h]

/-- **The middleBlock has twenty four edges leaving it.** -/
lemma outEdges_middleBlock {n a : ℕ} (h0 : 1 ≤ a) (h : a + 2 < n) :
    outEdges (cubeGraph n) (middleBlock n a) = 24 := by
  unfold cubeGraph middleBlock
  rw [outEdges_boxProd, outEdges_boxProd, outEdges_cellPair h0 h]
  simp [Finset.card_product, card_cellPair (show a + 1 < n by omega)]

lemma degree_pathGraph_interior {n : ℕ} {i : Fin n} (h0 : 1 ≤ i.val) (h1 : i.val + 1 < n) :
    (pathGraph n).degree i = 2 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have : (pathGraph n).neighborFinset i = {⟨i.val - 1, by omega⟩, ⟨i.val + 1, h1⟩} := by
    ext j
    simp only [SimpleGraph.mem_neighborFinset, pathGraph_adj, mem_insert, mem_singleton,
      Fin.ext_iff]
    omega
  rw [this]
  exact Finset.card_pair (by simp [Fin.ext_iff])

lemma degree_cube_interior {n : ℕ} {p : Fin n × Fin n × Fin n}
    (h0 : ∀ i ∈ [p.1, p.2.1, p.2.2], 1 ≤ i.val)
    (h1 : ∀ i ∈ [p.1, p.2.1, p.2.2], i.val + 1 < n) : (cubeGraph n).degree p = 6 := by
  unfold cubeGraph
  rw [SimpleGraph.degree_boxProd, SimpleGraph.degree_boxProd]
  simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, or_false, forall_eq] at h0 h1
  rw [degree_pathGraph_interior h0.1 h1.1, degree_pathGraph_interior h0.2.1 h1.2.1,
    degree_pathGraph_interior h0.2.2 h1.2.2]


/-!

## C. The Coulomb centre in the middle of the cube

-/

/-- The position of the cell `i` of a path of `n` cells, from the middle of the path. -/
noncomputable def cellPos (a : ℝ) (n : ℕ) (i : Fin n) : ℝ := ((i.val : ℝ) + 1 / 2 - n / 2) * a

/-- The distance of the cell `p` of the cube from its centre. -/
noncomputable def cubeRadius (a : ℝ) (n : ℕ) (p : Fin n × Fin n × Fin n) : ℝ :=
  √(cellPos a n p.1 ^ 2 + cellPos a n p.2.1 ^ 2 + cellPos a n p.2.2 ^ 2)

/-- The wall of the cube: the part of the degree that the border cells lack. -/
noncomputable def wallCube (n : ℕ) (t : ℝ) (p : Fin n × Fin n × Fin n) : ℝ :=
  t * (6 - (cubeGraph n).degree p)

lemma cellPos_sq {M : ℕ} {a : ℝ} {i : Fin (2 * M)} (h : i ∈ cellPair (2 * M) (M - 1)) (hM : 1 ≤ M) :
    cellPos a (2 * M) i ^ 2 = a ^ 2 / 4 := by
  rw [mem_cellPair] at h
  have : i.val = M - 1 ∨ i.val = M := by omega
  unfold cellPos
  rcases this with h | h
  · have : (i.val : ℝ) = M - 1 := by rw [h]; push_cast [Nat.cast_sub hM]; ring
    rw [this]; push_cast; ring
  · have : (i.val : ℝ) = M := by rw [h]
    rw [this]; push_cast; ring

lemma cubeRadius_middleBlock {M : ℕ} (hM : 1 ≤ M) {a : ℝ} (ha : 0 < a)
    {p : Fin (2 * M) × Fin (2 * M) × Fin (2 * M)}
    (hp : p ∈ middleBlock (2 * M) (M - 1)) : cubeRadius a (2 * M) p = √3 * a / 2 := by
  simp only [middleBlock, Finset.mem_product] at hp
  unfold cubeRadius
  rw [cellPos_sq hp.1 hM, cellPos_sq hp.2.1 hM, cellPos_sq hp.2.2 hM]
  rw [show a ^ 2 / 4 + a ^ 2 / 4 + a ^ 2 / 4 = (√3 * a / 2) ^ 2 by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]; ring]
  exact Real.sqrt_sq (by positivity)

lemma wallCube_middleBlock {M : ℕ} (hM : 2 ≤ M) (t : ℝ)
    {p : Fin (2 * M) × Fin (2 * M) × Fin (2 * M)}
    (hp : p ∈ middleBlock (2 * M) (M - 1)) : wallCube (2 * M) t p = 0 := by
  simp only [middleBlock, Finset.mem_product, mem_cellPair] at hp
  have := degree_cube_interior (n := 2 * M) (p := p) (by simp; omega) (by simp; omega)
  unfold wallCube
  rw [this]; norm_num

/-- The ground energy of the hydrogen cube is at most `3 t - 2 k / (√3 a)`, whenever the cube has at
least four cells on a side. -/
lemma groundEnergy_le_middleBlock_cube {M : ℕ} (hM : 2 ≤ M) {a t k : ℝ} (ha : 0 < a) :
    groundEnergy (hamiltonian (cubeGraph (2 * M)) t
      (coulombBox k (cubeRadius a (2 * M)) (wallCube (2 * M) t))) ⊤ ≤
      3 * t - k * (2 / (√3 * a)) := by
  have hB : (middleBlock (2 * M) (M - 1)).Nonempty := by
    rw [← Finset.card_pos, card_middleBlock (by omega)]; norm_num
  have h := groundEnergy_le_region (cubeGraph (2 * M)) hB t
    (coulombBox k (cubeRadius a (2 * M)) (wallCube (2 * M) t))
  rw [outEdges_middleBlock (by omega) (by omega), card_middleBlock (by omega)] at h
  have hV : ∀ p ∈ middleBlock (2 * M) (M - 1),
      coulombBox k (cubeRadius a (2 * M)) (wallCube (2 * M) t) p = -(k * (2 / (√3 * a))) := by
    intro p hp
    unfold coulombBox
    rw [wallCube_middleBlock hM t hp, cubeRadius_middleBlock (by omega) ha hp]
    have : (√3 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [Finset.sum_congr rfl hV, Finset.sum_const, card_middleBlock (by omega)] at h
  have e : ((24 : ℕ) : ℝ) = 24 := by norm_num
  have e8 : ((8 : ℕ) : ℝ) = 8 := by norm_num
  rw [e, e8] at h
  simp only [nsmul_eq_mul, e8] at h
  linarith

end LatticeModels
end CondensedMatter
