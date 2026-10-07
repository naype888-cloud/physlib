/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import PhyslibAlpha.CondensedMatter.TightBindingChain.HorizonCount
/-!

# Each bond across the cut closes one cycle

## i. Overview

The nearest-neighbour bonds of the open tight binding chain on `N` sites form the path graph,
a tree: `N - 1` edges and no cycle. A bond of range at least two closes a cycle. Adding a set
`S` of bonds across a cut gives the bond graph of the chain with `S`, whose cycle rank
`|E| + 1 - |V|` is exactly `|S|`: each bond across the cut is one independent cycle. Different
sets give different graphs, so the entropy of `k` quanta on distinct bonds counts graphs.

## ii. Key results

- `card_edgeSet_pathGraph`, `pathGraph_isTree` : the nearest-neighbour bonds form a tree.
- `cycleRank` : the cycle rank `|E| + 1 - |V|` of a graph on `Fin m`.
- `cycleRank_sup_edge` : a new edge in a connected graph raises the cycle rank by one.
- `bondGraph` : the path with the extra bonds `S`.
- `cycleRank_bondGraph` : with `S` across the cut, the cycle rank is `|S|`.
- `bondGraph_injOn` : different sets of bonds across the cut give different graphs.
- `simpleCutEntropy_eq_log_card_graphs` : the entropy on distinct bonds counts graphs.

## iii. Table of contents

- A. The path is a tree
- B. Cycle rank
- C. The bonds across the cut

## iv. References

* N. Biggs, *Algebraic Graph Theory*, Cambridge University Press (1993), chapter 4.

-/

@[expose] public section

namespace CondensedMatter
namespace TightBindingChain

open SimpleGraph

/-!

## A. The path is a tree

-/

/-- The path graph on `n + 1` vertices has `n` edges. -/
lemma card_edgeSet_pathGraph (n : ℕ) : Nat.card (pathGraph (n + 1)).edgeSet = n := by
  have hbij : Nat.card (Fin n) = Nat.card (pathGraph (n + 1)).edgeSet := by
    refine Nat.card_eq_of_bijective (fun i : Fin n =>
      (⟨s(i.castSucc, i.succ), by simp [pathGraph_adj]⟩ : (pathGraph (n + 1)).edgeSet))
      ⟨fun i j h => ?_, ?_⟩
    · have h := congrArg Subtype.val h
      simp only [Sym2.eq_iff] at h
      rcases h with ⟨h, -⟩ | ⟨h, h'⟩
      · exact Fin.castSucc_injective _ h
      · have := congrArg Fin.val h
        have := congrArg Fin.val h'
        simp at *
        omega
    · rintro ⟨e, he⟩
      induction e using Sym2.ind with
      | h u v =>
        rw [mem_edgeSet, pathGraph_adj] at he
        rcases he with h | h
        · exact ⟨⟨u.val, by omega⟩, Subtype.ext (Sym2.eq_iff.mpr
            (Or.inl ⟨Fin.ext rfl, Fin.ext (by simp only [Fin.val_succ]; omega)⟩))⟩
        · exact ⟨⟨v.val, by omega⟩, Subtype.ext (Sym2.eq_iff.mpr
            (Or.inr ⟨Fin.ext rfl, Fin.ext (by simp only [Fin.val_succ]; omega)⟩))⟩
  rw [← hbij, Nat.card_fin]

/-- The path graph on a nonempty vertex set is connected. -/
lemma pathGraph_connected' {m : ℕ} (hm : m ≠ 0) : (pathGraph m).Connected :=
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  ⟨pathGraph_preconnected m⟩

/-- **The nearest-neighbour bonds form a tree.** -/
lemma pathGraph_isTree (n : ℕ) : (pathGraph (n + 1)).IsTree :=
  isTree_iff_connected_and_card.mpr ⟨pathGraph_connected n, by
    rw [card_edgeSet_pathGraph, Nat.card_fin]⟩

/-!

## B. Cycle rank

-/

/-- The cycle rank `|E| + 1 - |V|` of a graph on `Fin m`. -/
noncomputable def cycleRank {m : ℕ} (G : SimpleGraph (Fin m)) : ℕ := Nat.card G.edgeSet + 1 - m

/-- A new edge in a connected graph raises the cycle rank by one. -/
lemma cycleRank_sup_edge {m : ℕ} {G : SimpleGraph (Fin m)} (hG : G.Connected) {s t : Fin m}
    (hn : ¬ G.Adj s t) (h : s ≠ t) : cycleRank (G ⊔ edge s t) = cycleRank G + 1 := by
  classical
  have hle := hG.card_vert_le_card_edgeSet_add_one
  rw [Nat.card_fin] at hle
  have hc : Nat.card (G ⊔ edge s t).edgeSet = Nat.card G.edgeSet + 1 := by
    simp only [Nat.card_eq_fintype_card, ← edgeFinset_card]
    convert card_edgeFinset_sup_edge (G := G) hn h
  unfold cycleRank
  rw [hc]
  omega

/-- The path graph on a nonempty vertex set has cycle rank zero. -/
lemma cycleRank_pathGraph {m : ℕ} (hm : m ≠ 0) : cycleRank (pathGraph m) = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  unfold cycleRank
  rw [card_edgeSet_pathGraph]
  omega

/-!

## C. The bonds across the cut

-/

/-- The path on `Fin m` with the extra bonds of `S`. -/
def bondGraph {m : ℕ} (S : Finset (Fin m × Fin m)) : SimpleGraph (Fin m) :=
  pathGraph m ⊔ S.sup fun p => edge p.1 p.2

lemma bondGraph_connected {m : ℕ} (hm : m ≠ 0) (S : Finset (Fin m × Fin m)) :
    (bondGraph S).Connected :=
  (pathGraph_connected' hm).mono le_sup_left

lemma bondGraph_insert {m : ℕ} (S : Finset (Fin m × Fin m)) (p : Fin m × Fin m) :
    bondGraph (insert p S) = bondGraph S ⊔ edge p.1 p.2 := by
  simp only [bondGraph, Finset.sup_insert]
  ac_rfl

/-- An adjacency of the bonds of `S` is one of them. -/
lemma exists_of_adj_sup {m : ℕ} (S : Finset (Fin m × Fin m)) {u v : Fin m}
    (h : (S.sup fun p => edge p.1 p.2).Adj u v) :
    ∃ q ∈ S, (u = q.1 ∧ v = q.2) ∨ (u = q.2 ∧ v = q.1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at h
  | insert q S _ ih =>
    rw [Finset.sup_insert, sup_adj, edge_adj] at h
    rcases h with ⟨hq, -⟩ | h
    · exact ⟨q, Finset.mem_insert_self _ _, hq⟩
    · obtain ⟨r, hr, hr'⟩ := ih h
      exact ⟨r, Finset.mem_insert_of_mem hr, hr'⟩

variable (T : TightBindingChain)

/-- A bond across the cut outside `S` is not yet an edge of the bond graph of `S`. -/
lemma not_adj_bondGraph {c : ℕ} {S : Finset (Fin T.N × Fin T.N)} (hS : S ⊆ T.cutBonds c)
    {p : Fin T.N × Fin T.N} (hp : p ∈ T.cutBonds c) (hpS : p ∉ S) :
    ¬ (bondGraph S).Adj p.1 p.2 := by
  have hp' := T.mem_cutBonds.mp hp
  rw [bondGraph, sup_adj, pathGraph_adj]
  rintro (h | h)
  · omega
  · obtain ⟨q, hq, ⟨h1, h2⟩ | ⟨h1, -⟩⟩ := exists_of_adj_sup S h
    · exact hpS (by rw [Prod.ext h1 h2]; exact hq)
    · have hq' := T.mem_cutBonds.mp (hS hq)
      have := congrArg Fin.val h1
      omega

/-- A bond of `S` across the cut is an edge of the bond graph of `S`. -/
lemma adj_bondGraph {c : ℕ} {S : Finset (Fin T.N × Fin T.N)} {p : Fin T.N × Fin T.N}
    (hp : p ∈ T.cutBonds c) (hpS : p ∈ S) : (bondGraph S).Adj p.1 p.2 := by
  have hne : p.1 ≠ p.2 := fun h => by
    have := T.mem_cutBonds.mp hp
    rw [h] at this
    omega
  rw [bondGraph, sup_adj]
  exact Or.inr ((Finset.le_sup (f := fun p => edge p.1 p.2) hpS)
    (show (edge p.1 p.2).Adj p.1 p.2 by rw [edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, hne⟩))

/-- **Each bond across the cut is one cycle**: with `S` across the cut, the cycle rank of the
bond graph is `|S|`. -/
theorem cycleRank_bondGraph {c : ℕ} {S : Finset (Fin T.N × Fin T.N)}
    (hS : S ⊆ T.cutBonds c) : cycleRank (bondGraph S) = S.card := by
  classical
  have hN : T.N ≠ 0 := NeZero.ne _
  induction S using Finset.induction_on with
  | empty =>
    simpa [bondGraph] using cycleRank_pathGraph hN
  | insert p S hpS ih =>
    have hSs : S ⊆ T.cutBonds c := (Finset.subset_insert p S).trans hS
    have hp : p ∈ T.cutBonds c := hS (Finset.mem_insert_self p S)
    have hne : p.1 ≠ p.2 := fun h => by
      have := T.mem_cutBonds.mp hp
      rw [h] at this
      omega
    rw [bondGraph_insert, cycleRank_sup_edge (bondGraph_connected hN S)
      (T.not_adj_bondGraph hSs hp hpS) hne, ih hSs, Finset.card_insert_of_notMem hpS]

/-- Different sets of bonds across the cut give different graphs. -/
theorem bondGraph_injOn (c : ℕ) :
    Set.InjOn (bondGraph (m := T.N)) {S | S ⊆ T.cutBonds c} := by
  intro S hS T' hT h
  ext p
  constructor
  · intro hp
    by_contra hpT
    exact T.not_adj_bondGraph hT (hS hp) hpT (h ▸ T.adj_bondGraph (hS hp) hp)
  · intro hp
    by_contra hpS
    exact T.not_adj_bondGraph hS (hT hp) hpS (h ▸ T.adj_bondGraph (hT hp) hp)

open Classical in
/-- **The entropy counts graphs**: the entropy of `k` quanta on distinct bonds across the cut is
the logarithm of the number of bond graphs with `k` extra cycles across it. -/
theorem simpleCutEntropy_eq_log_card_graphs (c k : ℕ) :
    T.simpleCutEntropy c k =
      Real.log (((T.cutBonds c).powersetCard k).image (bondGraph (m := T.N))).card := by
  rw [simpleCutEntropy, Finset.card_image_of_injOn, Finset.card_powersetCard]
  intro S hS S' hS' h
  exact T.bondGraph_injOn c (Finset.mem_powersetCard.mp hS).1 (Finset.mem_powersetCard.mp hS').1 h

end TightBindingChain
end CondensedMatter
