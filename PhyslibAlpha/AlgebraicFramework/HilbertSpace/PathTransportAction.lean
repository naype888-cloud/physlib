/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathObservables
public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.PathExtremalState

/-!

# The transport acting on the extremal vector

The adjacency matrix of `pathGraph d` sums the two neighbours of a vertex; on `sineMode d` this
gives `T v = -i tan θ cos ((j + 1) θ) (-i)ʲ`.

-/

@[expose] public section

open Finset Matrix SimpleGraph

namespace PathObservables

open scoped Classical in
/-- The adjacency matrix of the path graph sums the two neighbours of each vertex. -/
lemma adjMatrix_mulVec_pathGraph {d : ℕ} (v : Fin d → ℂ) (j : Fin d) :
    ((pathGraph d).adjMatrix ℂ *ᵥ v) j =
      (if h : (j : ℕ) + 1 < d then v ⟨j + 1, h⟩ else 0) +
        (if h : 0 < (j : ℕ) then v ⟨j - 1, by omega⟩ else 0) := by
  simp only [mulVec, dotProduct, adjMatrix_apply, pathGraph_adj]
  have key : ∀ x : Fin d, (if (j : ℕ) + 1 = x ∨ (x : ℕ) + 1 = j then (1 : ℂ) else 0) * v x =
      (if h : (j : ℕ) + 1 < d then (if x = ⟨j + 1, h⟩ then v x else 0) else 0) +
        (if h : 0 < (j : ℕ) then (if x = ⟨j - 1, by omega⟩ then v x else 0) else 0) := by
    intro x
    have hx := x.2
    by_cases h1 : (j : ℕ) + 1 = x
    · have hr : (j : ℕ) + 1 < d := by omega
      have hl : ¬ (x : ℕ) + 1 = j := by omega
      simp [h1, hl, Fin.ext_iff]
      intro _ h
      exfalso
      omega
    · by_cases h2 : (x : ℕ) + 1 = j
      · have hl : 0 < (j : ℕ) := by omega
        simp [h1, h2, hl, Fin.ext_iff, show (j : ℕ) - 1 = x by omega]
        intro _ h
        exfalso
        omega
      · simp [h1, h2, Fin.ext_iff]
        split_ifs <;> simp_all <;> omega
  rw [sum_congr rfl fun x _ => key x, sum_add_distrib]
  by_cases hr : (j : ℕ) + 1 < d <;> by_cases hl : 0 < (j : ℕ) <;> simp [hr, hl]

lemma spectralRadius_eq (d : ℕ) : spectralRadius d = 2 * Real.cos (angle d) := rfl

lemma sineMode_apply (d : ℕ) (i : Fin d) :
    (sineMode d).ofLp i = (-Complex.I) ^ (i : ℕ) * (Real.sin (((i : ℕ) + 1) * angle d) : ℂ) := by
  simp [sineMode]

lemma cos_angle_pos {d : ℕ} (hd : 2 ≤ d) : 0 < Real.cos (angle d) := by
  have h : (3 : ℝ) ≤ (d : ℝ) + 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have : 0 < angle d := by unfold angle; positivity
    linarith [Real.pi_pos]
  · unfold angle
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]

lemma sin_succ_angle (d : ℕ) : Real.sin (((d : ℝ) + 1) * angle d) = 0 := by
  have : ((d : ℝ) + 1) * angle d = Real.pi := by
    unfold angle
    field_simp
  rw [this, Real.sin_pi]

/-- The transport matrix acts on the extremal vector coordinatewise by
`-i tan θ cos ((j + 1) θ) (-i)ʲ`. -/
lemma transport_mulVec_sineMode {d : ℕ} (hd : 2 ≤ d) (j : Fin d) :
    (transport d *ᵥ (sineMode d).ofLp) j =
      -Complex.I * (Real.tan (angle d) : ℂ) * (Real.cos (((j : ℕ) + 1) * angle d) : ℂ) *
        (-Complex.I) ^ (j : ℕ) := by
  have hcos := cos_angle_pos hd
  rw [transport, Matrix.smul_mulVec, Pi.smul_apply, adjMatrix_mulVec_pathGraph]
  have hR : (if h : (j : ℕ) + 1 < d then (sineMode d).ofLp ⟨j + 1, h⟩ else 0) =
      (-Complex.I) ^ (j : ℕ) * (-Complex.I) *
        (Real.sin ((((j : ℕ) : ℝ) + 2) * angle d) : ℂ) := by
    by_cases h : (j : ℕ) + 1 < d
    · rw [dif_pos h, sineMode_apply, Fin.val_mk, pow_succ]
      push_cast
      ring_nf
    · have h0 : Real.sin ((((j : ℕ) : ℝ) + 2) * angle d) = 0 := by
        have hjd : (j : ℕ) + 1 = d := by omega
        have : (((j : ℕ) : ℝ) + 2) = (d : ℝ) + 1 := by
          have := congrArg (fun n : ℕ => (n : ℝ)) hjd
          push_cast at this
          linarith
        rw [this, sin_succ_angle]
      rw [dif_neg h, h0]
      simp
  have hL : (if h : 0 < (j : ℕ) then (sineMode d).ofLp ⟨j - 1, by omega⟩ else 0) =
      (-Complex.I) ^ (j : ℕ) * Complex.I * (Real.sin (((j : ℕ) : ℝ) * angle d) : ℂ) := by
    by_cases h : 0 < (j : ℕ)
    · rw [dif_pos h, sineMode_apply, Fin.val_mk]
      obtain ⟨m, hm⟩ : ∃ m, (j : ℕ) = m + 1 := ⟨(j : ℕ) - 1, by omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel]
      have hI : (-Complex.I) ^ m = (-Complex.I) ^ (m + 1) * Complex.I := by
        rw [pow_succ, mul_assoc, neg_mul, Complex.I_mul_I]
        simp
      rw [hI]
      have : (((m : ℝ) + 1) : ℝ) = (((m + 1 : ℕ) : ℝ)) := by push_cast; ring
      rw [this]
    · have h0 : (j : ℕ) = 0 := by omega
      rw [dif_neg h, h0]
      simp
  rw [hR, hL, smul_eq_mul]
  have hsl : Real.sin (((j : ℕ) : ℝ) * angle d) =
      Real.sin ((((j : ℕ) : ℝ) + 1) * angle d) * Real.cos (angle d) -
        Real.cos ((((j : ℕ) : ℝ) + 1) * angle d) * Real.sin (angle d) := by
    rw [show ((j : ℕ) : ℝ) * angle d = (((j : ℕ) : ℝ) + 1) * angle d - angle d by ring,
      Real.sin_sub]
  have hsr : Real.sin ((((j : ℕ) : ℝ) + 2) * angle d) =
      Real.sin ((((j : ℕ) : ℝ) + 1) * angle d) * Real.cos (angle d) +
        Real.cos ((((j : ℕ) : ℝ) + 1) * angle d) * Real.sin (angle d) := by
    rw [show (((j : ℕ) : ℝ) + 2) * angle d = (((j : ℕ) : ℝ) + 1) * angle d + angle d by ring,
      Real.sin_add]
  rw [hsl, hsr, spectralRadius_eq, Real.tan_eq_sin_div_cos]
  push_cast
  have hc : (Real.cos (angle d) : ℂ) ≠ 0 := by exact_mod_cast hcos.ne'
  field_simp
  ring

end PathObservables
