/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import PhyslibAlpha.AlgebraicFramework.HilbertSpace.Dynamics.Hamiltonian

/-!

# A Lieb–Robinson bound for bounded Hamiltonians

Let `H` be a bounded Hamiltonian and suppose that `ψ` cannot reach `φ` in fewer than `r`
applications of `H`, that is `⟪φ, Hⁿ ψ⟫ = 0` for every `n < r`. Then the transition amplitude
of the unitary evolution `U_H(t) = exp(-itH/ℏ)` is bounded by the tail of the exponential series:

    ‖⟪φ, U_H(t) ψ⟫‖ ≤ (|t| ‖H‖ / |ℏ|) ^ r / r! · exp(|t| ‖H‖ / |ℏ|) · ‖φ‖ ‖ψ‖.

For a Hamiltonian that only couples neighbouring sites of a lattice, the hypothesis holds with
`r` the lattice distance, and the bound decays faster than any exponential in `r`: amplitudes
outside the light cone `r ≲ |t| ‖H‖ / |ℏ|` are suppressed.

## Main results

- `norm_inner_exp_le` : the bound for `exp A`, with `‖A‖` in place of `|t| ‖H‖ / |ℏ|`.
- `norm_inner_unitaryEvolution_le` : the Lieb–Robinson bound for `unitaryEvolution ℏ H`.

-/

@[expose] public section

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace UnitaryOneParameterGroup

/-- `x ^ (m + r) / (m + r)! ≤ x ^ r / r! · x ^ m / m!`, from `m! r! ∣ (m + r)!`. -/
private lemma pow_div_factorial_add_le {x : ℝ} (hx : 0 ≤ x) (m r : ℕ) :
    x ^ (m + r) / (m + r).factorial ≤ x ^ r / r.factorial * (x ^ m / m.factorial) := by
  have h : ((m.factorial : ℝ) * r.factorial) ≤ (m + r).factorial := by
    exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos _)
      (m.factorial_mul_factorial_dvd_factorial_add r)
  calc x ^ (m + r) / (m + r).factorial ≤ x ^ (m + r) / (m.factorial * r.factorial) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h
    _ = x ^ r / r.factorial * (x ^ m / m.factorial) := by rw [pow_add]; field_simp

omit [CompleteSpace H] in
private lemma norm_pow_apply_le (A : H →L[ℂ] H) (n : ℕ) (ψ : H) :
    ‖(A ^ n) ψ‖ ≤ ‖A‖ ^ n * ‖ψ‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc ‖(A ^ (n + 1)) ψ‖ = ‖A ((A ^ n) ψ)‖ := by rw [pow_succ']; rfl
      _ ≤ ‖A‖ * (‖A‖ ^ n * ‖ψ‖) := (A.le_opNorm _).trans (by gcongr)
      _ = ‖A‖ ^ (n + 1) * ‖ψ‖ := by ring

/-- If `⟪φ, Aⁿ ψ⟫ = 0` for every `n < r`, then
`‖⟪φ, exp A ψ⟫‖ ≤ ‖A‖ ^ r / r! · exp ‖A‖ · ‖φ‖ ‖ψ‖`. -/
lemma norm_inner_exp_le (A : H →L[ℂ] H) {φ ψ : H} {r : ℕ}
    (hr : ∀ n < r, ⟪φ, (A ^ n) ψ⟫_ℂ = 0) :
    ‖⟪φ, NormedSpace.exp A ψ⟫_ℂ‖ ≤
      ‖A‖ ^ r / r.factorial * Real.exp ‖A‖ * (‖φ‖ * ‖ψ‖) := by
  set f : ℕ → ℂ := fun n => (n.factorial : ℂ)⁻¹ * ⟪φ, (A ^ n) ψ⟫_ℂ
  set b : ℕ → ℝ := fun n => if n < r then 0 else ‖A‖ ^ n / n.factorial * (‖φ‖ * ‖ψ‖)
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℂ) A
  have hexp : ⟪φ, NormedSpace.exp A ψ⟫_ℂ = ∑' n, f n := by
    rw [congrFun (NormedSpace.exp_eq_tsum ℂ) A, ← ContinuousLinearMap.apply_apply ψ,
      (ContinuousLinearMap.apply ℂ H ψ).map_tsum hs, ← innerSL_apply_apply,
      (innerSL ℂ φ).map_tsum ((ContinuousLinearMap.apply ℂ H ψ).summable hs)]
    simp [f]
  have hfb : ∀ n, ‖f n‖ ≤ b n := by
    intro n
    by_cases hn : n < r
    · simp only [f, b, hn, hr n hn, ite_true, mul_zero, norm_zero, le_refl]
    · simp only [f, b, hn, ite_false, norm_mul, norm_inv, Complex.norm_natCast]
      calc (n.factorial : ℝ)⁻¹ * ‖⟪φ, (A ^ n) ψ⟫_ℂ‖
          ≤ (n.factorial : ℝ)⁻¹ * (‖φ‖ * (‖A‖ ^ n * ‖ψ‖)) := by
            gcongr
            exact (norm_inner_le_norm _ _).trans (by gcongr; exact norm_pow_apply_le A n ψ)
        _ = ‖A‖ ^ n / n.factorial * (‖φ‖ * ‖ψ‖) := by ring
  have hb0 : ∀ n, 0 ≤ b n := fun n => by simp only [b]; split_ifs <;> positivity
  have hg := (Real.summable_pow_div_factorial ‖A‖).mul_right (‖φ‖ * ‖ψ‖)
  have hbs : Summable b := hg.of_nonneg_of_le hb0 fun n => by
    simp only [b]; split_ifs <;> [positivity; exact le_rfl]
  have hfs : Summable fun n => ‖f n‖ := hbs.of_nonneg_of_le (fun _ => norm_nonneg _) hfb
  have hhead : ∑ n ∈ Finset.range r, b n = 0 :=
    Finset.sum_eq_zero fun n hn => by simp [b, Finset.mem_range.mp hn]
  calc ‖⟪φ, NormedSpace.exp A ψ⟫_ℂ‖ ≤ ∑' n, ‖f n‖ := hexp ▸ norm_tsum_le_tsum_norm hfs
    _ ≤ ∑' n, b n := hfs.tsum_le_tsum hfb hbs
    _ = ∑' m, b (m + r) := by rw [← hbs.sum_add_tsum_nat_add r, hhead, zero_add]
    _ ≤ ∑' m : ℕ, ‖A‖ ^ r / r.factorial * (‖A‖ ^ m / m.factorial) * (‖φ‖ * ‖ψ‖) := by
        refine ((summable_nat_add_iff r).mpr hbs).tsum_le_tsum (fun m => ?_)
          (((Real.summable_pow_div_factorial ‖A‖).mul_left _).mul_right _)
        simp only [b, show ¬ m + r < r by omega, ite_false]
        gcongr
        exact pow_div_factorial_add_le (norm_nonneg A) m r
    _ = ‖A‖ ^ r / r.factorial * Real.exp ‖A‖ * (‖φ‖ * ‖ψ‖) := by
        rw [tsum_mul_right, tsum_mul_left, Real.exp_eq_exp_ℝ,
          congrFun NormedSpace.exp_eq_tsum_div]

/-- **Lieb–Robinson bound.** If `⟪φ, Hⁿ ψ⟫ = 0` for every `n < r`, then
`‖⟪φ, U_H(t) ψ⟫‖ ≤ (|t| ‖H‖ / |ℏ|) ^ r / r! · exp(|t| ‖H‖ / |ℏ|) · ‖φ‖ ‖ψ‖`. -/
lemma norm_inner_unitaryEvolution_le (ℏ : ℝ) (Hm : Observable (H →L[ℂ] H)) {φ ψ : H} {r : ℕ}
    (hr : ∀ n < r, ⟪φ, ((Hm : H →L[ℂ] H) ^ n) ψ⟫_ℂ = 0) (t : ℝ) :
    ‖⟪φ, (unitaryEvolution ℏ Hm t : H →L[ℂ] H) ψ⟫_ℂ‖ ≤
      (|t| * ‖(Hm : H →L[ℂ] H)‖ / |ℏ|) ^ r / r.factorial *
        Real.exp (|t| * ‖(Hm : H →L[ℂ] H)‖ / |ℏ|) * (‖φ‖ * ‖ψ‖) := by
  set c : ℂ := -(t : ℂ) * Complex.I * ((ℏ⁻¹ : ℝ) : ℂ)
  have hA : (-(t : ℂ) * Complex.I) • ((ℏ⁻¹ : ℝ) • (Hm : H →L[ℂ] H)) = c • (Hm : H →L[ℂ] H) := by
    rw [← Complex.coe_smul, smul_smul]
  have hc : ‖c • (Hm : H →L[ℂ] H)‖ = |t| * ‖(Hm : H →L[ℂ] H)‖ / |ℏ| := by
    rw [norm_smul]; simp [c, div_eq_mul_inv]; ring
  rw [unitaryEvolution_apply, hA, ← hc]
  refine norm_inner_exp_le _ fun n hn => ?_
  rw [smul_pow, smul_apply, inner_smul_right, hr n hn, mul_zero]

end UnitaryOneParameterGroup
